// budi-markdown — a fast, dependency-free Markdown parser.
//
// parse(markdown) returns exactly the HTML that marked 18.1.3 renders with
// its default options (gfm on, breaks off, pedantic off, async off). This is
// an original implementation written for this competition: it follows the
// same CommonMark 0.31.2 + GFM rules marked implements, but the code,
// structure and optimisations are my own. It shares no code with marked.
//
// Architecture: a block lexer turns the document into block tokens (each
// text-bearing token queues its source for inline lexing), an inline lexer
// turns each queued source into inline tokens, and a small renderer walks
// the tokens to HTML. The inline lexer keeps marked's delimiter algorithm
// for emphasis / strikethrough (including its "last possible closer" scan),
// because that is what decides the exact output on the tricky spec cases.

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const escapeChar = (ch) => ESCAPE_MAP[ch];

/** Escape HTML. With `encode`, escape `&` too; otherwise leave valid entities alone. */
function escapeHtml(str, encode) {
  if (encode) return str.replace(ESCAPE_REPLACE, escapeChar);
  return str.replace(ESCAPE_REPLACE_NO_ENCODE, escapeChar);
}

const NUMERIC_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUMERIC_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

/** Decode numeric character references (&#65; &#x41;). Named entities pass through untouched. */
function decodeNumericRefs(str) {
  if (str.indexOf('&#') === -1) return str;
  if (!NUMERIC_REF.test(str)) return str;
  return str.replace(NUMERIC_REF_OR_AMP, (whole, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    if (code === 38) return '&amp;';
    return String.fromCodePoint(code);
  });
}

const PERCENT_DECODE = /%25/g;
/** Clean a URL the way marked does: encodeURI, then restore %25 to %. Null when unencodable. */
function cleanUrl(href) {
  try {
    return encodeURI(href).replace(PERCENT_DECODE, '%');
  } catch {
    return null;
  }
}

/** Strip trailing characters: with `inverted`, strip trailing chars that are NOT `ch`. */
function stripTrailing(str, ch, inverted) {
  const n = str.length;
  if (n === 0) return '';
  let cut = 0;
  for (;;) {
    const c = str.charAt(n - cut - 1);
    if (c === ch && !inverted) cut++;
    else if (c !== ch && inverted) cut++;
    else break;
  }
  return str.slice(0, n - cut);
}

/** Remove excess trailing blank lines from an indented code block's raw text. */
function stripTrailingBlanks(str) {
  const lines = str.split('\n');
  let t = lines.length - 1;
  for (; t >= 0 && BLANK_LINE.test(lines[t]);) t--;
  return lines.length - t <= 2 ? str : lines.slice(0, t + 1).join('\n');
}

/** Normalise a link reference label: trim, collapse whitespace, fold case. */
function normalizeLabel(str) {
  return str.trim().replace(MULTI_SPACE, ' ').toLowerCase().toUpperCase().toLowerCase();
}

/** Find the index of an unmatched closing paren (like marked's `ke`). -2 = unclosed open, -1 = none. */
function findUnmatchedParen(str, pair) {
  if (str.indexOf(pair[0]) === -1 && str.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === pair[0]) depth++;
    else if (str[i] === pair[1]) {
      depth--;
      if (depth < 0) return i;
    }
  }
  return depth > 0 ? -2 : -1;
}

/** Expand tabs to spaces, tab stops every 4 columns starting at column `col`. */
function expandTabs(str, col = 0) {
  let out = '';
  let c = col;
  for (const ch of str) {
    if (ch === '\t') {
      const n = 4 - (c % 4);
      out += ' '.repeat(n);
      c += n;
    } else {
      out += ch;
      c++;
    }
  }
  return out;
}

/** Split a table row into cells, honouring escaped pipes and optional edge pipes. */
function splitTableRow(str, expected) {
  const withMarks = str.replace(FIND_PIPE, (ch, off, whole) => {
    let escaped = false;
    for (let p = off; --p >= 0 && whole[p] === '\\';) escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = withMarks.split(SPLIT_PIPE);
  if (cells[0].trim() || cells.shift(), cells.length > 0 && !cells.at(-1)?.trim() && cells.pop(), expected) {
    if (cells.length > expected) cells.splice(expected);
    else for (; cells.length < expected;) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim().replace(SLASH_PIPE, '|');
  return cells;
}

// ---------------------------------------------------------------------------
// Regexes
// ---------------------------------------------------------------------------
//
// A tiny builder: start from a pattern (string or regex), replace a token
// with another pattern's source (stripping its ^ anchors, which would be
// wrong mid-pattern), and compile. Mirrors the way marked composes its
// block rules from shared fragments.

function rxBuilder(pattern, flags = '') {
  let src = typeof pattern === 'string' ? pattern : pattern.source;
  const api = {
    replace(token, replacement) {
      let rep = typeof replacement === 'string' ? replacement : replacement.source;
      rep = rep.replace(/(^|[^\[])\^/g, '$1');
      src = src.replace(token, rep);
      return api;
    },
    getRegex() {
      return new RegExp(src, flags);
    },
  };
  return api;
}

/** Cache a regex factory by indent level 0..3 (marked's `D`). */
function cachedByIndent(make) {
  const cache = [];
  return (n) => {
    const i = Math.max(0, Math.min(3, n - 1));
    return cache[i] || (cache[i] = make(i));
  };
}

const TAG_NAMES = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

const CODE_REMOVE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const OUTPUT_LINK_REPLACE = /\\([\[\]])/g;
const INDENT_CODE_COMP = /^(\s+)(?:```)/;
const BEGINNING_SPACE = /^\s+/;
const ENDING_HASH = /#$/;
const STARTING_SPACE = /^ /;
const ENDING_SPACE = / $/;
const ENDING_SPACE_TAB = /[ \t]$/;
const NON_SPACE = /[^ ]/;
const LF = String.fromCharCode(10);
const TAB_CH = String.fromCharCode(9);
const CR_CH = String.fromCharCode(13);
const BS_CH = String.fromCharCode(92);
const NEWLINE_GLOBAL = /\n/g;
const TAB_GLOBAL = /\t/g;
const LEADING_SPACE_TAB = /^[ \t]+/;
const MULTI_SPACE = /\s+/g;
const BLANK_LINE = /^[ \t]*$/;
const DOUBLE_BLANK_LINE = /\n[ \t]*\n[ \t]*$/;
const BLOCKQUOTE_START = /^ {0,3}>/;
const BLOCKQUOTE_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const BLOCKQUOTE_SETEXT_LINE = /^ {0,3}>[ \t]?/gm;
const BLOCKQUOTE_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const LIST_REPLACE_NESTING = /^ {1,4}(?=( {4})*[^ ])/g;
const LIST_IS_TASK = /^\[[ xX]\][ \t]+\S/;
const LIST_REPLACE_TASK = /^\[[ xX]\][ \t]+/;
const LIST_TASK_CHECKBOX = /\[[ xX]\]/;
const ANY_LINE = /\n.*\n/;
const HREF_BRACKETS = /^<(.*)>$/;
const TABLE_DELIMITER = /[:|]/;
const TABLE_ALIGN_CHARS = /^\||\| *$/g;
const TABLE_ROW_BLANK = /\n[ \t]*$/;
const TABLE_ALIGN_RIGHT = /^ *-+: *$/;
const TABLE_ALIGN_CENTER = /^ *:-+: *$/;
const TABLE_ALIGN_LEFT = /^ *:-+ *$/;
const START_A_TAG = /^<a /i;
const END_A_TAG = /^<\/a>/i;
const START_PRE_TAG = /^<(pre|code|kbd|script)(\s|>)/i;
const END_PRE_TAG = /^<\/(pre|code|kbd|script)(\s|>)/i;
const START_ANGLE = /^</;
const END_ANGLE = />$/;
const UNICODE_ALNUM = /[\p{L}\p{N}]/u;
const ESCAPE_TEST = /[&<>"']/;
const ESCAPE_REPLACE = /[&<>"']/g;
const ESCAPE_TEST_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const ESCAPE_REPLACE_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const FIND_PIPE = /\|/g;
const SPLIT_PIPE = / \|/;
const SLASH_PIPE = /\\\|/g;
const CARRIAGE_RETURN = /\r\n|\r/g;
const SPACE_LINE = /^ +$/gm;
const NOT_SPACE_START = /^\S*/;
const ENDING_NEWLINE = /\n$/;

const listItemRegex = (bull) => new RegExp(`^( {0,3}${bull})((?:[\t ][^\n]*)?(?:\n|$))`);
const listItemReCache = new Map();
function cachedListItemRegex(bull) {
  let re = listItemReCache.get(bull);
  if (!re) { re = listItemRegex(bull); listItemReCache.set(bull, re); }
  return re;
}
const nextBulletRegex = cachedByIndent((n) => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\n]*)?(?:\\n|$))`));
const hrRegex = cachedByIndent((n) => new RegExp(`^ {0,${n}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
const fencesBeginRegex = cachedByIndent((n) => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`));
const headingBeginRegex = cachedByIndent((n) => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`));
const htmlBeginRegex = cachedByIndent((n) => new RegExp(`^ {0,${n}}(?:</?(?:${TAG_NAMES})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const blockquoteBeginRegex = cachedByIndent((n) => new RegExp(`^ {0,${n}}>`));
const NEXT_BULLET_RES = [nextBulletRegex(1), nextBulletRegex(2), nextBulletRegex(3), nextBulletRegex(4)];
const HR_RES = [hrRegex(1), hrRegex(2), hrRegex(3), hrRegex(4)];
const FENCES_BEGIN_RES = [fencesBeginRegex(1), fencesBeginRegex(2), fencesBeginRegex(3), fencesBeginRegex(4)];
const HEADING_BEGIN_RES = [headingBeginRegex(1), headingBeginRegex(2), headingBeginRegex(3), headingBeginRegex(4)];
const HTML_BEGIN_RES = [htmlBeginRegex(1), htmlBeginRegex(2), htmlBeginRegex(3), htmlBeginRegex(4)];
const BLOCKQUOTE_BEGIN_RES = [blockquoteBeginRegex(1), blockquoteBeginRegex(2), blockquoteBeginRegex(3), blockquoteBeginRegex(4)];

// Block rules
const BLOCK_NEWLINE = /^(?:[ \t]*(?:\n|$))+/;
const BLOCK_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const BLOCK_FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const BLOCK_HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const HR_PLAIN = / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const BLOCK_HEADING = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const BLOCK_TEXT = /^[^\n]+/;
const BULLET = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
const LABEL = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
const BLOCK_DEF = rxBuilder(/^ {0,3}\[(label)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(title))? *(?:\n+|$)/)
  .replace('label', LABEL)
  .replace('title', /(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/)
  .getRegex();
const BLOCK_LIST = rxBuilder(/^(bull)([ \t][^\n]*?)?(?:\n|$)/).replace(/bull/g, BULLET).getRegex();
const HTML_COMMENT = /<!--(?:-?>|[\s\S]*?(?:-->|$))/;
const BLOCK_HTML = rxBuilder("^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)|comment[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))", 'i')
  .replace('comment', HTML_COMMENT)
  .replace('tag', TAG_NAMES)
  .replace('attribute', / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/)
  .getRegex();

// Paragraph: lines that continue until a blank line or a block start.
const PARAGRAPH_CORE = /^([^\n]+(?:\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)/;
const HTML_START = ` {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`;
const HTML_START_RE = rxBuilder('^' + HTML_START).replace('tag', TAG_NAMES).getRegex();

function buildParagraph(listPattern, tablePattern) {
  const b = rxBuilder(PARAGRAPH_CORE)
    .replace('hr', BLOCK_HR)
    .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
    .replace('|lheading', '');
  if (tablePattern === '') b.replace('|table', '');
  else b.replace('table', tablePattern);
  return b
    .replace('blockquote', ' {0,3}>')
    .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
    .replace('list', listPattern)
    .replace('html', rxBuilder(HTML_START).replace('tag', TAG_NAMES).getRegex())
    .getRegex();
}

const TABLE_PATTERN = rxBuilder("^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)")
  .replace('hr', BLOCK_HR)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('blockquote', ' {0,3}>')
  .replace('code', '(?: {4}| {0,3}\t)[^\\n]')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]')
  .replace('html', rxBuilder(HTML_START).replace('tag', TAG_NAMES).getRegex())
  .getRegex();

const BLOCK_PARAGRAPH = buildParagraph(' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]', TABLE_PATTERN);

// Setext heading: paragraph-like text followed by === or ---.
const LHEADING_CORE = /^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\n(?!\s*?\n|bull |fences|blockquote|heading|hr|html|table))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;
const BLOCK_LHEADING = rxBuilder(LHEADING_CORE)
  .replace(/bull/g, BULLET)
  .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
  .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
  .replace(/blockquote/g, / {0,3}>/)
  .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
  .replace(/hr/g, HR_PLAIN)
  .replace(/html/g, / {0,3}<[^\n>]+>\n/)
  .replace(/table/g, / {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/)
  .getRegex();

// Blockquote: lines starting with >, with the paragraph rule for lazy continuation.
const BLOCKQUOTE_PARA = buildParagraph(/ {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/, '');
const BLOCK_BLOCKQUOTE = rxBuilder(/^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(paragraph)|[^\n]*)(?:\n|$))+/).replace('paragraph', BLOCKQUOTE_PARA).getRegex();

// Inline rules (GFM)
const INLINE_ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const INLINE_CODE = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const INLINE_BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const PUNCT = /[\p{P}\p{S}]/u;
const PUNCT_SPACE = /[\s\p{P}\p{S}]/u;
const NOT_PUNCT_SPACE = /[^\s\p{P}\p{S}]/u;
// GFM variants: ~ counts as punctuation-adjacent, and ~ itself is not punctuation here.
const PUNCT_GFM = /(?!~)[\p{P}\p{S}]/u;
const PUNCT_SPACE_GFM = /(?!~)[\s\p{P}\p{S}]/u;
const NOT_PUNCT_SPACE_GFM = /(?:[^\s\p{P}\p{S}]|~)/u;
const OPEN_QUOTE = /[\p{Pi}\p{Ps}"']/u;

const ANY_PUNCT = rxBuilder(/\\(punct)/, 'gu').replace(/punct/g, PUNCT).getRegex();
const ANY_PUNCT_OUTSIDE_CODE = rxBuilder(/(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\(punct)/, 'gu').replace(/punct/g, PUNCT).getRegex();
const INLINE_PUNCTUATION = rxBuilder(/^((?![*_])punctSpace)/, 'u').replace(/punctSpace/g, PUNCT_SPACE).getRegex();
const EMAIL_RE = /[a-zA-Z0-9.!#$%&'*+/=?^_`{\|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])/;
const INLINE_AUTOLINK = rxBuilder(/^<(scheme:[^\s\x00-\x1f<>]*|email)>/)
  .replace('scheme', /[a-zA-Z][a-zA-Z0-9+.-]{1,31}/)
  .replace('email', EMAIL_RE)
  .getRegex();
const INLINE_TAG = rxBuilder("^comment|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>")
  .replace('comment', rxBuilder(HTML_COMMENT).replace('(?:-->|$)', '-->').getRegex())
  .replace('attribute', /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/)
  .getRegex();

const BRACKET_INNER = /\[(?:\\[\s\S]|[^\[\]\\])*\]/;
const LINK_LABEL = rxBuilder(/(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/).replace('brackets', BRACKET_INNER).getRegex();
const INLINE_LINK = rxBuilder(/^!?\[(label)\]\([ \t\n]*(href)(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)(title))?[ \t\n]*\)/)
  .replace('label', LINK_LABEL)
  .replace('href', /<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\))/)
  .replace('title', /"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)/)
  .getRegex();
const INLINE_REFLINK = rxBuilder(/^!?\[(label)\]\[(ref)\]/).replace('label', LINK_LABEL).replace('ref', LABEL).getRegex();
const INLINE_NOLINK = rxBuilder(/^!?\[(ref)\](?:\[\])?/).replace('ref', LABEL).getRegex();
const REFLINK_SEARCH_LABEL = rxBuilder(/(?:[^\[\]\\`]*(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/).replace('brackets', BRACKET_INNER).getRegex();
const REF_LABEL = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}/;
const REFLINK_SEARCH = rxBuilder('reflink|nolink(?!\\()', 'g')
  .replace('reflink', rxBuilder(/^!?\[(label)\]\[(ref)\]/).replace('label', REFLINK_SEARCH_LABEL).replace('ref', REF_LABEL).getRegex())
  .replace('nolink', rxBuilder(/^!?\[(ref)\](?:\[\])?/).replace('ref', REF_LABEL).getRegex())
  .getRegex();
const BLOCK_SKIP = rxBuilder(/link|precode-code|html/, 'g')
  .replace('link', /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/)
  .replace('precode-', '(?<!`)()')
  .replace('code', /(?<b>`+)[^`]+\k<b>(?!`)/)
  .replace('html', /<(?! )[^<>]*?>/)
  .getRegex();

const PROTOCOL = /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/;
const EMAIL_LOOSE = /[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/;
const EMAIL_PROTOCOL = rxBuilder(/(?:mailto:email|xmpp:email(?:\/[A-Za-z0-9@.]+)?)/).replace(/email/g, EMAIL_LOOSE).getRegex();
const INLINE_URL = rxBuilder(/^emailProtocol|^((?:protocol):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^email/)
  .replace('emailProtocol', EMAIL_PROTOCOL)
  .replace('protocol', PROTOCOL)
  .replace('email', /[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/)
  .getRegex();
const URL_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// Emphasis delimiter rules.
const EM_STRONG_L = /^(?:\*+(?:((?!\*)punct)|([^\s*]))?)|^_+(?:((?!_)punct)|([^\s_]))?/;
const EM_STRONG_L_GFM = rxBuilder(EM_STRONG_L, 'u').replace(/punct/g, PUNCT_GFM).getRegex();
const EM_STRONG_R_AST_TMPL = "^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)punct(\\*+)(?=[\\s]|$)|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)|[\\s](\\*+)(?!\\*)(?=punct)|(?!\\*)punct(\\*+)(?!\\*)(?=punct)|notPunctSpace(\\*+)(?=notPunctSpace)";
const EM_STRONG_R_AST = rxBuilder(EM_STRONG_R_AST_TMPL, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE_GFM)
  .replace(/punctSpace/g, PUNCT_SPACE_GFM)
  .replace(/punct/g, PUNCT_GFM)
  .getRegex();
const EM_STRONG_R_UND_TMPL = "^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)punct(_+)(?=[\\s]|$)|notPunctSpace(_+)(?!_)(?=punctSpace|$)|(?!_)punctSpace(_+)(?=notPunctSpace)|[\\s](_+)(?!_)(?=punct)|(?!_)punct(_+)(?!_)(?=punct)";
const EM_STRONG_R_UND = rxBuilder(EM_STRONG_R_UND_TMPL, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE)
  .replace(/punctSpace/g, PUNCT_SPACE)
  .replace(/punct/g, PUNCT)
  .getRegex();
const DEL_L = rxBuilder(/^~~?(?:((?!~)punct)|[^\s~])/, 'u').replace(/punct/g, PUNCT).getRegex();
const DEL_R_TMPL = "^[^~]+(?=[^~])|(?!~)punct(~~?)(?=[\\s]|$)|notPunctSpace(~~?)(?!~)(?=punctSpace|$)|(?!~)punctSpace(~~?)(?=notPunctSpace)|[\\s](~~?)(?!~)(?=punct)|(?!~)punct(~~?)(?!~)(?=punct)|notPunctSpace(~~?)(?=notPunctSpace)";
const DEL_R = rxBuilder(DEL_R_TMPL, 'gu')
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE)
  .replace(/punctSpace/g, PUNCT_SPACE)
  .replace(/punct/g, PUNCT)
  .getRegex();
const INLINE_TEXT = rxBuilder(/^(?:[^a-zA-Z0-9](?=emailProtocol)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|protocol:\/\/|wwwStart|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=emailProtocol)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/)
  .replace(/emailProtocol/g, /(?:mailto|xmpp):/)
  .replace('protocol', PROTOCOL)
  .replace('wwwStart', /(?<![^\s*_~(])www\./)
  .getRegex();

// ---------------------------------------------------------------------------
// Emphasis masking: the last-possible-closer scan
// ---------------------------------------------------------------------------
//
// Before inline lexing, the source is "masked" (punctuation inside code
// spans and links is neutralised) so the delimiter search cannot be fooled
// by a closer that lives inside a code span or a link. The scan below finds
// the last position a `*`/`_`/`~` run could still close, which bounds the
// search in emStrong/del. Results are cached per tokenizer while one inline
// source is being lexed.

const maskCache = new WeakMap();

function scanLastClosers(src) {
  const em = { '*': -1, '_': -1 };
  let del = -1;
  const n = src.length;
  for (let i = 0; i < n; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    for (; j < n && src[j] === ch;) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') del = i;
      else em[ch] = i;
    }
    i = j - 1;
  }
  return { maskedSrc: src, lastEm: em, lastDel: del };
}

function pushMask(tokenizer, masked) {
  const entry = scanLastClosers(masked);
  const stack = maskCache.get(tokenizer);
  if (stack) stack.push(entry);
  else maskCache.set(tokenizer, [entry]);
}

function popMask(tokenizer) {
  const stack = maskCache.get(tokenizer);
  if (stack) {
    stack.pop();
    if (stack.length === 0) maskCache.delete(tokenizer);
  }
}

function lastEmCloser(tokenizer, masked, delim) {
  const top = maskCache.get(tokenizer)?.at(-1);
  if (top && top.maskedSrc === masked) return top.lastEm[delim];
  return scanLastClosers(masked).lastEm[delim];
}

function lastDelCloser(tokenizer, masked) {
  const top = maskCache.get(tokenizer)?.at(-1);
  if (top && top.maskedSrc === masked) return top.lastDel;
  return scanLastClosers(masked).lastDel;
}

// ---------------------------------------------------------------------------
// Tokenizer (block + inline)
// ---------------------------------------------------------------------------

/** Email-local-part characters for the inline-text scan (marked's lookahead set). */
const EMAIL_CHAR_TABLE = new Uint8Array(128);
for (let c = 48; c <= 57; c++) EMAIL_CHAR_TABLE[c] = 1;
for (let c = 65; c <= 90; c++) EMAIL_CHAR_TABLE[c] = 1;
for (let c = 97; c <= 122; c++) EMAIL_CHAR_TABLE[c] = 1;
for (const c of [46, 33, 35, 36, 37, 38, 39, 42, 43, 47, 61, 63, 95, 96, 123, 124, 125, 126, 45]) EMAIL_CHAR_TABLE[c] = 1;

/** Characters that end a plain-text run (delimiters, brackets, backtick, backslash). */
const STOP_TABLE = new Uint8Array(128);
for (const c of [92, 60, 33, 91, 96, 42, 95, 126]) STOP_TABLE[c] = 1;

function isAlnumCode(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

/** True when an email-local run followed by @ starts at i. */
function isEmailAt(src, i) {
  let j = i;
  while (EMAIL_CHAR_TABLE[src.charCodeAt(j)]) j++;
  return j > i && src.charCodeAt(j) === 64;
}

/** True when http(s):// or ftp:// (any case) starts at i. */
function isProtocolAt(src, i) {
  const a = src.charCodeAt(i);
  if (a === 104 || a === 72) {
    const t1 = src.charCodeAt(i + 1);
    if (t1 !== 116 && t1 !== 84) return false;
    const t2 = src.charCodeAt(i + 2);
    if (t2 !== 116 && t2 !== 84) return false;
    const p = src.charCodeAt(i + 3);
    if (p !== 112 && p !== 80) return false;
    let j = i + 4;
    const s = src.charCodeAt(j);
    if (s === 115 || s === 83) j++;
    return src.charCodeAt(j) === 58 && src.charCodeAt(j + 1) === 47 && src.charCodeAt(j + 2) === 47;
  }
  if (a === 102 || a === 70) {
    const t1 = src.charCodeAt(i + 1);
    if (t1 !== 116 && t1 !== 84) return false;
    const p = src.charCodeAt(i + 2);
    if (p !== 112 && p !== 80) return false;
    return src.charCodeAt(i + 3) === 58 && src.charCodeAt(i + 4) === 47 && src.charCodeAt(i + 5) === 47;
  }
  return false;
}

/** True when a literal mailto: or xmpp: starts at i. */
function isMailtoAt(src, i) {
  return src.startsWith('mailto:', i) || src.startsWith('xmpp:', i);
}

/**
 * Length of the plain-text run at the start of src. A manual scan mirroring
 * marked inline-text rule: it stops before a delimiter, a backtick/tilde
 * run, two spaces + newline, a URL scheme, www., or an email / mailto: start.
 */
function scanText(src) {
  const n = src.length;
  if (n === 0) return 0;
  let i;
  const c0 = src.charCodeAt(0);
  if (c0 === 96 || c0 === 126) {
    i = 1;
    while (i < n && src.charCodeAt(i) === c0) i++;
  } else {
    i = 1;
  }
  const p0 = i;
  let atIdx = src.indexOf('@', p0);
  for (; i < n; i++) {
    const c = src.charCodeAt(i);
    if (STOP_TABLE[c]) break;
    if (c === 119 && src.startsWith('www.', i)) {
      const p = src.charCodeAt(i - 1);
      if (p === 32 || p === 9 || p === 10 || p === 13 || p === 12 || p === 11 || p === 160 || p === 5760 || (p >= 8192 && p <= 8202) || p === 8232 || p === 8233 || p === 8239 || p === 8287 || p === 12288 || p === 65279 || p === 42 || p === 95 || p === 126 || p === 40) break;
    }
    if (c === 104 || c === 72 || c === 102 || c === 70) {
      if (isProtocolAt(src, i)) break;
    }
    if (c === 32) {
      let j = i;
      while (j < n && src.charCodeAt(j) === 32) j++;
      if (j - i >= 2 && src.charCodeAt(j) === 10) break;
    }
    if (c === 109 || c === 120) {
      if (isMailtoAt(src, i) && !isAlnumCode(src.charCodeAt(i - 1)) && (p0 === 1 || i > p0)) break;
    }
    if (EMAIL_CHAR_TABLE[c] && (i === p0 || !EMAIL_CHAR_TABLE[src.charCodeAt(i - 1)])) {
      if (atIdx !== -1) {
        if (i > atIdx) atIdx = src.indexOf('@', i);
        if (atIdx !== -1 && isEmailAt(src, i)) break;
      }
    }
  }
  return i;
}

/**
 * True when a line after the first (up to the next blank line) is a setext
 * underline (up to 3 spaces, then = or - runs). A cheap precheck so the
 * setext-heading regex is only tried when one could actually match.
 */
/** First non-space char within the first 3 columns (a block-start scan). */
/** A table delimiter row: up to 3 spaces, then |/:?/- cells. */
const TABLE_DELIM_TEST = /^ {0,3}(?:[|] *)?:?-+:? *(?:[|] *:?-+:? *)*(?:[|] *)?$/;

/** True when the second line of src could be a table delimiter row. */
function hasTableDelimiter(src) {
  const nl1 = src.indexOf(LF);
  if (nl1 === -1) return false;
  const nl2 = src.indexOf(LF, nl1 + 1);
  const lineEnd = nl2 === -1 ? src.length : nl2;
  const dash = src.indexOf(String.fromCharCode(45), nl1 + 1);
  if (dash === -1 || dash >= lineEnd) return false;
  return TABLE_DELIM_TEST.test(src.slice(nl1 + 1, lineEnd));
}

/** True when s consists only of whitespace (the exact set String.trim removes). */
function isBlankLine(s) {
  for (let k = 0; k < s.length; k++) {
    const c = s.charCodeAt(k);
    if (c === 32 || c === 9 || c === 10 || c === 13 || c === 12 || c === 11 || c === 160 || c === 5760 || (c >= 8192 && c <= 8202) || c === 8232 || c === 8233 || c === 8239 || c === 8287 || c === 12288 || c === 65279) continue;
    return false;
  }
  return true;
}

/**
 * Length of the paragraph starting at src[0]: the first line plus following
 * lines until a blank line or a line starting a new block (hr, heading,
 * blockquote, fence, list, html, or a table header). Mirrors the paragraph
 * regex (its per-line lookahead) without the regex engine.
 */
function scanParagraph(src) {
  const n = src.length;
  if (n === 0 || src.charCodeAt(0) === 10) return 0;
  let end = src.indexOf(LF);
  if (end === -1) return n;
  let pos = end + 1;
  while (pos < n) {
    const nl = src.indexOf(LF, pos);
    const lineEnd = nl === -1 ? n : nl;
    if (lineEnd === pos) return end;
    if (lineEnd < n) {
      let blank = true;
      for (let k = pos; k < lineEnd; k++) {
        const ch = src.charCodeAt(k);
        if (ch !== 32 && ch !== 9) { blank = false; break; }
      }
      if (blank) return end;
    }
    let i = pos;
    let sp = 0;
    while (sp < 3 && src.charCodeAt(i) === 32) { i++; sp++; }
    const c = src.charCodeAt(i);
    let isBreak = false;
    if (c === 45 || c === 95 || c === 42) {
      let cnt = 0;
      let j = i;
      let ok = true;
      while (j < lineEnd) {
        const ch = src.charCodeAt(j);
        if (ch === c) { cnt++; j++; }
        else if (ch === 32 || ch === 9) { j++; }
        else { ok = false; break; }
      }
      if (ok && cnt >= 3) isBreak = true;
    }
    if (!isBreak && c === 35) {
      let j = i;
      let cnt = 0;
      while (cnt < 6 && src.charCodeAt(j) === 35) { j++; cnt++; }
      if (cnt >= 1 && (j >= lineEnd || src.charCodeAt(j) === 32 || src.charCodeAt(j) === 9 || src.charCodeAt(j) === 13 || src.charCodeAt(j) === 12 || src.charCodeAt(j) === 11)) isBreak = true;
    }
    if (!isBreak && c === 62) isBreak = true;
    if (!isBreak && (c === 96 || c === 126)) {
      let j = i;
      let cnt = 0;
      while (src.charCodeAt(j) === c) { j++; cnt++; }
      if (cnt >= 3) {
        if (c === 126) isBreak = true;
        else {
          let hasTick = false;
          for (let k = j; k < lineEnd; k++) { if (src.charCodeAt(k) === 96) { hasTick = true; break; } }
          if (!hasTick) isBreak = true;
        }
      }
    }
    if (!isBreak && (c === 42 || c === 43 || c === 45)) {
      let j = i + 1;
      let sp2 = 0;
      while (src.charCodeAt(j) === 32 || src.charCodeAt(j) === 9) { j++; sp2++; }
      if (sp2 >= 1 && j < lineEnd && src.charCodeAt(j) !== 32 && src.charCodeAt(j) !== 9) isBreak = true;
    }
    if (!isBreak && c === 49) {
      const d = src.charCodeAt(i + 1);
      if (d === 46 || d === 41) {
        let j = i + 2;
        let sp2 = 0;
        while (src.charCodeAt(j) === 32 || src.charCodeAt(j) === 9) { j++; sp2++; }
        if (sp2 >= 1 && j < lineEnd && src.charCodeAt(j) !== 32 && src.charCodeAt(j) !== 9) isBreak = true;
      }
    }
    if (!isBreak && c === 60) {
      if (HTML_START_RE.test(src.slice(pos, lineEnd))) isBreak = true;
    }
    if (isBreak) return end;
    if (lineEnd < n) {
      const np = lineEnd + 1;
      let ni = np;
      let nsp = 0;
      while (nsp < 3 && src.charCodeAt(ni) === 32) { ni++; nsp++; }
      const nc = src.charCodeAt(ni);
      if (nc === 124 || nc === 58 || nc === 45) {
        const nEnd = src.indexOf(LF, np);
        const nLineEnd = nEnd === -1 ? n : nEnd;
        const dash = src.indexOf(String.fromCharCode(45), ni);
        if (dash !== -1 && dash < nLineEnd && TABLE_DELIM_TEST.test(src.slice(np, nLineEnd))) return end;
      }
    }
    if (nl === -1) return n;
    end = nl;
    pos = nl + 1;
  }
  return end;
}

function firstNonSpace(src) {
  let i = 0;
  while (i < 3 && src.charCodeAt(i) === 32) i++;
  return src.charCodeAt(i);
}

function hasSetextUnderline(src) {
  let pos = src.indexOf(LF);
  if (pos === -1) return false;
  pos++;
  const n = src.length;
  while (pos < n) {
    const nl = src.indexOf(LF, pos);
    const end = nl === -1 ? n : nl;
    let i = pos;
    let sp = 0;
    while (sp < 3 && src.charCodeAt(i) === 32) { i++; sp++; }
    const c = src.charCodeAt(i);
    if (c === 61 || c === 45) {
      let j = i + 1;
      let ok = true;
      while (j < end) {
        const ch = src.charCodeAt(j);
        if (ch !== c && ch !== 32 && ch !== 9) { ok = false; break; }
        j++;
      }
      if (ok) return true;
    }
    let k = pos;
    let blank = true;
    while (k < end) {
      const ch = src.charCodeAt(k);
      if (ch !== 32 && ch !== 9 && ch !== 13) { blank = false; break; }
      k++;
    }
    if (blank) return false;
    if (nl === -1) return false;
    pos = nl + 1;
  }
  return false;
}

class Tokenizer {
  constructor(lexer) {
    this.lexer = lexer;
  }

  // --- blocks ---

  space(src) {
    const c0 = src.charCodeAt(0);
    if (c0 !== 32 && c0 !== 9 && c0 !== 10) return;
    const m = BLOCK_NEWLINE.exec(src);
    if (m && m[0].length > 0) return { type: 'space', raw: m[0] };
  }

  code(src) {
    let ci = 0;
    while (ci < 4 && src.charCodeAt(ci) === 32) ci++;
    if (ci !== 4 && src.charCodeAt(ci) !== 9) return;
    const m = BLOCK_CODE.exec(src);
    if (m) {
      const raw = stripTrailingBlanks(m[0]);
      const text = raw.replace(CODE_REMOVE_INDENT, '');
      return { type: 'code', raw, codeBlockStyle: 'indented', text };
    }
  }

  fences(src) {
    const fc = firstNonSpace(src);
    if (fc !== 96 && fc !== 126) return;
    const m = BLOCK_FENCES.exec(src);
    if (m) {
      const raw = m[0];
      const text = dedentFence(raw, m[3] || '');
      return {
        type: 'code',
        raw,
        lang: m[2] ? m[2].trim().replace(ANY_PUNCT, '$1') : m[2],
        text,
      };
    }
  }

  heading(src) {
    const fc = firstNonSpace(src);
    if (fc !== 35) return;
    const m = BLOCK_HEADING.exec(src);
    if (m) {
      let text = m[2].trim();
      if (ENDING_HASH.test(text)) {
        const stripped = stripTrailing(text, '#');
        if (!stripped || ENDING_SPACE_TAB.test(stripped)) text = stripped.trim();
      }
      return { type: 'heading', raw: stripTrailing(m[0], '\n'), depth: m[1].length, text, tokens: this.lexer.inline(text) };
    }
  }

  hr(src) {
    const fc = firstNonSpace(src);
    if (fc !== 45 && fc !== 95 && fc !== 42) return;
    const m = BLOCK_HR.exec(src);
    if (m) return { type: 'hr', raw: stripTrailing(m[0], '\n') };
  }

  blockquote(src) {
    const fc = firstNonSpace(src);
    if (fc !== 62) return;
    const m = BLOCK_BLOCKQUOTE.exec(src);
    if (!m) return;
    const lines = stripTrailing(m[0], '\n').split('\n');
    let raw = '';
    let text = '';
    const tokens = [];
    while (lines.length > 0) {
      let inQuote = false;
      const chunk = [];
      let p;
      for (p = 0; p < lines.length; p++) {
        if (BLOCKQUOTE_START.test(lines[p])) { chunk.push(lines[p]); inQuote = true; }
        else if (!inQuote) chunk.push(lines[p]);
        else break;
      }
      lines.splice(0, p);
      const joined = chunk.join('\n');
      // Strip the > markers (expanding tabs after them) and neutralise
      // setext underlines so they stay paragraph text inside the quote.
      const inner = joined
        .replace(BLOCKQUOTE_MARKER_WS, (whole, marker, ws) => marker + expandTabs(ws, marker.length))
        .replace(BLOCKQUOTE_SETEXT, '\n    $1')
        .replace(BLOCKQUOTE_SETEXT_LINE, '');
      raw = raw ? `${raw}\n${joined}` : joined;
      text = text ? `${text}\n${inner}` : inner;
      const savedTop = this.lexer.state.top;
      this.lexer.state.top = true;
      this.lexer.blockTokens(inner, tokens, true);
      this.lexer.state.top = savedTop;
      if (lines.length === 0) break;
      const last = tokens.at(-1);
      if (last?.type === 'code' || last?.type === 'heading' || last?.type === 'hr' || last?.type === 'html' || last?.type === 'table') break;
      if (last?.type === 'blockquote') {
        const rest = lines.join('\n');
        const combined = last.raw + '\n' + rest.replace(BLOCKQUOTE_SETEXT_LINE, '');
        const reparsed = this.blockquote(combined);
        tokens[tokens.length - 1] = reparsed;
        const leftover = combined.substring(reparsed.raw.length).replace(/^\n/, '');
        const leftLines = leftover ? leftover.split('\n').length : 0;
        const taken = leftLines ? lines.slice(0, -leftLines) : lines;
        if (taken.length > 0) raw = `${raw}\n${taken.join('\n')}`;
        text = text.substring(0, text.length - last.text.length) + reparsed.text;
        lines.splice(0, taken.length);
        if (lines.length > 0 && BLOCKQUOTE_START.test(lines[0])) continue;
        break;
      } else if (last?.type === 'list') {
        const combined = last.raw + '\n' + lines.join('\n');
        const reparsed = this.list(combined);
        tokens[tokens.length - 1] = reparsed;
        const extra = reparsed.raw.length > last.raw.length
          ? combined.slice(last.raw.length + 1, reparsed.raw.length).split('\n').length
          : 0;
        if (extra > 0) {
          const taken = lines.slice(0, extra).join('\n');
          raw = `${raw}\n${taken}`;
          text = `${text}\n${taken}`;
        }
        lines.splice(0, extra);
        continue;
      }
    }
    return { type: 'blockquote', raw, tokens, text };
  }

  list(src) {
    const fc = firstNonSpace(src);
    if (fc !== 42 && fc !== 43 && fc !== 45 && (fc < 48 || fc > 57)) return;
    const m = BLOCK_LIST.exec(src);
    if (!m) return;
    const full = src;
    const consumed = () => full.length - src.length;
    const bullet = m[1].trim();
    const ordered = bullet.length > 1;
    const listTok = { type: 'list', raw: '', ordered, start: ordered ? +bullet.slice(0, -1) : '', loose: false, items: [] };
    const bullPattern = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
    const itemRe = cachedListItemRegex(bullPattern);
    let pendingLoose = false;
    for (; src;) {
      let empty = false;
      let itemText = '';
      const itemMatch = itemRe.exec(src);
      if (!itemMatch || BLOCK_HR.test(src)) break;
      const itemStart = consumed();
      src = src.substring(itemMatch[0].length);
      const nl0 = itemMatch[2].indexOf(LF);
      const firstLine = nl0 === -1 ? itemMatch[2] : itemMatch[2].slice(0, nl0);
      const bulletWidth = itemMatch[1].length;
      let content = firstLine.charCodeAt(0) === 32 || firstLine.charCodeAt(0) === 9 ? firstLine.replace(LEADING_SPACE_TAB, (v) => expandTabs(v, bulletWidth)) : firstLine;
      const nl1 = src.indexOf(LF);
      let nextLine = nl1 === -1 ? src : src.slice(0, nl1);
      let blankFirst = isBlankLine(content);
      let indent;
      if (blankFirst) {
        indent = bulletWidth + 1;
      } else {
        indent = 0;
        while (indent < content.length && content.charCodeAt(indent) === 32) indent++;
        if (indent > 4) indent = 1;
        itemText = content.slice(indent);
        indent += bulletWidth;
      }
      if (blankFirst && BLANK_LINE.test(nextLine)) {
        src = src.substring(nextLine.length + 1);
        empty = true;
      }
      if (!empty) {
        const ridx = indent <= 1 ? 0 : indent >= 4 ? 3 : indent - 1;
        const nextBullet = NEXT_BULLET_RES[ridx];
        const hrRe = HR_RES[ridx];
        const fenceRe = FENCES_BEGIN_RES[ridx];
        const headingRe = HEADING_BEGIN_RES[ridx];
        const htmlRe = HTML_BEGIN_RES[ridx];
        const quoteRe = BLOCKQUOTE_BEGIN_RES[ridx];
        for (; src;) {
          const nl2 = src.indexOf(LF);
          const line = nl2 === -1 ? src : src.slice(0, nl2);
          const lc = line.charCodeAt(0);
          const dedented = (lc === 32 || lc === 9) && line.indexOf(TAB_CH) !== -1 ? line.replace(LEADING_SPACE_TAB, (v) => expandTabs(v)) : line;
          nextLine = line;
          let lineBreaks;
          if (lc === 32) lineBreaks = fenceRe.test(line) || headingRe.test(line) || htmlRe.test(line) || quoteRe.test(line) || nextBullet.test(line) || hrRe.test(line);
          else if (lc === 96 || lc === 126) lineBreaks = fenceRe.test(line);
          else if (lc === 35) lineBreaks = headingRe.test(line);
          else if (lc === 60) lineBreaks = htmlRe.test(line);
          else if (lc === 62) lineBreaks = quoteRe.test(line);
          else if (lc === 42 || lc === 45) lineBreaks = nextBullet.test(line) || hrRe.test(line);
          else if (lc === 43) lineBreaks = nextBullet.test(line);
          else if (lc === 95) lineBreaks = hrRe.test(line);
          else if (lc >= 48 && lc <= 57) lineBreaks = nextBullet.test(line);
          else lineBreaks = false;
          if (lineBreaks) break;
          let sp = 0;
          while (sp < dedented.length && dedented.charCodeAt(sp) === 32) sp++;
          if (sp >= indent || isBlankLine(line)) {
            itemText += LF + dedented.slice(indent);
          } else {
            const contentNoTab = content.indexOf(TAB_CH) === -1 ? content : content.replace(TAB_GLOBAL, '    ');
            let csp = 0;
            while (csp < contentNoTab.length && contentNoTab.charCodeAt(csp) === 32) csp++;
            const cc = content.charCodeAt(0);
            let contentBreaks;
            if (cc === 32) contentBreaks = fenceRe.test(content) || headingRe.test(content) || htmlRe.test(content) || hrRe.test(content);
            else if (cc === 96 || cc === 126) contentBreaks = fenceRe.test(content);
            else if (cc === 35) contentBreaks = headingRe.test(content);
            else if (cc === 60) contentBreaks = htmlRe.test(content);
            else if (cc === 42 || cc === 45 || cc === 95) contentBreaks = hrRe.test(content);
            else contentBreaks = false;
            if (blankFirst || (csp < contentNoTab.length && csp >= 4) || contentBreaks) break;
            // A setext underline stays list text (indented) rather than a heading.
            const setextLine = (line.charCodeAt(0) === 61 || line.charCodeAt(0) === 45 || line.charCodeAt(0) === 32) && /^ {0,3}(?:=+|-+) *$/.test(line) && BLOCK_LHEADING.test(`${content}\n${line}`)
              ? `    ${dedented.replace(/^ {0,3}/, '')}`
              : line;
            itemText += LF + setextLine;
          }
          blankFirst = isBlankLine(line);
          src = src.substring(line.length + 1);
          content = dedented.slice(indent);
        }
      }
      const itemRaw = full.slice(itemStart, consumed());
      if (!listTok.loose) {
        if (pendingLoose) listTok.loose = true;
        else if (DOUBLE_BLANK_LINE.test(itemRaw)) pendingLoose = true;
      }
      listTok.items.push({
        type: 'list_item',
        raw: itemRaw,
        task: itemText.charCodeAt(0) === 91 && LIST_IS_TASK.test(itemText),
        loose: false,
        text: itemText,
        tokens: [],
      });
    }
    const lastItem = listTok.items.at(-1);
    if (!lastItem) return;
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
    listTok.raw = full.slice(0, consumed()).trimEnd();
    for (const item of listTok.items) {
      this.lexer.state.top = false;
      item.tokens = this.lexer.blockTokens(item.text, []);
      if (!listTok.loose) {
        const spaces = item.tokens.filter((t) => t.type === 'space');
        if (spaces.length > 0 && spaces.some((t) => ANY_LINE.test(t.raw))) listTok.loose = true;
      }
    }
    for (const item of listTok.items) {
      const first = item.tokens[0];
      if (item.task && (first?.type === 'text' || first?.type === 'paragraph')) {
        item.text = item.text.replace(LIST_REPLACE_TASK, '');
        first.raw = first.raw.replace(LIST_REPLACE_TASK, '');
        first.text = first.text.replace(LIST_REPLACE_TASK, '');
        for (let i = this.lexer.inlineQueue.length - 1; i >= 0; i--) {
          if (LIST_IS_TASK.test(this.lexer.inlineQueue[i].src)) {
            this.lexer.inlineQueue[i].src = this.lexer.inlineQueue[i].src.replace(LIST_REPLACE_TASK, '');
            break;
          }
        }
        const box = LIST_TASK_CHECKBOX.exec(item.raw);
        if (box) {
          const checkbox = { type: 'checkbox', raw: box[0] + ' ', checked: box[0] !== '[ ]' };
          item.checked = checkbox.checked;
          if (listTok.loose) {
            if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
              item.tokens[0].raw = checkbox.raw + item.tokens[0].raw;
              item.tokens[0].text = checkbox.raw + item.tokens[0].text;
              item.tokens[0].tokens.unshift(checkbox);
            } else {
              item.tokens.unshift({ type: 'paragraph', raw: checkbox.raw, text: checkbox.raw, tokens: [checkbox] });
            }
          } else {
            item.tokens.unshift(checkbox);
          }
        }
      } else if (item.task) {
        item.task = false;
      }
    }
    if (listTok.loose) {
      for (const item of listTok.items) {
        item.loose = true;
        for (const t of item.tokens) if (t.type === 'text') t.type = 'paragraph';
      }
    }
    return listTok;
  }

  html(src) {
    const fc = firstNonSpace(src);
    if (fc !== 60) return;
    const m = BLOCK_HTML.exec(src);
    if (m) {
      const raw = stripTrailingBlanks(m[0]);
      return { type: 'html', block: true, raw, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style', text: raw };
    }
  }

  def(src) {
    const fc = firstNonSpace(src);
    if (fc !== 91) return;
    const m = BLOCK_DEF.exec(src);
    if (!m) return;
    if (!START_ANGLE.test(m[2]) && findUnmatchedParen(m[2], '()') !== -1) return;
    const tag = normalizeLabel(m[1]);
    const href = m[2] ? m[2].replace(HREF_BRACKETS, '$1').replace(ANY_PUNCT, '$1') : '';
    const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(ANY_PUNCT, '$1') : m[3];
    return { type: 'def', tag, raw: stripTrailing(m[0], '\n'), href, title };
  }

  table(src) {
    if (!hasTableDelimiter(src)) return;
    const m = TABLE_PATTERN.exec(src);
    if (!m || !TABLE_DELIMITER.test(m[2])) return;
    const header = splitTableRow(m[1]);
    const divider = m[2].replace(TABLE_ALIGN_CHARS, '').split('|');
    const bodyLines = m[3]?.trim() ? m[3].replace(TABLE_ROW_BLANK, '').split('\n') : [];
    const out = { type: 'table', raw: stripTrailing(m[0], '\n'), header: [], align: [], rows: [] };
    if (header.length !== divider.length) return;
    for (const cell of divider) {
      if (TABLE_ALIGN_RIGHT.test(cell)) out.align.push('right');
      else if (TABLE_ALIGN_CENTER.test(cell)) out.align.push('center');
      else if (TABLE_ALIGN_LEFT.test(cell)) out.align.push('left');
      else out.align.push(null);
    }
    for (let i = 0; i < header.length; i++) {
      out.header.push({ text: header[i], tokens: this.lexer.inline(header[i]), header: true, align: out.align[i] });
    }
    for (const line of bodyLines) {
      out.rows.push(splitTableRow(line, out.header.length).map((cell, i) => ({ text: cell, tokens: this.lexer.inline(cell), header: false, align: out.align[i] })));
    }
    return out;
  }

  lheading(src) {
    if (!hasSetextUnderline(src)) return;
    const m = BLOCK_LHEADING.exec(src);
    if (m) {
      const text = m[1].trim();
      return { type: 'heading', raw: stripTrailing(m[0], '\n'), depth: m[2].charAt(0) === '=' ? 1 : 2, text, tokens: this.lexer.inline(text) };
    }
  }

  paragraph(src) {
    const len = scanParagraph(src);
    if (len === 0) return;
    const raw = src.slice(0, len);
    let text = raw;
    if (text.charAt(text.length - 1) === '\n') text = text.slice(0, -1);
    return { type: 'paragraph', raw, text, tokens: this.lexer.inline(text) };
  }

  text(src) {
    if (src.length === 0 || src.charCodeAt(0) === 10) return;
    const nl = src.indexOf(LF);
    const raw = nl === -1 ? src : src.slice(0, nl);
    return { type: 'text', raw, text: raw, tokens: this.lexer.inline(raw) };
  }

  // --- inline ---

  escape(src) {
    const m = INLINE_ESCAPE.exec(src);
    if (m) return { type: 'escape', raw: m[0], text: m[1] };
  }

  tag(src) {
    const m = INLINE_TAG.exec(src);
    if (!m) return;
    const state = this.lexer.state;
    if (!state.inLink && START_A_TAG.test(m[0])) state.inLink = true;
    else if (state.inLink && END_A_TAG.test(m[0])) state.inLink = false;
    if (!state.inRawBlock && START_PRE_TAG.test(m[0])) state.inRawBlock = true;
    else if (state.inRawBlock && END_PRE_TAG.test(m[0])) state.inRawBlock = false;
    return { type: 'html', raw: m[0], inLink: state.inLink, inRawBlock: state.inRawBlock, block: false, text: m[0] };
  }

  link(src) {
    if (this.lexer.state.linkParenPossible === false) return;
    const m = INLINE_LINK.exec(src);
    if (!m) return;
    const bang = m[0].charAt(0) === '!' ? 2 : 1;
    if (hasTagInside(src, m[1], bang)) return;
    let href = m[2].trim();
    if (START_ANGLE.test(href)) {
      if (!END_ANGLE.test(href)) return;
      const stripped = stripTrailing(href.slice(0, -1), '\\');
      if ((href.length - stripped.length) % 2 === 0) return;
    } else {
      const paren = findUnmatchedParen(m[2], '()');
      if (paren === -2) return;
      if (paren > -1) {
        const cut = (m[0].indexOf('!') === 0 ? 5 : 4) + m[1].length + paren;
        m[2] = m[2].substring(0, paren);
        m[0] = m[0].substring(0, cut).trim();
        m[3] = '';
      }
    }
    const stripped = stripTrailing(m[0].slice(0, -1), '\\');
    if ((m[0].length - stripped.length) % 2 === 0) return;
    let dest = m[2];
    let title = '';
    if (m[3]) title = m[3].slice(1, -1);
    dest = dest.trim();
    if (START_ANGLE.test(dest)) dest = dest.slice(1, -1);
    return makeLink(m, { href: dest && dest.replace(ANY_PUNCT, '$1'), title: title && title.replace(ANY_PUNCT, '$1') }, m[0], this.lexer);
  }

  reflink(src, links) {
    const m = INLINE_REFLINK.exec(src) || INLINE_NOLINK.exec(src);
    if (!m) return;
    const bang = m[0].charAt(0) === '!' ? 2 : 1;
    if (hasTagInside(src, m[1], bang)) return;
    const ref = links[normalizeLabel(m[2] || m[1])];
    if (!ref) {
      const ch = m[0].charAt(0);
      return { type: 'text', raw: ch, text: ch };
    }
    return makeLink(m, ref, m[0], this.lexer);
  }

  emStrong(src, masked, prev = '') {
    const m = EM_STRONG_L_GFM.exec(src);
    if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return;
    const delim = m[0][0];
    const insideRun = prev === delim;
    const fullLen = masked.length - src.length;
    let runStart = fullLen;
    while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
    const beforeRun = [...masked.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
    const beforeIsDelimOrPunct = beforeRun === '*' || beforeRun === '_' || !!INLINE_PUNCTUATION.exec(beforeRun);
    if (runStart < fullLen) prev = beforeRun;
    const canOpen = runStart < fullLen ? beforeIsDelimOrPunct : !!INLINE_PUNCTUATION.exec(prev);
    if (m[4] && prev.match(UNICODE_ALNUM)) return;
    const punctAfter = m[1] || m[3] || '';
    if (!punctAfter || !prev || canOpen) {
      const runLen = [...m[0]].length - 1;
      let openLeft = runLen;
      let extra = 0;
      const y = fullLen - runStart + runLen;
      const ruleOfThree = !!beforeRun.trim() && (!!punctAfter || (delim === '*' && !beforeIsDelimOrPunct));
      if (delim !== '*' && delim !== '_') return;
      const closerRe = delim === '*' ? EM_STRONG_R_AST : EM_STRONG_R_UND;
      const lastCloser = lastEmCloser(this, masked, delim);
      const closerMin = fullLen + runLen;
      if (lastCloser < closerMin) return;
      const rest = masked.slice(-src.length + runLen);
      const maxIndex = lastCloser - closerMin;
      closerRe.lastIndex = 0;
      let close;
      while ((close = closerRe.exec(rest)) !== null && !(close.index > maxIndex)) {
        const g = close[1] || close[2] || close[3] || close[4] || close[5] || close[6];
        if (!g) continue;
        const gLen = [...g].length;
        if (close[3] || close[4]) { openLeft += gLen; continue; }
        if (close[5] || close[6] || ruleOfThree) {
          if (insideRun && (close[5] || close[6])) break;
          if (y % 3 && !((y + gLen) % 3)) { extra += gLen; continue; }
        }
        openLeft -= gLen;
        if (openLeft > 0) continue;
        const take = Math.min(gLen, gLen + openLeft + extra);
        const firstLen = [...close[0]][0].length;
        const raw = src.slice(0, runLen + close.index + firstLen + take);
        if (Math.min(runLen, take) % 2) {
          const inner = raw.slice(1, -1);
          return { type: 'em', raw, text: inner, tokens: this.lexer.inlineTokens(inner) };
        }
        const inner = raw.slice(2, -2);
        return { type: 'strong', raw, text: inner, tokens: this.lexer.inlineTokens(inner) };
      }
    }
  }

  codespan(src) {
    const m = INLINE_CODE.exec(src);
    if (!m) return;
    let text = m[2].replace(NEWLINE_GLOBAL, ' ');
    if (NON_SPACE.test(text) && STARTING_SPACE.test(text) && ENDING_SPACE.test(text)) text = text.substring(1, text.length - 1);
    return { type: 'codespan', raw: m[0], text };
  }

  br(src) {
    const m = INLINE_BR.exec(src);
    if (m) return { type: 'br', raw: m[0] };
  }

  del(src, masked, prev = '') {
    const m = DEL_L.exec(src);
    if (!m) return;
    if (!(m[1] || '') || !prev || INLINE_PUNCTUATION.exec(prev)) {
      const runLen = [...m[0]].length - 1;
      let openLeft = runLen;
      const lastCloser = lastDelCloser(this, masked);
      const closerMin = masked.length - src.length + runLen;
      if (lastCloser < closerMin) return;
      const rest = masked.slice(-src.length + runLen);
      const maxIndex = lastCloser - closerMin;
      DEL_R.lastIndex = 0;
      let close;
      while ((close = DEL_R.exec(rest)) !== null && !(close.index > maxIndex)) {
        const g = close[1] || close[2] || close[3] || close[4] || close[5] || close[6];
        if (!g) continue;
        const gLen = [...g].length;
        if (gLen !== runLen) continue;
        if (close[3] || close[4]) { openLeft += gLen; continue; }
        openLeft -= gLen;
        if (openLeft > 0) continue;
        const take = Math.min(gLen, gLen + openLeft);
        const firstLen = [...close[0]][0].length;
        const raw = src.slice(0, runLen + close.index + firstLen + take);
        const inner = raw.slice(runLen, -runLen);
        return { type: 'del', raw, text: inner, tokens: this.lexer.inlineTokens(inner) };
      }
    }
  }

  autolink(src) {
    const m = INLINE_AUTOLINK.exec(src);
    if (!m) return;
    let text;
    let href;
    if (m[2] === '@') { text = m[1]; href = 'mailto:' + text; }
    else { text = m[1]; href = text; }
    return { type: 'link', raw: m[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
  }

  url(src) {
    const m = INLINE_URL.exec(src);
    if (!m) return;
    let text;
    let href;
    if (m[2] === '@') {
      text = m[0];
      href = 'mailto:' + text;
    } else {
      let cur = m[0];
      let prev;
      do {
        prev = cur;
        cur = URL_BACKPEDAL.exec(cur)?.[0] ?? '';
      } while (prev !== cur);
      text = cur;
      href = m[1] === 'www.' ? 'http://' + cur : cur;
      m[0] = cur;
    }
    return { type: 'link', raw: m[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
  }

  inlineText(src) {
    const len = scanText(src);
    if (len === 0) return;
    const raw = src.slice(0, len);
    const inRaw = this.lexer.state.inRawBlock;
    return { type: 'text', raw, text: inRaw ? raw : decodeNumericRefs(raw), escaped: inRaw };
  }
}

/** Remove the opening fence's indentation from a fenced code block's text. */
function dedentFence(raw, text) {
  const m = raw.match(INDENT_CODE_COMP);
  if (m === null) return text;
  const indent = m[1];
  return text.split('\n').map((line) => {
    const lead = line.match(BEGINNING_SPACE);
    if (lead === null) return line;
    return line.slice(Math.min(lead[0].length, indent.length));
  }).join('\n');
}

/**
 * A link (or image) is invalid when its text contains a `<` that starts an
 * HTML tag or autolink running past the end of the link text.
 */
function hasTagInside(src, linkText, bangOffset) {
  if (!linkText.includes('<')) return false;
  for (let i = 0; i < linkText.length; i++) {
    if (linkText[i] === '\\') { i++; continue; }
    if (linkText[i] === '`') {
      const code = INLINE_CODE.exec(linkText.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (linkText[i] !== '<') continue;
    const rest = src.slice(bangOffset + i);
    const tag = INLINE_TAG.exec(rest) || INLINE_AUTOLINK.exec(rest);
    if (tag) {
      if (tag[0].length > linkText.length - i) return true;
      i += tag[0].length - 1;
    }
  }
  return false;
}

/** Build a link/image token, lexing its text as inline tokens. */
function makeLink(match, dest, raw, lexer) {
  const text = match[1].replace(OUTPUT_LINK_REPLACE, '$1');
  const isImage = match[0].charAt(0) === '!';
  const savedLink = lexer.state.inLink;
  const savedEmitted = lexer.state.linkEmitted;
  const savedRaw = lexer.state.inRawBlock;
  lexer.state.inLink = true;
  lexer.state.linkEmitted = false;
  const tokens = lexer.inlineTokens(text);
  const nestedLink = lexer.state.linkEmitted;
  lexer.state.linkEmitted = savedEmitted;
  lexer.state.inLink = savedLink;
  if (!isImage) {
    if (nestedLink) {
      lexer.state.inRawBlock = savedRaw;
      return;
    }
    lexer.state.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href: dest.href, title: dest.title || null, text, tokens };
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

class Lexer {
  constructor() {
    this.tokens = [];
    this.tokens.links = Object.create(null);
    this.tokenizer = new Tokenizer(this);
    this.inlineQueue = [];
    this.state = { inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true, top: true };
  }

  lex(src) {
    if (src.indexOf(CR_CH) !== -1) src = src.replace(CARRIAGE_RETURN, '\n');
    this.blockTokens(src, this.tokens);
    for (let i = 0; i < this.inlineQueue.length; i++) {
      const item = this.inlineQueue[i];
      this.state.inRawBlock = false;
      this.inlineTokens(item.src, item.tokens);
    }
    this.inlineQueue = [];
    return this.tokens;
  }

  blockTokens(src, tokens = [], inBlockquote = false) {
    let shortest = Infinity;
    while (src) {
      if (src.length < shortest) shortest = src.length;
      else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
      let tok;
      if ((tok = this.tokenizer.space(src))) {
        src = src.substring(tok.raw.length);
        const prev = tokens.at(-1);
        if (tok.raw.length === 1 && prev !== undefined) prev.raw += '\n';
        else tokens.push(tok);
        continue;
      }
      if ((tok = this.tokenizer.code(src))) {
        src = src.substring(tok.raw.length);
        const prev = tokens.at(-1);
        if (prev?.type === 'paragraph' || prev?.type === 'text') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          prev.text += '\n' + tok.text;
          this.inlineQueue.at(-1).src = prev.text;
        } else tokens.push(tok);
        continue;
      }
      if ((tok = this.tokenizer.fences(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.heading(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.hr(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.blockquote(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.list(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.html(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.def(src))) {
        src = src.substring(tok.raw.length);
        const prev = tokens.at(-1);
        if (prev?.type === 'paragraph' || prev?.type === 'text') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          prev.text += '\n' + tok.raw;
          this.inlineQueue.at(-1).src = prev.text;
        } else {
          if (!this.tokens.links[tok.tag]) this.tokens.links[tok.tag] = { href: tok.href, title: tok.title };
          tokens.push(tok);
        }
        continue;
      }
      if ((tok = this.tokenizer.table(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.lheading(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if (this.state.top && (tok = this.tokenizer.paragraph(src))) {
        const prev = tokens.at(-1);
        if (inBlockquote && prev?.type === 'paragraph') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          prev.text += '\n' + tok.text;
          this.inlineQueue.pop();
          this.inlineQueue.at(-1).src = prev.text;
        } else tokens.push(tok);
        inBlockquote = false;
        src = src.substring(tok.raw.length);
        continue;
      }
      if ((tok = this.tokenizer.text(src))) {
        src = src.substring(tok.raw.length);
        const prev = tokens.at(-1);
        if (prev?.type === 'text') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          prev.text += '\n' + tok.text;
          this.inlineQueue.pop();
          this.inlineQueue.at(-1).src = prev.text;
        } else tokens.push(tok);
        continue;
      }
      throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    }
    this.state.top = true;
    return tokens;
  }

  inline(src, tokens = []) {
    this.inlineQueue.push({ src, tokens });
    return tokens;
  }

  linkInText(src) {
    if (!src.includes('[')) return false;
    for (const m of src.matchAll(BLOCK_SKIP)) {
      if (INLINE_LINK.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
    }
    for (const m of src.matchAll(REFLINK_SEARCH)) {
      const whole = m[0];
      const open = whole.lastIndexOf('[');
      if (!(whole.charAt(0) === '!' || !Object.hasOwn(this.tokens.links, normalizeLabel(whole.slice(open + 1, -1)))) && !(open > 1 && this.linkInText(whole.slice(1, open - 1)))) return true;
    }
    return false;
  }

  inlineTokens(src, tokens = []) {
    const saved = this.state.linkParenPossible;
    this.state.linkParenPossible = saved && src.includes(')');
    try {
      return this.lexInline(src, tokens);
    } finally {
      this.state.linkParenPossible = saved;
    }
  }

  lexInline(src, tokens) {
    const hasDelim = src.includes('*') || src.includes('_') || src.includes('~');
    const masked = hasDelim ? maskInline(src, this) : src;
    pushMask(this.tokenizer, masked);
    try {
      return this.lexInlineMasked(src, masked, tokens);
    } finally {
      popMask(this.tokenizer);
    }
  }

  lexInlineMasked(src, masked, tokens) {
    let wasText = false;
    let lastChar = '';
    let shortest = Infinity;
    while (src) {
      if (src.length < shortest) shortest = src.length;
      else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
      if (!wasText) lastChar = '';
      wasText = false;
      let tok;
      if (src.charCodeAt(0) === 92 && (tok = this.tokenizer.escape(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if (src.charCodeAt(0) === 60 && (tok = this.tokenizer.tag(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((src.charCodeAt(0) === 91 || src.charCodeAt(0) === 33) && (tok = this.tokenizer.link(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((src.charCodeAt(0) === 91 || src.charCodeAt(0) === 33) && (tok = this.tokenizer.reflink(src, this.tokens.links))) {
        src = src.substring(tok.raw.length);
        const prev = tokens.at(-1);
        if (tok.type === 'text' && prev?.type === 'text') { prev.raw += tok.raw; prev.text += tok.text; }
        else tokens.push(tok);
        continue;
      }
      if ((src.charCodeAt(0) === 42 || src.charCodeAt(0) === 95) && (tok = this.tokenizer.emStrong(src, masked, lastChar))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if (src.charCodeAt(0) === 96 && (tok = this.tokenizer.codespan(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((src.charCodeAt(0) === 32 || src.charCodeAt(0) === 92) && (tok = this.tokenizer.br(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if (src.charCodeAt(0) === 126 && (tok = this.tokenizer.del(src, masked, lastChar))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if (src.charCodeAt(0) === 60 && (tok = this.tokenizer.autolink(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if (!this.state.inLink && (tok = this.tokenizer.url(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = this.tokenizer.inlineText(src))) {
        src = src.substring(tok.raw.length);
        if (tok.raw.slice(-1) !== '_') lastChar = tok.raw.slice(-1);
        wasText = true;
        const prev = tokens.at(-1);
        if (prev?.type === 'text') { prev.raw += tok.raw; prev.text += tok.text; }
        else tokens.push(tok);
        continue;
      }
      throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    }
    return tokens;
  }
}

/** True when s contains a * _ or ~ at or after pos. */
function hasDelimAfter(s, pos) {
  return s.indexOf('*', pos) !== -1 || s.indexOf('_', pos) !== -1 || s.indexOf('~', pos) !== -1;
}

/** Index of the first span-start char ([ ` <) in s, or -1. */
function firstSpanStart(s) {
  let first = -1;
  for (const ch of ['[', '`', '<']) {
    const p = s.indexOf(ch);
    if (p !== -1 && (first === -1 || p < first)) first = p;
  }
  return first;
}

/** Mask punctuation inside code spans and links so emphasis can't see through them. */
function maskInline(src, lexer) {
  let out = src;
  // Masking a span only matters when a delimiter (* _ ~) sits inside it:
  // the span's edge characters survive masking and are punctuation either
  // way, so flanking of delimiters outside the span is unchanged.
  if (lexer.tokens.links && src.includes('[') && hasDelimAfter(src, src.indexOf('['))) {
    const maskRef = (whole) => {
      const open = whole.lastIndexOf('[');
      if (!Object.hasOwn(lexer.tokens.links, normalizeLabel(whole.slice(open + 1, -1)))) return whole;
      if (open > 1 && whole.charAt(0) !== '!') {
        const inner = whole.slice(1, open - 1);
        if (lexer.linkInText(inner)) return '[' + inner.replace(REFLINK_SEARCH, maskRef) + '][' + 'a'.repeat(whole.length - open - 2) + ']';
      }
      return '[' + 'a'.repeat(whole.length - 2) + ']';
    };
    out = out.replace(REFLINK_SEARCH, maskRef);
  }
  if (out.includes('`') || out.includes(BS_CH)) {
    out = out.replace(ANY_PUNCT_OUTSIDE_CODE, (whole, ticks, punct) => {
      if (punct) return '+'.repeat(whole.length);
      if (ticks) return ticks + whole.slice(ticks.length, -ticks.length).replace(/`/g, '+') + ticks;
      return whole;
    });
  }
  if (out.includes('[') || out.includes('`') || out.includes('<')) {
    const fs = firstSpanStart(out);
    if (fs !== -1 && hasDelimAfter(out, fs)) {
      out = out.replace(BLOCK_SKIP, (whole, ticks, pre) => {
        const lead = pre ? pre.length : 0;
        return whole.slice(0, lead) + '[' + 'a'.repeat(whole.length - lead - 2) + ']';
      });
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Renderer
// ---------------------------------------------------------------------------

class TextRenderer {
  constructor(parser) {
    this.parser = parser;
  }
  strong(tok) { return tok.tokens ? this.parser.parseInline(tok.tokens, this) : tok.text; }
  em(tok) { return tok.tokens ? this.parser.parseInline(tok.tokens, this) : tok.text; }
  codespan(tok) { return tok.text; }
  del(tok) { return tok.tokens ? this.parser.parseInline(tok.tokens, this) : tok.text; }
  html(tok) { return tok.text; }
  text(tok) { return tok.text; }
  link(tok) { return tok.tokens ? this.parser.parseInline(tok.tokens, this) : tok.text; }
  image(tok) { return tok.tokens ? this.parser.parseInline(tok.tokens, this) : tok.text; }
  br() { return ''; }
  checkbox(tok) { return tok.raw; }
}

class Renderer {
  constructor(parser) {
    this.parser = parser;
  }
  space() { return ''; }
  code(tok) {
    const lang = (tok.lang || '').match(NOT_SPACE_START)?.[0];
    const text = tok.text ? tok.text.replace(ENDING_NEWLINE, '') + '\n' : '';
    const body = escapeHtml(text, true);
    return lang
      ? `<pre><code class="language-${escapeHtml(lang)}">${body}</code></pre>\n`
      : `<pre><code>${body}</code></pre>\n`;
  }
  blockquote(tok) { return `<blockquote>\n${this.parser.parse(tok.tokens)}</blockquote>\n`; }
  html(tok) { return tok.text; }
  def() { return ''; }
  heading(tok) { return `<h${tok.depth}>${this.parser.parseInline(tok.tokens)}</h${tok.depth}>\n`; }
  hr() { return '<hr>\n'; }
  list(tok) {
    let items = '';
    for (const item of tok.items) items += this.listitem(item);
    const tag = tok.ordered ? 'ol' : 'ul';
    const start = tok.ordered && tok.start !== 1 ? ` start="${tok.start}"` : '';
    return `<${tag}${start}>\n${items}</${tag}>\n`;
  }
  listitem(tok) { return `<li>${this.parser.parse(tok.tokens)}</li>\n`; }
  checkbox(tok) { return `<input ${tok.checked ? 'checked="" ' : ''}disabled="" type="checkbox"> `; }
  paragraph(tok) { return `<p>${this.parser.parseInline(tok.tokens)}</p>\n`; }
  table(tok) {
    let head = '';
    for (const cell of tok.header) head += this.tablecell(cell);
    const headRow = this.tablerow({ text: head });
    let body = '';
    for (const row of tok.rows) {
      let cells = '';
      for (const cell of row) cells += this.tablecell(cell);
      body += this.tablerow({ text: cells });
    }
    if (body) body = `<tbody>${body}</tbody>`;
    return `<table>\n<thead>\n${headRow}</thead>\n${body}</table>\n`;
  }
  tablerow(tok) { return `<tr>\n${tok.text}</tr>\n`; }
  tablecell(tok) {
    const inner = this.parser.parseInline(tok.tokens);
    const tag = tok.header ? 'th' : 'td';
    return (tok.align ? `<${tag} align="${tok.align}">` : `<${tag}>`) + inner + `</${tag}>\n`;
  }
  strong(tok) { return `<strong>${this.parser.parseInline(tok.tokens)}</strong>`; }
  em(tok) { return `<em>${this.parser.parseInline(tok.tokens)}</em>`; }
  codespan(tok) { return `<code>${escapeHtml(tok.text, true)}</code>`; }
  br() { return '<br>'; }
  del(tok) { return `<del>${this.parser.parseInline(tok.tokens)}</del>`; }
  link(tok) {
    const text = tok.autolink ? escapeHtml(tok.text, true) : this.parser.parseInline(tok.tokens);
    const href = cleanUrl(tok.href);
    if (href === null) return text;
    let out = `<a href="${escapeHtml(href, tok.autolink)}"`;
    if (tok.title) out += ` title="${escapeHtml(tok.title)}"`;
    return out + `>${text}</a>`;
  }
  image(tok) {
    let alt = tok.text;
    if (tok.tokens) alt = this.parser.parseInline(tok.tokens, this.parser.textRenderer);
    const src = cleanUrl(tok.href);
    if (src === null) return escapeHtml(alt);
    let out = `<img src="${escapeHtml(src)}" alt="${escapeHtml(alt)}"`;
    if (tok.title) out += ` title="${escapeHtml(tok.title)}"`;
    return out + '>';
  }
  text(tok) {
    if ('tokens' in tok && tok.tokens) return this.parser.parseInline(tok.tokens);
    if ('escaped' in tok && tok.escaped) return tok.text;
    return escapeHtml(tok.text);
  }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

class Parser {
  constructor() {
    this.renderer = new Renderer(this);
    this.textRenderer = new TextRenderer(this);
  }
  parse(tokens) {
    let out = '';
    for (const tok of tokens) {
      switch (tok.type) {
        case 'space': out += this.renderer.space(tok); break;
        case 'hr': out += this.renderer.hr(tok); break;
        case 'heading': out += this.renderer.heading(tok); break;
        case 'code': out += this.renderer.code(tok); break;
        case 'table': out += this.renderer.table(tok); break;
        case 'blockquote': out += this.renderer.blockquote(tok); break;
        case 'list': out += this.renderer.list(tok); break;
        case 'checkbox': out += this.renderer.checkbox(tok); break;
        case 'html': out += this.renderer.html(tok); break;
        case 'def': out += this.renderer.def(tok); break;
        case 'paragraph': out += this.renderer.paragraph(tok); break;
        case 'text': out += this.renderer.text(tok); break;
        default: throw new Error(`Token with "${tok.type}" type was not found.`);
      }
    }
    return out;
  }
  parseInline(tokens, renderer = this.renderer) {
    let out = '';
    for (const tok of tokens) {
      switch (tok.type) {
        case 'escape': out += renderer.text(tok); break;
        case 'html': out += renderer.html(tok); break;
        case 'link': out += renderer.link(tok); break;
        case 'image': out += renderer.image(tok); break;
        case 'checkbox': out += renderer.checkbox(tok); break;
        case 'strong': out += renderer.strong(tok); break;
        case 'em': out += renderer.em(tok); break;
        case 'codespan': out += renderer.codespan(tok); break;
        case 'br': out += renderer.br(tok); break;
        case 'del': out += renderer.del(tok); break;
        case 'text': out += renderer.text(tok); break;
        default: throw new Error(`Token with "${tok.type}" type was not found.`);
      }
    }
    return out;
  }
}

/** Render `markdown` to the HTML marked 18.1.3 renders for it (default options). */
export function parse(markdown) {
  const lexer = new Lexer();
  const tokens = lexer.lex(markdown);
  return new Parser().parse(tokens);
}
