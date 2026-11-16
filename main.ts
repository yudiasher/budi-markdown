// Driver for the make.fun markdown-render-speed-02 entry.
//
// Reads every case from the input directory (MAKEFUN_INPUT_DIR, or /input
// in the grading container), renders each one alone with parse() from
// parse.js, and writes the HTML strings in order to html.json in the
// output directory (MAKEFUN_OUTPUT_DIR, or /output in the container).

import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const parsed = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
const cases = (Array.isArray(parsed) ? parsed : parsed.cases) as { id: string; markdown: string }[];

const html = new Array<string>(cases.length);
for (let i = 0; i < cases.length; i++) {
  html[i] = parse(cases[i].markdown);
}

mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
