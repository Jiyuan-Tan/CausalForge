#!/usr/bin/env node
import path from "node:path";
import { readSolveUnitOutput } from "./dispatch.js";

const outPath = process.argv[2];
if (!outPath) throw new Error("usage: validate_output.ts <solve-output.json>");

await readSolveUnitOutput(outPath, path.basename(outPath, path.extname(outPath)));
console.log(`PASS ${outPath}`);
