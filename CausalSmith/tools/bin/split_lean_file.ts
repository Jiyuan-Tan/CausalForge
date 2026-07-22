#!/usr/bin/env tsx
// CLI for the reactive Lean-file splitter (Mechanism 3).
//
//   tsx bin/split_lean_file.ts <path/to/File.lean> [--budget 700] [--apply]
//
// Dry-run by default: prints the split plan (parts, line counts, de-privatized
// decls).  With --apply: backs up the original to <File>.lean.presplit.bak,
// writes the Part files next to it, and overwrites the original with the thin
// re-export aggregator.  Always `lake build` afterwards and restore the .bak on
// failure (verify-or-rollback).

import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, join, basename } from 'node:path';
import { splitFlatNamespaceFile } from '../src/formalization/splitLeanFile.js';

function moduleNameFromPath(p: string): string {
  const segs = p.replace(/\\/g, '/').split('/').filter(Boolean);
  let last = -1;
  for (let i = 0; i < segs.length; i++) if (segs[i] === 'CausalSmith' || segs[i] === 'Causalean') last = i;
  if (last < 0) throw new Error(`cannot locate package root (CausalSmith/Causalean) in path: ${p}`);
  // path is …/<pkg>/<lib>/… where <pkg>===<lib> name; module starts at the lib dir = `last`
  const modSegs = segs.slice(last);
  modSegs[modSegs.length - 1] = modSegs[modSegs.length - 1].replace(/\.lean$/, '');
  return modSegs.join('.');
}

function main() {
  const args = process.argv.slice(2);
  const target = args.find(a => !a.startsWith('--'));
  if (!target) { console.error('usage: split_lean_file.ts <File.lean> [--budget N] [--apply]'); process.exit(2); }
  const apply = args.includes('--apply');
  const budgetArg = args.find(a => a.startsWith('--budget'));
  const lineBudget = budgetArg ? parseInt(budgetArg.split(/[=\s]/)[1] ?? args[args.indexOf(budgetArg) + 1], 10) : 700;
  // `--pin <declName>` (repeatable): PINNED-SUFFIX mode — keep these decls in the
  // original file, extract only the prefix before the first of them.
  const pinnedDecls = new Set<string>();
  for (let i = 0; i < args.length; i++) if (args[i] === '--pin' && args[i + 1]) pinnedDecls.add(args[i + 1]);

  const abs = target.replace(/\\/g, '/');
  if (!existsSync(abs)) { console.error(`no such file: ${abs}`); process.exit(2); }
  const text = readFileSync(abs, 'utf8');
  const fullModule = moduleNameFromPath(abs);
  const baseName = basename(abs).replace(/\.lean$/, '');
  const modulePrefix = fullModule.slice(0, fullModule.length - baseName.length - 1);

  const res = splitFlatNamespaceFile(text, { lineBudget, modulePrefix, baseName, pinnedDecls });
  if (!res.ok) { console.error(`REFUSED: ${res.reason}`); process.exit(1); }

  const totalIn = text.split('\n').length;
  console.log(`split ${baseName}.lean (${totalIn} lines, ${res.declCount} decls) -> ${res.parts.length} parts (budget ${lineBudget})`);
  for (const p of res.parts) console.log(`  ${p.relFileName.padEnd(22)} ${String(p.lineCount).padStart(5)} lines  module ${p.moduleName}`);
  console.log(
    pinnedDecls.size > 0
      ? `  ${baseName}.lean retains pinned decl(s) [${[...pinnedDecls].join(', ')}] + imports ${res.parts.length} parts`
      : `  aggregator (${baseName}.lean) re-exports ${res.parts.length} parts`,
  );
  if (res.deprivatized.length)
    console.log(`  de-privatized (cross-part refs): ${[...new Set(res.deprivatized)].join(', ')}`);

  if (!apply) { console.log('\n(dry-run — pass --apply to write files)'); return; }

  const dir = dirname(abs);
  // A destination part may already exist and hold work this run did not produce — a previous
  // split whose parts were since edited or proved. The `.presplit.bak` covers ONLY the original
  // file, so overwriting a part here is unrecoverable. Refuse instead, and say what to do.
  const collisions = res.parts
    .map((p) => join(dir, p.relFileName))
    .filter((p) => existsSync(p));
  if (collisions.length > 0) {
    console.error(
      `\nREFUSING to apply: ${collisions.length} destination part file(s) already exist and would be ` +
        `overwritten with no backup (the .presplit.bak covers only ${basename(abs)}):\n` +
        collisions.map((c) => `  ${basename(c)}`).join('\n') +
        `\n\nThis is what a re-split of an already-split file looks like. Move or delete those parts ` +
        `if they are stale, or restore ${basename(abs)} from its .presplit.bak first.`,
    );
    process.exitCode = 1;
    return;
  }

  const bak = `${abs}.presplit.bak`;
  if (!existsSync(bak)) writeFileSync(bak, text, 'utf8');
  for (const p of res.parts) writeFileSync(join(dir, p.relFileName), p.content, 'utf8');
  writeFileSync(abs, res.aggregator, 'utf8');
  console.log(`\nAPPLIED. backup at ${basename(bak)}. lake build to verify; restore .bak on failure.`);
}

main();
