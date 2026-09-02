/**
 * Orchestrator-only: land PROOF-IRRELEVANT core metadata directly, with no solver round.
 *
 * Allowed: `statement-replace` changing only justification/gap/consumer on a non-cited,
 * non-partial node. Everything else (claims, dependencies, declarations, status, source,
 * symbols, bibliography, comparator table, cited leaves) is refused — that is
 * `d0_directive` territory (the solver authors AND re-proves it). Edits go through the
 * SAME apply path as a solver bundle (schema, structural gate, atomic transaction,
 * provenance-only journal entry); no proof is reopened, the stage pointer is not
 * rewound, round outputs are kept, and core.json is re-rendered.
 *
 * Usage:
 *   npx tsx tools/bin/d0_author_edits.ts <qid> <spec> --file <edits.json> --note "<why>" [--check]
 *
 * `edits.json` is a JSON array in the worker `proposed_core_edits` item shape.
 * `--check` validates and previews with no mutation.
 */
import path from "node:path";
import process from "node:process";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { authorMetadataEdits } from "../src/discovery/stages/d0_author_edits.js";

export async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const take = (flag: string): string | undefined => {
    const i = args.indexOf(flag);
    if (i === -1) return undefined;
    const value = args[i + 1];
    if (value === undefined || value.startsWith("--")) {
      throw new Error(`${flag} requires a value`);
    }
    args.splice(i, 2);
    return value;
  };
  const file = take("--file");
  const note = take("--note");
  const checkIdx = args.indexOf("--check");
  const checkOnly = checkIdx !== -1;
  if (checkOnly) args.splice(checkIdx, 1);
  const unknown = args.filter((a) => a.startsWith("--"));
  if (unknown.length > 0) throw new Error(`unrecognized flag(s) ${unknown.join(", ")}; valid: --file <edits.json> --note "..." [--check]`);
  const [qid, spec] = args;
  if (!qid || !spec || !file || !note) {
    throw new Error('usage: d0_author_edits.ts <qid> <spec> --file <edits.json> --note "<why>" [--check]');
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: false };
  const edits = JSON.parse(await readFile(path.resolve(file), "utf8")) as unknown;
  const changed = await authorMetadataEdits({ ctx, edits, note, checkOnly });
  console.log(`${checkOnly ? "Validated" : "Applied"} ${changed.length} orchestrator-authored metadata edit(s)${checkOnly ? " with no mutation" : " + logged escalation"}:`);
  for (const c of changed) console.log(`  - ${c.kind} ${c.id}`);
  if (!checkOnly) console.log("core.json re-rendered; stage pointer and proofs untouched — continue with --resume as before.");
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main().catch((err: unknown) => {
    console.error(`d0_author_edits: ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  });
}
