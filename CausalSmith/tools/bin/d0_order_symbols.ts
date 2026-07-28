#!/usr/bin/env -S npx tsx
/** Guarded mechanical migration for a durable G1 use-before-definition ordering defect.
 * Reorders only `proto_core.symbols`; every symbol object must remain byte-identical. */
import { readFile } from "node:fs/promises";
import process from "node:process";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import { CoreSchema } from "../src/discovery/core/schema.js";
import { topologicallyOrderSymbols } from "../src/discovery/core/symbol_order.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";
import { appendEscalationLog, loadWorkingState } from "../src/discovery/stages/d0_working.js";
import { statePath } from "../src/paths.js";
import { STAGE_ORDER } from "../src/constants.js";
import { existsSync } from "node:fs";
import { loadState, saveState } from "../src/state.js";
import type { PipelineContext } from "../src/types.js";

async function main(): Promise<void> {
  const [qid, spec] = process.argv.slice(2);
  if (!qid || !spec) throw new Error("Usage: d0_order_symbols.ts <qid> <spec>");
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  const protoPath = protoCoreJsonPath(ctx);
  const proto = CoreSchema.parse(JSON.parse(await readFile(protoPath, "utf8")));
  const before = proto.symbols;
  const after = topologicallyOrderSymbols(before);
  const signature = (symbols: typeof before): string[] => symbols.map((symbol) => JSON.stringify(symbol)).sort();
  if (JSON.stringify(signature(before)) !== JSON.stringify(signature(after))) {
    throw new Error("symbol-order migration changed symbol payload bytes; refusing write");
  }
  const moved = after.filter((symbol, i) => symbol !== before[i]).map((symbol) => symbol.name);
  if (moved.length === 0) throw new Error("symbol-order migration found no ordering change");
  proto.symbols = after;
  CoreSchema.parse(proto);
  await writeJsonAtomic(protoPath, proto);

  const sp = statePath(repoRoot, qid, spec);
  if (existsSync(sp)) {
    const state = await loadState(repoRoot, qid, spec);
    // REWIND ONLY. Setting the cursor unconditionally moves it FORWARD for a run that has
    // not yet reached D-0.5 — and this tool's precondition (a symbol-ordering defect in
    // proto_core.json) is satisfiable the moment D-1.2 authors the proto. That would mark
    // the D-0.5 proposal review as completed without it ever running, and the next resume
    // would go straight to D0 past the gate.
    const current = STAGE_ORDER.indexOf(state.stage_completed);
    const target = STAGE_ORDER.indexOf("-0.5");
    if (current > target) {
      state.stage_completed = "-0.5";
      await saveState(repoRoot, qid, spec, state);
    }
  }
  const working = await loadWorkingState(ctx);
  await appendEscalationLog(ctx, {
    round: working?.round ?? 0,
    changed: [],
    note: `MECHANICAL SYMBOL TOPOLOGICAL ORDER: moved ${moved.length} positions; every symbol payload preserved byte-for-byte.`,
  });
  console.log(JSON.stringify({ proto: protoPath, moved }, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_order_symbols: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
