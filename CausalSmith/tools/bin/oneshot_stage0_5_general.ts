#!/usr/bin/env node
/**
 * One-shot D0.5.G — run ONLY the cold general referee against the existing
 * stitched .tex, skipping the rubric reviewer (D0.5.1/D0.5.2). This is the
 * cheap debug path: the rubric re-run on an unchanged note is the wasteful part
 * of a `--resume` into D0.5, and for inspecting the cold-referee verdict (tier /
 * salvageable / improvement_directive) or iterating on
 * `stage0_5_general_review.txt`, only D0.5.G matters.
 *
 * One codex call (~3–5 min), no Lean, no D0 re-derive. Does NOT mutate state.json
 * (it never increments `general_reroute_count` nor writes a boundary verdict). It
 * DOES print the exact routing the live boundary WOULD take given the current
 * `flags.general_reroute_count`, so you can see reroute-vs-halt without paying for
 * the rubric reviewer or the D0 re-derivation.
 *
 * Usage:
 *   npx tsx bin/oneshot_stage0_5_general.ts <qid> <specialization> [novelty_target]
 *   (novelty_target defaults to "field"; one of
 *    incremental | subfield | field | flagship — legacy relative-to-repo / relative-to-literature accepted)
 *
 * Note: runGeneralReview persists its verdict to `reviews/review_general.json`
 * as a side effect (the attempt index is recorded inside the record, not the
 * filename); this harness passes a high debug attempt index (99). Run it against a
 * throwaway dir — it overwrites the real run's `review_general.json`.
 */
import { existsSync, readFileSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { defaultDeps } from "../src/pipeline_support.js";
import { meetsNoveltyFloor } from "../src/pipeline_stages.js";
import {
  buildGeneralTierVerdict,
  runGeneralReview,
} from "../src/discovery/stages/d0_5_general.js";
import { loadState } from "../src/state.js";
import type { PipelineContext } from "../src/types.js";
import { NOVELTY_TARGETS, normalizeNoveltyTarget } from "../src/novelty.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

const DEBUG_ATTEMPT = 99;
// Mirror stage0_5.ts: env-overridable directed-reroute cap (default 2).
const REROUTE_CAP = (() => {
  const n = Number.parseInt(process.env.CAUSALSMITH_GENERAL_REROUTE_CAP ?? "", 10);
  return Number.isFinite(n) ? Math.min(6, Math.max(1, n)) : 2;
})();


async function main() {
  const rawArgs = process.argv.slice(2);
  const noteIdx = rawArgs.indexOf("--note");
  const notePath = noteIdx >= 0 ? rawArgs[noteIdx + 1] : undefined;
  const positional = rawArgs.filter((a, i) => i !== noteIdx && i !== noteIdx + 1 && !a.startsWith("--"));
  const [qid, spec, targetArg] = positional;
  if (!qid || !spec) {
    console.error(
      "Usage: oneshot_stage0_5_general.ts <qid> <specialization> [novelty_target] [--note <path>]",
    );
    process.exit(1);
  }
  const noteText = notePath ? await readFile(notePath, "utf8") : undefined;
  const target = normalizeNoveltyTarget(targetArg ?? "field");
  if (!target) {
    console.error(`bad novelty_target '${targetArg}'. one of: ${NOVELTY_TARGETS.join(", ")}`);
    process.exit(1);
  }

  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const ctx: PipelineContext = {
    repoRoot,
    qid,
    specialization: spec,
    dryRun: false,
    resume: true,
    noveltyTarget: target,
  };
  const deps = defaultDeps(ctx);

  console.error(`[oneshot D0.5.G] ${qid} ${spec} · novelty_target=${target}${notePath ? ` · note=${notePath}` : ""} · dispatching cold referee…`);
  const gen = await runGeneralReview({ ctx, state, deps, attempt: DEBUG_ATTEMPT, noteText });

  // Replicate the live boundary's routing WITHOUT mutating state (read-only).
  const meets = meetsNoveltyFloor(gen.tier, target);
  const used = state.flags.general_reroute_count ?? 0;
  const capExhausted = used >= REROUTE_CAP;
  const hasDirective = !!gen.improvement_directive?.trim();
  const canReroute = gen.salvageable && hasDirective && !capExhausted;

  let decision: string;
  if (meets) {
    decision = "ACCEPT — tier ≥ floor; live pipeline would proceed to F1.";
  } else if (canReroute) {
    decision = `REVISE → re-run D0 carrying the directive (reroute ${used + 1}/${REROUTE_CAP}).`;
  } else if (gen.salvageable && hasDirective && capExhausted) {
    decision = `REJECT/HALT — salvageable + directive, but reroute cap (${REROUTE_CAP}) exhausted.`;
  } else {
    decision = "REJECT/HALT — not salvageable (dead object / open-ended lift / no directive).";
  }
  const verdict = buildGeneralTierVerdict(gen, target, canReroute, capExhausted && gen.salvageable && hasDirective);

  console.log("\n===== D0.5.G cold-referee result =====");
  console.log(`tier:                 ${gen.tier}   (floor for ${target}: ${meets ? "MET" : "BELOW"})`);
  console.log(`salvageable:          ${gen.salvageable}`);
  console.log(`improvement_directive:${gen.improvement_directive ? "\n  " + gen.improvement_directive : " (none)"}`);
  console.log(`flagged_labels:       ${gen.flagged_conjecture_labels.join(", ") || "(none)"}`);
  console.log(`general_reroute_count:${used} (cap ${REROUTE_CAP})`);
  console.log(`\n>>> ROUTING DECISION:  ${decision}`);
  console.log(`    boundary verdict status = ${verdict.status}`);
  console.log("\n--- critique ---\n" + gen.critique + "\n");
}

main().catch((err) => {
  console.error(err instanceof Error ? err.stack ?? err.message : String(err));
  process.exit(1);
});
