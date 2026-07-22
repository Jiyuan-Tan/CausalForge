// Cluster routing + setup-block loading, shared across the discovery stages.
//
// Extracted from the (retired) monolithic Stage 0 (`stage0.ts`) so the typed
// D0-SOLVE path (`stage0_solve.ts`) can depend on these helpers without pulling
// in the deleted legacy orchestrator. Pure routing/prompt-assembly — no codex.

import type { PipelineContext, StateJson } from "../types.js";
import { readPrompt } from "../pipeline_support.js";

export type Cluster = "panel" | "exactid" | "partialid" | "stat" | "experimentation" | "scm";

export function clusterFor(ctx: PipelineContext, state: StateJson): Cluster | null {
  const fromState = state.proposed_from?.cluster;
  if (fromState === "panel" || fromState === "exactid" || fromState === "partialid" || fromState === "stat" || fromState === "experimentation" || fromState === "scm") return fromState;
  // Fallback: qid prefix convention.
  //   eid_*    → exactid
  //   pid_*    → partialid
  //   stat_*   → stat (estimation and inference theory of a causal estimand)
  //   panel_*  → panel (free-form panel kernel)
  const qid = ctx.qid.toLowerCase();
  if (qid.startsWith("eid_")) return "exactid";
  if (qid.startsWith("pid_")) return "partialid";
  if (qid.startsWith("stat_")) return "stat";
  if (qid.startsWith("exp_")) return "experimentation";
  if (qid.startsWith("scm_")) return "scm";
  if (qid.startsWith("panel_")) return "panel";
  return null;
}

/** Strip the "In-repo substrate (informational only …)" paragraph — the only
 * Causalean push in the cluster setup blocks — for DISCOVERY use. Removes the
 * heading line and the following non-blank lines (the substrate bullet list).
 * Leaves the math setup untouched. No-op when the marker is absent (e.g. panel). */
function stripInRepoSubstrate(block: string): string {
  const lines = block.split("\n");
  const start = lines.findIndex((l) => /^\s*In-repo substrate \(informational only/i.test(l));
  if (start === -1) return block;
  let end = start + 1;
  while (end < lines.length && lines[end].trim() !== "") end += 1;
  lines.splice(start, end - start);
  return lines.join("\n").replace(/\n{3,}/g, "\n\n");
}

/** Discovery variant of the cluster setup block: the same math setup with the
 * Causalean "In-repo substrate" paragraph removed (D stages reason about math,
 * not formalization). */
export async function loadDiscoveryClusterSetupBlock(
  ctx: PipelineContext,
  cluster: Cluster | null,
): Promise<string> {
  return stripInRepoSubstrate(await loadClusterSetupBlock(ctx, cluster));
}

export async function loadClusterSetupBlock(
  ctx: PipelineContext,
  cluster: Cluster | null,
): Promise<string> {
  if (cluster === "panel") return readPrompt(ctx, "stage0_setup_panel.txt");
  if (cluster === "exactid") return readPrompt(ctx, "stage0_setup_exactid.txt");
  if (cluster === "partialid") return readPrompt(ctx, "stage0_setup_partialid.txt");
  if (cluster === "stat") return readPrompt(ctx, "stage0_setup_stat.txt");
  if (cluster === "experimentation") return readPrompt(ctx, "stage0_setup_experimentation.txt");
  if (cluster === "scm") return readPrompt(ctx, "stage0_setup_scm.txt");
  // Unknown cluster: inject all six so the model can pick from the locked-parameter tuple itself.
  const [a, b, c, d, e, f] = await Promise.all([
    readPrompt(ctx, "stage0_setup_panel.txt"),
    readPrompt(ctx, "stage0_setup_exactid.txt"),
    readPrompt(ctx, "stage0_setup_partialid.txt"),
    readPrompt(ctx, "stage0_setup_stat.txt"),
    readPrompt(ctx, "stage0_setup_experimentation.txt"),
    readPrompt(ctx, "stage0_setup_scm.txt"),
  ]);
  return [a, "", b, "", c, "", d, "", e, "", f].join("\n");
}
