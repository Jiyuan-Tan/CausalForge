// Throwaway: assemble the EXACT prompt each agent receives in the current (redesign)
// D-1.2 and D0 pipelines, for human review. Reconstructs the same assembly as each
// stage's .ts against the stat_ate_overlap_decay context. The renders are pure
// (renderCoreTex); D0-RENDER has no prompt (deterministic).
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { findRepoRoot } from "../src/cli.js";
import { baseBrief, discoveryBrief, readPrompt, artifactPaths } from "../src/pipeline_support.js";
import { clusterFor, loadDiscoveryClusterSetupBlock } from "../src/discovery/stage0.js";
import { protoCoreJsonPath } from "../src/discovery/stage_neg1_2_proto_core.js";
import { coreJsonPath } from "../src/discovery/stage0_core.js";
import { proofFilePath } from "../src/discovery/stage0_prove.js";
import { buildDrafterHandoff } from "../src/discovery/stageNeg1_2.js";
import { tierFloorBlock } from "../src/pipeline_stages.js";
import { renderCoreTex } from "../src/discovery/core/render_tex.js";
import { CoreSchema, type Core } from "../src/discovery/core/schema.js";
import type { PipelineContext, StateJson } from "../src/types.js";

const repoRoot = findRepoRoot(path.dirname(fileURLToPath(import.meta.url)));
const QID = "stat_ate_overlap_decay";
const SPEC = "v1";
const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: false } as PipelineContext;
const state = {
  stage_completed: "0",
  lean_subdir: `CausalSmith/Stat/${QID}`,
  pending_sorries: [], design_decisions: {}, added_assumptions: [],
  flags: { local_fix_from_4d: false, missing_architecture: false },
  proposed_from: { topic: "overlap-decay ATE minimax rate", novelty_target: "field", chosen_qid: QID, chosen_specialization: SPEC, cluster: "stat" },
} as unknown as StateJson;

const brief = discoveryBrief(ctx, state);
const clusterBlock = await loadDiscoveryClusterSetupBlock(ctx, clusterFor(ctx, state));

// the discharged D0 core (for PROVE/0.5/R context) and the D-1 proposal core
const d0Core: Core = CoreSchema.parse(JSON.parse(await readFile(new URL("../test/fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8")));
const protoCore: Core = CoreSchema.parse(JSON.parse(await readFile(new URL("../test/fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url), "utf8")));

const out: Record<string, string> = {};

// ---- D-1.2 author (single) — uses the Causalean-free discovery brief ----
out["D-1.2_author"] = [
  await readPrompt(ctx, "stage_neg1_2_proto_core.txt"), "",
  discoveryBrief(ctx, state),
  "\n[At run time the wiring also APPENDS here: the D-1.1 gaps/literature block, the cold-start motif library, the Stage-0.5 rejection block, the upgrade-parent block, and (on revise) the prior reviewer verdict.]\n",
  `Write the typed proposal core JSON to this path (create it): ${protoCoreJsonPath(ctx)}`,
  'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<proto_core.json>"], "literature_checklist":[...]}.',
].join("\n");

// ---- D0-CORE (copy + extend the frozen D-1.2 proposal core) ----
const protoBlock = [
  "=== FROZEN PROPOSAL CORE (from D-1.2 — COPY VERBATIM, then extend in place) ===",
  JSON.stringify(protoCore, null, 2),
  "=== END FROZEN PROPOSAL CORE ===",
  "Reproduce every field above UNCHANGED, then add ONLY: a `route` per statement, and",
  "the lemma decomposition (new `lem:` nodes with routes + `depends_on`; you may extend",
  "the headline statements' `depends_on` to cite them). Do NOT alter symbols, assumptions,",
  "definitions, the headline statements' claims/kinds/status/prose, the estimand, or the",
  "prose fields — they are frozen at D-1 (a mechanical check rejects any change).",
  "",
].join("\n");
out["D0-CORE"] = [
  await readPrompt(ctx, "stage0_common_discovery.txt"), "", clusterBlock, "",
  await readPrompt(ctx, "stage0_core.txt"), "", brief, "",
  protoBlock,
  `Write the typed core JSON to this path (create it): ${coreJsonPath(ctx)}`,
  'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<core.json>"]}.',
].join("\n");

// ---- D0-PROVE (one node: thm:lower) ----
const node = d0Core.statements.find((s) => s.id === "thm:lower")!;
const frozenContext = JSON.stringify({
  symbols: d0Core.symbols, assumptions: d0Core.assumptions, definitions: d0Core.definitions,
  statements: d0Core.statements.map((s) => ({ id: s.id, kind: s.kind, statement: s.statement, depends_on: s.depends_on })),
}, null, 2);
out["D0-PROVE_thm-lower"] = [
  await readPrompt(ctx, "stage0_common_discovery.txt"), "", clusterBlock, "",
  await readPrompt(ctx, "stage0_prove.txt"), "", brief, "",
  "=== FROZEN CORE (read-only context) ===", frozenContext, "",
  "=== NODE TO PROVE ===", JSON.stringify(node, null, 2), "",
  `PROOF_OUTPUT_PATH: ${proofFilePath(ctx, node.id)}`,
  'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<proof.json>"]}.',
].join("\n");

// ---- D0.5 (math referee; general/decision differ only in the referee prompt) ----
out["D0.5_math"] = [
  await readPrompt(ctx, "stage0_5_math_review.txt"), "",
  await readPrompt(ctx, "stage0_5_core_adapter.txt"), "", brief, "",
  "=== CORE UNDER REVIEW ===", JSON.stringify(d0Core, null, 2), "",
  "VERDICT_OUTPUT_PATH: <path>",
  'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<verdict.json>"]}.',
].join("\n");

// ---- D0.R (reviser) ----
out["D0.R"] = [
  await readPrompt(ctx, "stage0_R_core.txt"), "", brief, "",
  "=== CURRENT CORE (edit in place) ===", JSON.stringify(d0Core, null, 2), "",
  "=== D0.5 FINDINGS (the directed floor — every one is must-fix) ===",
  JSON.stringify([{ referee: "math", node_id: "thm:lower", code: "omission", one_line: "tighten the TV bound" }], null, 2), "",
  `CORE_FILE: ${coreJsonPath(ctx)}`,
  'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<core.json>"]}.',
].join("\n");

// ---- D-0.5 reviewer (single-artifact: core rubric + inlined core; no adapter, no .tex feed) ----
const reviewPrompt = `${await readPrompt(ctx, "stage_neg1_review_core.txt")}\n\n${await readPrompt(ctx, "stage_flagship_rubric.txt")}`;
const protoCoreBlock = [
  "=== PROPOSAL CORE (the artifact under review — typed source of truth) ===",
  JSON.stringify(protoCore, null, 2),
  "=== END PROPOSAL CORE ===",
].join("\n");
const sampleDraftJson = {
  chosen_qid: QID, chosen_specialization: SPEC, version: 1, mode: "cold-start",
  literature_checklist: [{ author: "Tsybakov", year: 2009, venue: "Springer", bibkey: "Tsybakov2009", one_line: "minimax lower-bound machinery", relevant_to: "thm:lower" }],
  novelty_justification: { repo_axis: "no in-repo overlap-decay rate", published_axis: "no matching converse published" },
  comparator_promise_table: [{ bibkey: "ChernozhukovEtAl2018", claim: "root-n AIPW under strict overlap", matched_conjecture: "thm:upper" }],
};
const reviewPaths = artifactPaths(ctx, state);
out["D-0.5_reviewer"] = [
  reviewPrompt, "",
  protoCoreBlock, "",
  "=== ORCHESTRATOR-PROVIDED INPUTS ===",
  `proposal_path: ${reviewPaths.proposalTex}`,
  `Output JSON template (READ THIS, fill TODOs, emit on stdout): ${reviewPaths.proposalReviewOutputJson}`,
  `novelty_target: field`,
  "Return ONLY the JSON object obtained by filling the output template.",
  "",
  tierFloorBlock("field"),
  "=== DRAFTER HANDOFF (load-bearing — this is the named literature checklist the reviewer prompt expects) ===",
  buildDrafterHandoff(sampleDraftJson),
  "=== END DRAFTER HANDOFF ===",
  // single-artifact: the core is inlined above; the .tex render is NOT double-fed.
].join("\n");

for (const [name, body] of Object.entries(out)) {
  await writeFile(`/tmp/prompt_${name}.txt`, body, "utf8");
  console.log(`${name}: ${body.length} chars -> /tmp/prompt_${name}.txt`);
}
// deterministic renders (no agent)
await writeFile("/tmp/render_D0_note.tex", renderCoreTex(d0Core), "utf8");
await writeFile("/tmp/render_D-1_proposal.tex", renderCoreTex(protoCore), "utf8");
console.log("renders -> /tmp/render_D0_note.tex, /tmp/render_D-1_proposal.tex (deterministic, no agent)");
