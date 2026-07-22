// Formalization Stage 2. Extracted from pipeline_stages.ts in Step 2.3 of the three-submodules refactor.

import path from "node:path";
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { MODEL_PLAN } from "../constants.js";
import type { Intervention, ReviewResult } from "../judgment.js";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  bookkeepingPolicyBlock,
  correctionBlock,
  findLeanDeclByLocalId,
  parseStageOutput,
  readIfExists,
  readPrompt,
  listLeanFiles,
  type StageDeps,
} from "../pipeline_support.js";
import { createRetrieval } from "./reuse_retrieval.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { CoreSchema } from "../discovery/core/schema.js";
import { runPlanGate, type PlanGateViolation } from "./plan/plan_gate.js";
import { PlanSchema } from "./plan/schema.js";
import { PROOF_SCAFFOLD_MAX, STAGE2_REDIRECT_MAX } from "./loop_limits.js";
import { interventionBlock } from "../shared/intervention_routing.js";
import { writeLeanLspMcpConfig } from "../workers/claude.js";
import { dispatchAgent, dispatchClaudeAgent } from "../framework/agent_dispatch.js";
import {
  snapshotPriorProofs,
  injectCarryoverComments,
  restoreCarryoverProofs,
} from "./proof_carryover.js";
import {
  recordMissingArchitecture,
  missingArchitectureLedgerPath,
} from "../shared/missing_architecture_ledger.js";
import { seedAnnotations } from "../graph/annotate.js";
import { extractFromLean } from "../graph/extractor.js";
import { graphPath, loadGraph, saveGraph } from "../graph/store.js";
import { validate } from "../graph/validator.js";
import type { FormalizationGraph, Finding } from "../graph/types.js";
import { markUnreviewed } from "../graph/mutate.js";
import { objIdToNodeId } from "../graph/from_note.js";
import {
  findStatementSemanticDefs,
  parseLeanDecls,
  type StatementSemanticDef,
} from "./crosswalk.js";
import { laterStageEverRan } from "../shared/resume_mode.js";
import { buildRunModules } from "./proof_review_loop.js";

/** Headline nodes whose statement meaning changed through an untagged inline
 * definition/structure during an F2 revise pass.  The headline's own Lean
 * signature hash can remain byte-identical while the body of (for example) its
 * output structure changes, so hash-only graph refresh would otherwise carry a
 * stale `matched` F2.5 verdict. */
export function hiddenDefinitionChangeTargets(
  before: StatementSemanticDef[],
  after: StatementSemanticDef[],
): string[] {
  const oldByName = new Map(before.map((d) => [d.name, d] as const));
  const newByName = new Map(after.map((d) => [d.name, d] as const));
  const names = new Set([...oldByName.keys(), ...newByName.keys()]);
  const targets = new Set<string>();
  for (const name of names) {
    const old = oldByName.get(name);
    const cur = newByName.get(name);
    if (old?.contentHash === cur?.contentHash) continue;
    for (const id of [...(old?.reachedFrom ?? []), ...(cur?.reachedFrom ?? [])]) {
      targets.add(objIdToNodeId(id));
    }
  }
  return [...targets].sort();
}

/** A source correction can be applied manually before F2 starts, so comparing
 * only the pre/post-F2 snapshots cannot discover it.  Consume the authoritative
 * receipt once and force its declared delta back into the graph review frontier. */
export function pendingSourceRewindDirtyNodeIds(state: StateJson): string[] {
  const rewind = state.flags.source_rewind;
  if (rewind?.status !== "applied") return [];
  return [...new Set(rewind.dirty_nodes)].sort();
}

/** Parse `-- @node: <id>` and `-- @env: <id>` tag comments from every .lean file in
 *  a directory, so the plan gate can verify the emitted Lean covers the plan (P7). */
export async function parseLeanNodeTags(
  leanDir: string,
): Promise<{ nodes: Set<string>; envs: Set<string> }> {
  const nodes = new Set<string>();
  const envs = new Set<string>();
  if (!existsSync(leanDir)) return { nodes, envs };
  let files: string[];
  try {
    files = await listLeanFiles(leanDir);
  } catch {
    return { nodes, envs };
  }
  for (const f of files) {
    let text: string;
    try {
      text = await readFile(f, "utf8");
    } catch {
      continue;
    }
    // Ownership/environment anchors are top-level metadata and therefore must
    // start in column zero. This excludes both prose mentions and an indented
    // duplicate accidentally emitted inside a declaration body.
    for (const m of text.matchAll(/^--\s*@node:\s*([A-Za-z0-9:._-]+)\s*$/gm)) nodes.add(m[1]);
    for (const m of text.matchAll(/^--\s*@env:\s*([A-Za-z0-9:._-]+)\s*$/gm)) envs.add(m[1]);
  }
  return { nodes, envs };
}

export interface DuplicateLeanNodeAnchor {
  id: string;
  locations: string[];
}

/** Return repeated canonical node anchors across the entire run tree.  A Set-based
 * coverage gate cannot detect these, and the graph extractor intentionally rejects
 * them only after extraction, so F2 checks multiplicity directly before advancing. */
export async function findDuplicateLeanNodeAnchors(
  leanDir: string,
): Promise<DuplicateLeanNodeAnchor[]> {
  if (!existsSync(leanDir)) return [];
  const byId = new Map<string, string[]>();
  for (const file of await listLeanFiles(leanDir)) {
    const text = await readFile(file, "utf8").catch(() => "");
    for (const [index, line] of text.split(/\r?\n/).entries()) {
      const match = /^--\s*@node:\s*([A-Za-z0-9:._-]+)\s*$/.exec(line);
      if (!match) continue;
      const locations = byId.get(match[1]) ?? [];
      locations.push(`${file}:${index + 1}`);
      byId.set(match[1], locations);
    }
  }
  return [...byId.entries()]
    .filter(([, locations]) => locations.length > 1)
    .map(([id, locations]) => ({ id, locations }))
    .sort((a, b) => a.id.localeCompare(b.id));
}

function nonEmittedLocalIdsFromPlan(planText: string): Set<string> {
  if (!planText.trim()) return new Set();
  try {
    const parsed = PlanSchema.safeParse(JSON.parse(planText));
    if (!parsed.success) return new Set();
    return new Set(
      Object.values(parsed.data.nodes)
        .filter((n) => (n.gate || n.delivery_status === "undelivered") && n.local_id)
        .map((n) => n.local_id!),
    );
  } catch {
    return new Set();
  }
}

/** Durable F2 instruction for disclosed non-delivery. These nodes remain in the
 * core/plan/graph, but must have no Lean declaration or @node anchor. */
export function undeliveredBlockFromPlan(planText: string): string {
  if (!planText.trim()) return "";
  try {
    const parsed = PlanSchema.safeParse(JSON.parse(planText));
    if (!parsed.success) return "";
    const rows = Object.entries(parsed.data.nodes)
      .filter(([, n]) => n.delivery_status === "undelivered")
      .map(([id, n]) => `  • ${id} (${n.delivery_role ?? "cited"}): ${n.delivery_reason ?? "reason missing"}`);
    if (rows.length === 0) return "";
    return [
      "=== UNDELIVERED OBJECTS — RETAIN IN PLAN, OMIT FROM LEAN ===",
      "The plan gate has classified the following objects as disclosed undelivered remarks.",
      "For each one, remove any existing Lean declaration and its `-- @node:` tag. Do not replace",
      "it with a Prop definition, axiom, gate, weakened theorem, or `sorry`. Preserve every unrelated",
      "declaration and proof body. The typed statement remains in core/plan/graph for presentation.",
      ...rows,
      "=== END UNDELIVERED OBJECTS ===",
      "",
    ].join("\n");
  } catch {
    return "";
  }
}

/** Scaffold-side dual of the F2.5/F4 gated-review exemption: build a directive telling the producer
 *  to emit each registered `gate_class:"gated"` node (from bin/gate.ts) as an EXPLICIT `_of_gate`
 *  HYPOTHESIS on every consumer that threads it in `hyps` — NOT an in-proof `have … := by sorry`.
 *  Without this the producer treats a note-DERIVED gate as an in-proof obligation (the general bias),
 *  re-emits a `sorry`, and the filler escalates `build-substrate` on debt we chose to assume. Reading
 *  it from the plan (not a hand-set free-text directive) is what lets `bin/gate.ts` register a durable
 *  gate that survives every re-scaffold with no hand-editing. Empty when there are no gated nodes. */
function gatedHypsBlockFromPlan(planText: string): string {
  if (!planText.trim()) return "";
  let plan: { nodes?: Record<string, { gate?: boolean; gate_class?: string; lean_name?: string; hyps?: string[] }> };
  try {
    const parsed = PlanSchema.safeParse(JSON.parse(planText));
    if (!parsed.success) return "";
    plan = parsed.data as typeof plan;
  } catch {
    return "";
  }
  const nodes = plan.nodes ?? {};
  const gated: { leanName: string; consumers: string[] }[] = [];
  for (const [id, n] of Object.entries(nodes)) {
    if (!n.gate || n.gate_class === "cited") continue; // only `gated` (cited is source-matched, not a hyp)
    const consumers = Object.entries(nodes)
      .filter(([, c]) => Array.isArray(c.hyps) && c.hyps.includes(id))
      .map(([cid, c]) => c.lean_name || cid);
    gated.push({ leanName: n.lean_name || id, consumers });
  }
  if (!gated.length) return "";
  return [
    "=== GATED SUBSTRATE-GATES — EMIT AS HYPOTHESES (registered via bin/gate.ts) ===",
    "",
    'The plan registers the DISCLOSED substrate-gate(s) below (`gate:true`, `gate_class:"gated"`). Each is',
    "an ASSUMED input — a classical / research-level fact this paper does NOT prove here (tracked in",
    "SUBSTRATE_DEBT.md). For EACH gate, emit it as an EXPLICIT `_of_gate`-style HYPOTHESIS on the signature",
    "of every listed consumer, and pass it through. This OVERRIDES the general 'derive a note-fact in-proof'",
    "guidance for THESE nodes specifically: do NOT inline them as an in-proof `have … := by sorry`, and do",
    "NOT drop them. A gate held as a signature hypothesis makes the consumer a sorry-free CONDITIONAL (the",
    "goal); an in-proof `sorry` makes it an un-closable obligation (not the goal). These are the ONLY",
    "hypotheses you may add that the note does not itself list — every other added premise is still drift.",
    "",
    ...gated.map((g) => `  • gate \`${g.leanName}\` → hypothesis on: ${g.consumers.join(", ") || "(no consumers threaded in plan hyps)"}`),
    "",
    "=== END GATED SUBSTRATE-GATES ===",
    "",
  ].join("\n");
}

function declNameRegex(name: string): RegExp {
  return new RegExp(`^\\s*(?:noncomputable\\s+|private\\s+|protected\\s+|scoped\\s+)*(?:theorem|lemma|def|abbrev|structure|class|instance)\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "m");
}

/** Best-effort F2 graph link: seed `-- @node:` annotations from the obj_id
 *  convention, extract the Lean side into the graph (links, proof state,
 *  statement-uses edges), persist, and return advisory validation findings.
 *  Never throws, never blocks the scaffold; no gate depends on the graph yet. */
export async function linkGraphFromStage2(a: {
  qid: string;
  spec: string;
  formalizationDir: string;
  leanDir: string;
  /** From-note rows whose cached review must be invalidated because an inline,
   * meaning-bearing dependency changed while their own signature stayed fixed. */
  invalidateReviewNodeIds?: string[];
}): Promise<{ graph: FormalizationGraph | null; findings: Finding[] }> {
  try {
    const p = graphPath(a.formalizationDir, a.qid, a.spec);
    if (!existsSync(p)) return { graph: null, findings: [] };
    await seedAnnotations(a.leanDir);
    const g = await loadGraph(p);
    const extracted = await extractFromLean(g, a.leanDir);
    let graph = extracted.graph;
    for (const id of a.invalidateReviewNodeIds ?? []) {
      const node = graph.nodes.find((n) => n.id === id);
      if (node?.provenance === "from-note") graph = markUnreviewed(graph, id);
    }
    await saveGraph(p, graph);
    return { graph, findings: validate(graph).findings };
  } catch {
    return { graph: null, findings: [] };
  }
}

/**
 * F2 may leave reuse lookup (P5) and module-resolution (P6) drift to the later typed phases.
 * Every other plan-gate code is structural/semantic and must refuse the scaffold.
 */
export function blockingPostSyncPlanViolations(violations: PlanGateViolation[]): PlanGateViolation[] {
  return violations.filter((violation) => violation.code !== "P5" && violation.code !== "P6");
}

export async function runStage2(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  priorReview?: ReviewResult | null;
  intervention?: Intervention | null;
  attempt?: number;
}): Promise<StageResult> {
  const paths = artifactPaths(args.ctx, args.state);
  const sourceRewindDirtyTargets = pendingSourceRewindDirtyNodeIds(args.state);
  const planText = await readIfExists(paths.plan);
  const nonEmittedLocalIds = nonEmittedLocalIdsFromPlan(planText);
  const gatedHypsBlock = gatedHypsBlockFromPlan(planText);
  const undeliveredBlock = undeliveredBlockFromPlan(planText);
  const redirectBlock =
    args.state.flags.scaffold_redirect
      ? [
          "=== SCAFFOLD REDIRECT DIRECTIVE (from prior Stage 3 intervention) ===",
          "",
          "Apply this directive verbatim as a top-priority constraint on top of the .md spec.",
          "Do NOT interpret it loosely; do NOT negotiate it.",
          "When the directive says the Lean OMITS / drops / weakens a hypothesis, condition, or clause",
          "that the note (spec) STATES, the faithful fix is to ADD that condition to the STATEMENT",
          "signature of the named target(s) — changing the signature here is EXPECTED and REQUIRED, not",
          "something to avoid. Resolving such a drift by editing only docstrings/comments to 'acknowledge'",
          "or 'note' the gap is FORBIDDEN: it leaves the statement unfaithful and the drift just re-flags.",
          "What you must NOT do is INVENT a hypothesis the spec does not state in order to make a target",
          "vacuously pass (gerrymandering) — only add conditions the note/spec actually states.",
          "",
          args.state.flags.scaffold_redirect,
          "",
          args.state.flags.proof_loop_counters
            ? `Proof-loop scaffold attempt: ${args.state.flags.proof_loop_counters.scaffold_rounds} of ${PROOF_SCAFFOLD_MAX} max.`
            : `Stage-2 redirect attempt: ${args.state.flags.scaffold_redirect_count ?? 1} of ${STAGE2_REDIRECT_MAX} max.`,
          "",
          "=== END SCAFFOLD REDIRECT DIRECTIVE ===",
          "",
        ].join("\n")
      : "";
  // REVISE / PATCH-IN-PLACE MODE (token-saver, drift-guard, proof-preserver). When
  // a prior scaffold is ALREADY on disk — an in-loop F2.5 revise OR a Stage-3
  // scaffold_redirect rewind — only the flagged/directed declarations (plus their
  // consistency ripples) need to change. Regenerating every file from the .md is
  // slow, burns tokens, drifts on declarations that already passed, AND DISCARDS any
  // real proof bodies Stage 3 already filled (and the carry-over comments that
  // preserve them). So we hand the producer the on-disk files and tell it to Edit in
  // place. A scaffold_redirect's directive is normally localized (it names specific
  // decls); editing in place keeps every other decl — and its proof — intact.
  // A `--from-stage F2` re-entry after any later stage ran is also a revise,
  // even when it carries only a persistent f2_scaffold_directive: treating it
  // as attempt 1 would replace every working proof with `sorry`.
  // (Not used on a true attempt 1, where there is no prior scaffold to patch.)
  let reviseBlock = "";
  const hasLaterStageHistory = await laterStageEverRan(args.ctx, args.state, "2");
  const patchInPlace =
    args.priorReview?.status === "revise" ||
    !!args.state.flags.scaffold_redirect ||
    hasLaterStageHistory;
  if (patchInPlace && existsSync(paths.leanDir)) {
    const existing = (await listLeanFiles(paths.leanDir)).sort();
    if (existing.length > 0) {
      reviseBlock = [
        await readPrompt(args.ctx, "stage2_head_revise.txt"),
        "",
        args.state.flags.scaffold_redirect
          ? "Apply the SCAFFOLD REDIRECT DIRECTIVE above. You MAY re-render the named target(s) however is needed for a faithful fix — a faithful equivalent formulation, new auxiliary defs, or restructuring — you are NOT limited to a byte-for-byte in-place edit (F2.5 re-reviews only the dirty/not-cleared frontier). Preserve existing proof bodies and `/-! PRIOR PROOF (carry-over…) -/` comments wherever the statement is unchanged, and leave UNRELATED declarations intact — don't churn them. When editing a named target is a SHARED env/structure declaration (e.g. retyping/constraining a structure field like `Observation.A` to match a core symbol's space) and the change FORCES dependent declarations to change in order to recompile (signatures, call sites), you MUST re-sync exactly those forced dependents — but still leave every UNRELATED declaration byte-for-byte. (Ripple that the edit makes mandatory is allowed; gratuitous edits are not.) A redirect target of the form `sym:<symbol>` denotes a SETUP/ENVIRONMENT symbol whose space (e.g. `propensity ∈ (0,1)`) is realized by a CLUSTER of decls — the carrier-type structure field PLUS the predicate(s) that pin its range. The cluster IS the affected region: grep the files for `@realizes <symbol>` to find every member, then make the symbol's space hold across their CONJUNCTION (constrain the field, add/repair an a.s. invariant or well-formedness clause, or retype only if a finite/discrete space like `{0,1}` warrants it — prefer carrier-type-`ℝ` + a predicate clause when witness measures need `ℝ`). Keep each member's `@realizes <symbol>(<clause hint>)` tag accurate, and add the tag to any decl you newly make load-bearing for that symbol."
          : "",
        "On-disk files to patch (Read first, then Edit):",
        ...existing.map((f) => `  - ${f}`),
        "",
      ].filter(Boolean).join("\n");
    }
  }
  // PERSISTENT orchestrator scaffold directive (analogue of F3's `f3_filler_directive`):
  // read on EVERY scaffold/revise pass, uncapped and never self-cleared, until the
  // orchestrator clears it via `bin/f2_directive.ts`. A faithfulness/statement-shape steer.
  const persistentDirectiveBlock =
    args.state.flags.f2_scaffold_directive
      ? [
          "=== PERSISTENT ORCHESTRATOR SCAFFOLD DIRECTIVE (applies to EVERY scaffold pass) ===",
          "",
          "A top-priority, PERSISTENT faithfulness constraint from the orchestrator. Apply it verbatim,",
          "on top of the .md spec, on THIS and every subsequent scaffold/revise pass (it is NOT one-shot",
          "and NOT capped). It steers statement SHAPE / faithfulness only: NEVER invent a hypothesis the",
          "spec does not state and NEVER weaken a statement; the F2.5 review + anti-laundering gates still",
          "apply. When it says the Lean over-assumes a fact the note DERIVES (e.g. a continuity/boundedness",
          "property, an algebraic identity), the fix is to DROP that premise and derive it in-proof",
          "(`have h : … := by sorry`), not to keep it as a hypothesis.",
          "",
          args.state.flags.f2_scaffold_directive,
          "",
          "=== END PERSISTENT ORCHESTRATOR SCAFFOLD DIRECTIVE ===",
          "",
        ].join("\n")
      : "";
  const prompt = [
    persistentDirectiveBlock,
    undeliveredBlock,
    gatedHypsBlock,
    redirectBlock,
    correctionBlock(args.priorReview ?? null, args.attempt ?? 1, {
      manifestContract: (args.state.theorems?.length ?? 0) > 0,
    }),
    reviseBlock,
    interventionBlock(args.intervention),
    await readPrompt(args.ctx, "stage2_scaffold.txt"),
    "",
    bookkeepingPolicyBlock(),
    "",
    baseBrief(args.ctx, args.state),
    "",
    // F2 implements the plan F1 already authored: per-node reuse / define-local
    // decisions, the env world, the node→Lean mapping. The reuse SEARCH happened at
    // F1; F2 does not re-run retrieval. The typed core is the ground truth for the
    // node statements/conditions the plan maps.
    `Formalization plan (plan.json — the contract you implement; for every DELIVERED node, tag EXACTLY ONE canonical primary declaration with "-- @node: <id>"; leave companion/auxiliary declarations untagged; an UNDELIVERED node emits no declaration and no tag; tag the S-block with "-- @env: <id>"). Additionally, for the SETUP/ENVIRONMENT symbols: tag EVERY Lean location that helps realize a core symbol's space with "@realizes <core-symbol-name>(<short clause hint>)" — using the EXACT core symbol name (e.g. mu_0, tau_P, e_P, pi, Pi; case-sensitive, NOT the Lean field name mu0/contrast). Put the tag at the most SPECIFIC location: for a structure FIELD, an INLINE trailing comment on that field line (e.g. 'propensity : 𝒳 → ℝ -- @realizes e_P(carrier 𝒳→ℝ; range via WellFormedLaw)'), NOT lumped on the structure docstring; for a MULTI-clause predicate (a Prop def of the form A and B and …), an INLINE comment on the SPECIFIC conjunct line that pins each symbol (e.g. in WellFormedLaw, the 'contrast x = mu1 x - mu0 x' conjunct line gets '-- @realizes tau_P(contrast = mu1 - mu0)' and the 'propensity x ∈ Icc 0 1' conjunct line gets '-- @realizes e_P(propensity ∈ Icc 0 1)'); a SINGLE-clause predicate may use its docstring (e.g. Positivity gets '@realizes e_P(a.s. 0<e<1)'). A symbol's space is normally carried by the CONJUNCTION of its carrier-type field PLUS the predicate(s) that pin its range, so the SAME symbol gets tagged on several locations (the field line AND each constraining predicate); the reviewer grades that whole cluster together. Tag EVERY core symbol in the JSON — not only setup-world ones — so the symbol→Lean crosswalk is COMPLETE: a primitive on its carrier field + constraining predicate; a quantity the paper DEFINES by a formula on the \`def\` that computes it; a symbol introduced only inside a theorem statement (e.g. an existential multiplier) on the clause that pins its range. Never tag a decl that merely USES a symbol without introducing it:\n${planText}`,
    "",
    `Typed core JSON (ground truth for each node's statement / condition):\n${await readIfExists(coreJsonPath(args.ctx))}`,
    "",
    "Return JSON. If blocked-missing-architecture, include missing_items exactly.",
  ].join("\n");
  // Rewind proof-preservation: snapshot the real proof bodies currently on disk
  // BEFORE the producer overwrites them, so we can re-attach those that survive a
  // signature match (see injectCarryoverComments after the producer runs). Empty
  // on a first scaffold or a sorry-only prior (nothing to preserve).
  const priorProofs = await snapshotPriorProofs(paths.leanDir);
  // Snapshot the typed-theorem → meaning-bearing inline-def closure before the
  // producer edits.  This is deliberately separate from proof carry-over: a
  // theorem can keep the same signature/proof while an output structure or
  // predicate it names changes semantics and therefore requires delta review.
  let priorSemanticDefs: StatementSemanticDef[] = [];
  if (patchInPlace && existsSync(paths.leanDir)) {
    try {
      priorSemanticDefs = await findStatementSemanticDefs(paths.leanDir);
    } catch (err) {
      console.warn(
        `[causalsmith] Stage 2 hidden-definition snapshot failed (continuing): ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }

  // Producer dispatch: F2 can be claude/opus or codex/gpt-5.5 (see MODEL_PLAN.stage2).
  // Widened cast so both branches typecheck regardless of which is configured.
  const plan = MODEL_PLAN.stage2 as { runner: string; model: string; effort?: string };
  const stage2PromptSources = [
    "stage2_scaffold.txt",
    ...(reviseBlock ? ["stage2_head_revise.txt"] : []),
    paths.plan,
    ...(args.state.flags.scaffold_redirect ? ["flags.scaffold_redirect"] : []),
    ...(args.state.flags.f2_scaffold_directive ? ["flags.f2_scaffold_directive"] : []),
  ];
  let out: string;
  if (plan.runner === "codex") {
    // codex writes the .lean files directly (workspace-write) and gets lean-lsp
    // for the substrate survey, like F3. parseStageOutput is tolerant: on a
    // non-JSON tail it falls back to "completed" (artifacts re-derived by F2.5's
    // re-enrichment of the on-disk .lean), so the missing manifest is harmless on
    // legacy (theorems-less) runs.
    const res = await dispatchAgent({
      ctx: args.ctx,
      deps: args.deps,
      stage: "2",
      label: "F2 scaffolder (codex)",
      prompt,
      promptSources: stage2PromptSources,
      model: plan.model,
      reasoningEffort: (plan.effort ?? "high") as "minimal" | "low" | "medium" | "high" | "xhigh",
      inactivityTimeoutMs: 30 * 60 * 1000,
      leanLsp: true,
    });
    out = res.stdout;
  } else {
    out = await dispatchClaudeAgent({
      ctx: args.ctx,
      deps: args.deps,
      stage: "2",
      label: "F2 scaffolder (claude)",
      promptSources: stage2PromptSources,
      input: {
        prompt,
        model: plan.model,
        cwd: args.ctx.repoRoot,
        mcpConfigPath: writeLeanLspMcpConfig(args.ctx.repoRoot),
        allowedTools: [
          "Read",
          "Write",
          "Edit",
          "Grep",
          "Glob",
          "Bash",
          "mcp__lean-lsp__lean_diagnostic_messages",
          "mcp__lean-lsp__lean_goal",
          "mcp__lean-lsp__lean_local_search",
          "mcp__lean-lsp__lean_multi_attempt",
        ],
      },
    });
  }
  const parsed = parseStageOutput(out);
  if (parsed.status === "blocked-missing-architecture") {
    args.state.flags.missing_architecture = true;
    args.state.flags.missing_architecture_items = parsed.missing_items ?? [];
    // Mirror into the permanent ledger so the gap survives outside this run's state.
    try {
      const items = parsed.missing_items ?? [];
      if (items.length > 0) {
        recordMissingArchitecture(missingArchitectureLedgerPath(args.ctx.repoRoot), {
          qid: args.ctx.qid,
          spec: args.ctx.specialization,
          source: "F2 missing-architecture",
          date: new Date().toISOString().slice(0, 10),
          items: items.map((m) => ({
            kind: m.kind,
            description: [
              `${m.name_suggestion} — ${m.purpose}`,
              m.suggested_location ? `[loc: ${m.suggested_location}]` : "",
            ].filter(Boolean).join(" "),
            effort: undefined,
          })),
        });
      }
    } catch (err) {
      console.warn(`[causalsmith] missing-architecture ledger write failed: ${err instanceof Error ? err.message : String(err)}`);
    }
    return {
      stage: "2",
      status: "blocked",
      advance: false,
      message: parsed.message ?? "MISSING ARCHITECTURE BLOCKED",
      artifacts: parsed.artifacts,
    };
  }
  if (parsed.status !== "completed") {
    // why: F2 must not run the completed state mutation path unless the worker completed.
    return {
      stage: "2",
      status: "blocked",
      advance: false,
      message: parsed.message ?? "F2 did not complete",
      artifacts: parsed.artifacts ?? [],
    };
  }

  // Rewind proof-preservation: re-attach prior proofs for new `sorry` decls whose
  // signature is unchanged. In revise mode, reactivate them immediately so F2
  // cannot return with a working proof downgraded to `sorry`; cold mode retains
  // the historical inert-comment handoff to F2.5/F3. No-op unless real prior
  // proofs existed. Best-effort: a preservation failure must not hide the
  // producer result, but it is surfaced loudly.
  if (priorProofs.size > 0) {
    try {
      const carried = await injectCarryoverComments(paths.leanDir, priorProofs);
      if (carried.count > 0) {
        if (patchInPlace) {
          const restored = await restoreCarryoverProofs(paths.leanDir);
          console.warn(
            `[causalsmith] Stage 2 revise proof preservation: restored ${restored.count} active prior proof(s) ` +
              `for signature-unchanged decl(s) (${restored.names.join(", ")}); only changed/new obligations may remain sorry.`,
          );
        } else {
          console.warn(
            `[causalsmith] Stage 2 proof carry-over: re-attached ${carried.count} prior proof(s) as Stage-3 anchors ` +
              `for signature-unchanged decl(s) (${carried.names.join(", ")}) — rewind did not discard them.`,
          );
        }
      }
    } catch (err) {
      console.warn(
        `[causalsmith] Stage 2 proof carry-over failed (continuing): ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }

  const duplicateNodeAnchors = await findDuplicateLeanNodeAnchors(paths.leanDir);
  if (duplicateNodeAnchors.length > 0) {
    throw new Error(
      "F2 duplicate @node gate failed; every graph node must have exactly one canonical primary declaration:\n" +
        duplicateNodeAnchors
          .map((d) => `  ${d.id}: ${d.locations.join(", ")}`)
          .join("\n"),
    );
  }

  // Paper-scoped: if state.theorems is present, walk the manifest and update
  // each entry. Falls back to legacy single-theorem behavior when absent.
  if (args.state.theorems && args.state.theorems.length > 0) {
    const manifest = (parsed.theorems ?? []).filter((m) => !nonEmittedLocalIds.has(m.theorem_local_id));
    const byLocal = new Map(manifest.map((m) => [m.theorem_local_id, m]));
    const artifactIndex = new Map<string, { decl: string; relpath: string }>();
    const leanArtifacts = (parsed.artifacts ?? []).filter((f) => f.endsWith(".lean"));
    for (const leanFile of leanArtifacts) {
      const leanSource = await readIfExists(leanFile);
      const relpath = path.relative(paths.leanDir, leanFile);
      for (const entry of args.state.theorems) {
        if (artifactIndex.has(entry.theorem_local_id)) continue;
        const recovered = findLeanDeclByLocalId(leanSource, entry.theorem_local_id);
        if (recovered) artifactIndex.set(entry.theorem_local_id, { decl: recovered, relpath });
      }
      for (const m of manifest) {
        if (!m.lean_decl_name || artifactIndex.has(m.theorem_local_id)) continue;
        if (declNameRegex(m.lean_decl_name).test(leanSource)) artifactIndex.set(m.theorem_local_id, { decl: m.lean_decl_name, relpath });
      }
    }
    for (const entry of args.state.theorems) {
      if (nonEmittedLocalIds.has(entry.theorem_local_id)) continue;
      let m = byLocal.get(entry.theorem_local_id);
      let loc = m?.lean_decl_name ? artifactIndex.get(entry.theorem_local_id) : undefined;
      if (!m?.lean_decl_name) {
        const recovered = artifactIndex.get(entry.theorem_local_id);
        if (recovered) {
          console.warn(
            `[causalsmith] Stage 2 manifest dropped ${entry.theorem_local_id} but .lean body has decl ${recovered.decl}; repairing manifest.`,
          );
          m = { theorem_local_id: entry.theorem_local_id, lean_decl_name: recovered.decl };
          loc = recovered;
        }
      }
      if (m?.lean_decl_name && loc) {
        entry.lean_decl_name = m.lean_decl_name;
        entry.lean_file_relpath = loc.relpath; // why: multi-artifact paper scaffolds must point each theorem at the file containing its decl.
        entry.stage_completed = "2";
        entry.status = "in_progress";
      } else {
        entry.status = "stuck";
        entry.failure_reason = "Stage 2 did not produce a Lean declaration for this theorem";
      }
    }
  }
  // After Stage 2 produces sorry-only output successfully, the redirect has been
  // honored. Clear it so Stage 2.5 / Stage 3 see a clean slate for re-review.
  // Do NOT clear `scaffold_redirect_count` — that's the loop guard counter,
  // accumulates over the run.
  if (parsed.status === "completed") {
    args.state.flags.scaffold_redirect = null;
  }
  // Sync-back check. The worker may have updated plan.json on
  // deviation (a planned reuse that did not type-fit; an atom better as a named def);
  // re-run the plan gate against the typed core, now also checking the emitted Lean's
  // @node/@env tags cover the plan one-to-one (P7). Every structural violation blocks the
  // scaffold EXCEPT P5 (reuse existence) and P6 (module resolution) — reuse lookup and
  // module resolution are settled in the later typed phases, so they stay advisory here.
  if (parsed.status === "completed") {
    const corePath = coreJsonPath(args.ctx);
    const coreExists = existsSync(corePath);
    const planExists = existsSync(paths.plan);
    const gateInputsPresent = coreExists && planExists;
    try {
      if (coreExists !== planExists) {
        throw new Error(
          `F2 structural plan gate inputs incomplete (core=${coreExists}, plan=${planExists})`,
        );
      }
      if (gateInputsPresent) {
        const core = CoreSchema.parse(JSON.parse(await readFile(corePath, "utf8")));
        const planObj = JSON.parse(await readFile(paths.plan, "utf8"));
        const leanTags = await parseLeanNodeTags(paths.leanDir);
        const leanDeclNames = new Set((await parseLeanDecls(paths.leanDir, { includeLemmas: true })).map((decl) => decl.name));
        let knownDecls: Set<string> | undefined;
        try {
          const lib = createRetrieval(args.ctx.repoRoot).library;
          if (lib) knownDecls = new Set(lib.entries.map((e) => e.name));
        } catch {
          knownDecls = undefined;
        }
        if (!knownDecls) {
          console.warn(
            "[causalsmith] library index unavailable (doc/library_index.json missing/unreadable) — the P5 reuse-existence check is SKIPPED this pass; hallucinated reuse decls will surface only at compile. Run `lake build && lake exe library_index`.",
          );
        }
        const gate = runPlanGate(planObj, core, { knownDecls, leanTags, leanDeclNames });
        if (!gate.ok) {
          const blockingViolations = blockingPostSyncPlanViolations(gate.violations);
          if (blockingViolations.length > 0) {
            throw new Error(
              `F2 structural plan gate refused the scaffold:\n  ` +
                blockingViolations.map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  "),
            );
          }
          console.warn(
            `[causalsmith] F2 post-sync plan_gate: ${gate.violations.length} violation(s)\n  ` +
              gate.violations.slice(0, 12).map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  "),
          );
        }
      } else {
        console.warn("[causalsmith] F2 post-sync gate skipped: legacy run has neither typed core nor plan");
      }
    } catch (err) {
      if (err instanceof Error && err.message.startsWith("F2 structural plan gate refused")) throw err;
      // The try only throws once at least one input exists (the XOR check, or the gate body under
      // `gateInputsPresent`), so reaching here always means a real execution failure — fail closed.
      throw new Error(
        `F2 structural plan gate failed to execute: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }
  // Graph link (best-effort, advisory): seed `-- @node:` annotations + extract the
  // Lean side into the formalization graph. No gate depends on it yet.
  let hiddenChangedTargets: string[] = [];
  if (patchInPlace) {
    try {
      hiddenChangedTargets = hiddenDefinitionChangeTargets(
        priorSemanticDefs,
        await findStatementSemanticDefs(paths.leanDir),
      );
      if (hiddenChangedTargets.length > 0) {
        console.warn(
          `[causalsmith] Stage 2 revise semantic invalidation: reset cached F2.5 review for ` +
            `${hiddenChangedTargets.join(", ")} (meaning-bearing inline dependency changed).`,
        );
      }
    } catch (err) {
      console.warn(
        `[causalsmith] Stage 2 hidden-definition comparison failed (continuing): ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }
  const invalidateReviewNodeIds = [...new Set([
    ...sourceRewindDirtyTargets,
    ...hiddenChangedTargets,
  ])].sort();
  const graphLink = await linkGraphFromStage2({
    qid: args.ctx.qid,
    spec: args.ctx.specialization,
    formalizationDir: paths.formalizationDir,
    leanDir: paths.leanDir,
    invalidateReviewNodeIds,
  });
  if (graphLink.graph) {
    if (sourceRewindDirtyTargets.length > 0 && args.state.flags.source_rewind?.status === "applied") {
      args.state.flags.source_rewind.status = "f2_revised";
      args.state.flags.source_rewind.f2_revised_at = new Date().toISOString();
      console.warn(
        `[causalsmith] Stage 2 source-rewind invalidation: reset cached F2.5 review for ` +
          `${sourceRewindDirtyTargets.join(", ")}.`,
      );
    }
    const errs = graphLink.findings.filter((f) => f.severity === "error").length;
    console.warn(`[graph] F2 linked ${graphLink.graph.nodes.length} nodes; ${errs} advisory invariant error(s)`);
  }
  // Do not trust the producer's `compiled sorry-only` self-report.  A revised
  // helper can be outside the producer's narrow target even though it is in the
  // run import closure; advancing to F2.5 with a red tree then lets a stale
  // review cache hide the failure.  Production runs have a lakefile at the repo
  // root; isolated unit-test fixtures do not and deliberately skip this gate.
  if (existsSync(path.join(args.ctx.repoRoot, "lakefile.toml"))) {
    const build = await buildRunModules(args.ctx.repoRoot, paths.leanDir);
    if (!build.ok) {
      throw new Error(`F2 run compile gate failed; refusing to advance to F2.5:\n${build.errors}`);
    }
    console.warn("[causalsmith] F2 run compile gate passed");
  }
  return {
    stage: "2",
    status: "completed",
    message: parsed.message ?? "Stage 2 Lean scaffold completed",
    artifacts: parsed.artifacts ?? [paths.leanDir],
  };
}
