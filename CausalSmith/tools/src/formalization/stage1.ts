// Discovery Stage 1 (F1) — the FORMALIZATION PLANNER.
//
// The D0 typed core (`<qid>_core.json`) is the machine-readable structural source
// of truth (symbols, atomic assumptions, class/construction definitions, statements,
// dep-DAG). F1 no longer re-extracts structure from the prose .tex: it authors the
// per-node formalization PLAN (`<qid>_<spec>_plan.json`) that maps every core node +
// ambient world to a Lean object, maximizing reuse of Causalean substrate. F2 then
// implements that plan. See CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md.

import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import { MODEL_PLAN } from "../constants.js";
import type { Intervention, ReviewResult } from "../judgment.js";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  clusterFromLeanSubdir,
  correctionBlock,
  parseStageOutput,
  recordGateNodes,
  readPrompt,
  readRequired,
  type StageDeps,
} from "../pipeline_support.js";
import { interventionBlock } from "../shared/intervention_routing.js";
import { writeLeanLspMcpConfig } from "../workers/claude.js";
import { dispatchClaudeAgent } from "../framework/agent_dispatch.js";
import { buildGraphFromMd } from "../graph/from_note.js";
import { buildGraphFromCorePlan } from "../graph/from_core.js";
import { renderBridgeNote } from "../graph/render_note.js";
import { graphPath, saveGraph } from "../graph/store.js";
import {
  recordMissingArchitecture,
  missingArchitectureLedgerPath,
} from "../shared/missing_architecture_ledger.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { CoreSchema, type Core } from "../discovery/core/schema.js";
import { runPlanGate } from "../formalization/plan/plan_gate.js";
import { PlanSchema, deriveFeasibility } from "../formalization/plan/schema.js";
import { createRetrieval } from "../formalization/reuse_retrieval.js";
import { coreReuseCandidateBlock } from "../formalization/reuse_render.js";
import { laterStageEverRan } from "../shared/resume_mode.js";

/** Copy D0.5's verified cited source-of-record into the F1 plan in place. */
export function copyVerifiedCitedSourcesToPlan(planObj: unknown, core: Core): number {
  if (!planObj || typeof planObj !== "object") return 0;
  const pj = planObj as {
    nodes?: Record<string, { source?: string }>;
    citations?: Array<Record<string, unknown> & { id?: string }>;
  };
  let copied = 0;
  for (const s of core.statements.filter((x) => x.status === "cited")) {
    const citeId = pj.nodes?.[s.id]?.source;
    const citation = citeId && pj.citations?.find((c) => c.id === citeId);
    if (!citation || !s.source) continue;
    citation.locator = s.source.locator;
    const verbatim = s.source.verbatim_statement ?? s.proof_tex?.trim() ?? undefined;
    if (verbatim) citation.verbatim_statement = verbatim;
    if (s.source.arxiv) citation.arxiv = s.source.arxiv;
    if (s.source.doi) citation.doi = s.source.doi;
    if (s.source.url) citation.url = s.source.url;
    if (s.source.attestation) citation.attestation = s.source.attestation;
    copied++;
  }
  return copied;
}

/** Legacy helper: build the formalization graph from an F1 .md and persist it.
 *  Retained as a standalone export (a test exercises it directly); F1 no longer
 *  calls it — graph emission migrates to a core+plan source in Phase 5. */
export async function emitGraphFromStage1(a: {
  qid: string;
  spec: string;
  formalizationDir: string;
  mdPath: string;
}): Promise<void> {
  try {
    if (!existsSync(a.mdPath)) return;
    const g = await buildGraphFromMd(a.qid, a.spec, a.mdPath);
    await saveGraph(graphPath(a.formalizationDir, a.qid, a.spec), g);
  } catch (err) {
    console.warn(`[graph] F1 emission skipped: ${err instanceof Error ? err.message : String(err)}`);
  }
}

/** True when the plan has a statement node realizing this `theorem_local_id`
 *  (the rescue for a manifest that dropped a theorem the plan actually covers). */
function planCoversLocalId(planObj: unknown, localId: string): boolean {
  const r = PlanSchema.safeParse(planObj);
  if (!r.success) return false;
  return Object.values(r.data.nodes).some((n) =>
    n.local_id === localId && !n.gate && (n.lean_kind === "theorem" || n.lean_kind === "lemma")
  );
}

export async function runStage1(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  priorReview?: ReviewResult | null;
  intervention?: Intervention | null;
  attempt?: number;
}): Promise<StageResult> {
  const paths = artifactPaths(args.ctx, args.state);
  const corePath = coreJsonPath(args.ctx);
  // The typed core is the structural input and is REQUIRED: D0 always emits it, so
  // absence is a fault (a plan authored from prose alone silently loses the
  // structural ground truth — the existsSync?degrade class from the D-stage hardening).
  const coreText = await readRequired(corePath, "F1 planning");
  let core: Core;
  try {
    core = CoreSchema.parse(JSON.parse(coreText));
  } catch (err) {
    throw new Error(
      `F1 planning: core.json at ${corePath} failed to parse/validate: ${err instanceof Error ? err.message : String(err)} (legacy pre-typed-core run? re-run discovery (D0) to regenerate core.json)`,
    );
  }

  // REVISE MODE (token-saver, drift-guard). F1 re-runs on two paths: the F1.5
  // boundary loop (carries `priorReview`) and a cross-stage fix-locus rewind from
  // F2.5 (carries no priorReview, but the critique was parked on
  // `flags.f1_revise_directive`). In either case the prior plan is on disk and only
  // the flagged nodes need to change — point the worker at it and Edit in place.
  const f1Directive = args.state.flags.f1_revise_directive ?? null;
  // SUBSTRATE-BUILT channel (build→F1): decls the orchestrator built since the last
  // F1 run, to discharge the matching gate nodes against (see the discharge directive
  // block below). A substrate-built rerun is a PATCH (only the discharged gates + their
  // closure change) — preserve the rest of the plan, exactly like an F1.5/F2.5 revise.
  const builtDecls = args.state.flags.substrate_built ?? [];
  const hasLaterStageHistory = await laterStageEverRan(args.ctx, args.state, "1");
  const isRevise =
    args.priorReview?.status === "revise" ||
    !!f1Directive ||
    builtDecls.length > 0 ||
    hasLaterStageHistory;
  let reviseBlock = "";
  if (isRevise && existsSync(paths.plan)) {
    reviseBlock = [
      await readPrompt(args.ctx, "stage1_head_revise.txt"),
      "",
      f1Directive
        ? `UPSTREAM DIRECTIVE (F2.5 fix-locus triage — the Lean scaffolder rooted the defect in the FORMALIZATION PLAN, not the Lean. Fix the plan so the scaffold can succeed):\n${f1Directive}\n`
        : "",
      builtDecls.length > 0
        ? "SUBSTRATE-BUILT rerun: PATCH the plan — edit ONLY the discharged gate node(s) named in the SUBSTRATE-BUILT block below and their dependency closure (consumers that referenced them as hyps). Leave every other node entry intact.\n"
        : "",
      `Prior plan to patch (Read, then Edit in place): ${paths.plan}`,
      "",
    ].filter(Boolean).join("\n");
  }

  const cluster = clusterFromLeanSubdir(args.state.lean_subdir) ?? core.cluster ?? null;
  const reuseBlock = coreReuseCandidateBlock(args.ctx.repoRoot, core, cluster, {
    // Semantic blend ON by default: pure-lexical ranking surfaced surface-token matches
    // (e.g. a Le Cam TV bound for `clip-bias`) over the concept-correct PO/Estimation
    // decls; the semantic tier re-ranks the right candidate up. Degrades to lexical-only
    // if embeddings are missing/stale. Set RETRIEVAL_SEMANTIC_PUSH=off to force lexical.
    semantic: process.env.RETRIEVAL_SEMANTIC_PUSH !== "off",
  });

  // SUBSTRATE-BUILT channel (build→F1): if the orchestrator built a Defer-item's
  // crux substrate since the last F1 run, it left the new decl(s) on
  // `flags.substrate_built` (read into `builtDecls` above). Inject them as a discharge
  // directive so this rerun un-defers/un-assumes the matching gate node(s).
  const substrateBuiltBlock = builtDecls.length
    ? [
        "=== SUBSTRATE-BUILT (discharge directive — these gates are now PROVEN upstream) ===",
        "The meta-orchestrator has BUILT the following substrate 0-sorry in Causalean.",
        "For EACH listed gate node you MUST now DISCHARGE it (not re-defer, not re-assume):",
        "set `lean_kind:\"lemma\"`, `disposition:\"reuse\"`, `reuse` = the decl's fully-qualified",
        "name, `module` = its module, DROP it from every statement's `hyps`, and set",
        "`defer_tier:false`. Confirm the decl's NL statement type-fits the node before reuse.",
        ...builtDecls.map(
          (d) =>
            `  - gate ${d.gate_id} → reuse ${d.decl_name} (module ${d.module}) : ${d.nl_statement}`,
        ),
        "",
      ].join("\n")
    : "";

  const prompt = [
    correctionBlock(args.priorReview ?? null, args.attempt ?? 1, {
      manifestContract: (args.state.theorems?.length ?? 0) > 0,
    }),
    substrateBuiltBlock,
    reviseBlock,
    interventionBlock(args.intervention),
    await readPrompt(args.ctx, "stage1_template.txt"),
    "",
    baseBrief(args.ctx, args.state),
    "",
    `Typed core JSON (the structural source of truth — map EVERY node; do NOT re-derive structure from prose):\n${coreText}`,
    "",
    reuseBlock,
    "",
    isRevise && existsSync(paths.plan)
      ? `Patch the existing plan at ${paths.plan} per REVISE MODE above — Edit every node entry AFFECTED by the correction (the flagged nodes AND their dependency closure), leave the rest intact (do NOT blind-regenerate).`
      : `Write the formalization plan JSON to ${paths.plan}.`,
    "Return only the JSON object specified in the prompt's `=== OUTPUT JSON ===` block.",
  ].join("\n");

  const out = await dispatchClaudeAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "1",
    label: "F1 plan author",
    promptSources: ["stage1_template.txt", ...(isRevise ? ["stage1_head_revise.txt"] : []), corePath],
    input: {
      prompt,
      model: MODEL_PLAN.stage1.model,
      cwd: args.ctx.repoRoot,
      mcpConfigPath: writeLeanLspMcpConfig(args.ctx.repoRoot),
      allowedTools: [
        "Read", "Write", "Edit", "Grep", "Glob",
        // Substrate survey for the per-node reuse decisions.
        "mcp__lean-lsp__lean_leansearch",
        "mcp__lean-lsp__lean_loogle",
        "mcp__lean-lsp__lean_local_search",
        "mcp__lean-lsp__lean_hover_info",
        "mcp__lean-lsp__lean_file_outline",
      ],
    },
  });
  const parsed = parseStageOutput(out);
  if (parsed.status === "parse_failed") {
    // AUDIT-A: fail closed on unparseable stage output; why: F1 must not advance on garbage.
    throw new Error("Stage 1: F1 worker output did not parse (parse_failed) - refusing to advance on unparseable output");
  }
  const p = parsed as Record<string, unknown>;

  // Read the just-written plan (if any) and run the deterministic gate as a
  // best-effort self-check — log violations. The F1.5 boundary enforces them as a
  // pre-review lint with producer retry (Phase 3); F1 never blocks on the gate.
  let planObj: unknown = null;
  if (existsSync(paths.plan)) {
    try {
      planObj = JSON.parse(await readFile(paths.plan, "utf8"));
    } catch (err) {
      console.warn(`[causalsmith] F1 wrote an unparseable plan at ${paths.plan}: ${err instanceof Error ? err.message : String(err)}`);
    }
  }
  // D0.5 has already source-matched every status:"cited" node. F1 must COPY
  // that verified source of record, not ask the planner to reconstruct theorem
  // text from prose. Apply it deterministically through the cited node's cite:
  // alias. Legacy cores may store the attested transcription in proof_tex.
  if (planObj && typeof planObj === "object") {
    const copied = copyVerifiedCitedSourcesToPlan(planObj, core);
    if (copied > 0) {
      await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
      console.warn(`[causalsmith] F1 copied ${copied} D0.5-verified cited source-of-record entr${copied === 1 ? "y" : "ies"} into the plan.`);
    }
  }
  // DETERMINISTIC discharge application (substrate-built channel). The channel is an
  // orchestrator→pipeline directive: the orchestrator BUILT these decls and knows the
  // exact discharge. Rather than rely on F1's (unreliable) LLM patch, APPLY the discharge
  // mechanically so the plan is always consistent — `lean_kind:"lemma"`, `disposition:
  // "reuse"`, the reuse decl + module, `defer_tier:false`, and dropped from every
  // statement's `hyps`. (F1 still authors everything else; this is bookkeeping the
  // channel fully determines.)
  if (builtDecls.length && planObj && typeof planObj === "object") {
    const pj = planObj as { nodes?: Record<string, Record<string, unknown>> };
    if (pj.nodes) {
      for (const d of builtDecls) {
        const node = pj.nodes[d.gate_id];
        if (node) {
          node.lean_kind = "lemma";
          node.disposition = "reuse";
          node.reuse = d.decl_name;
          const mods = Array.isArray(node.modules) ? (node.modules as string[]) : [];
          node.modules = mods.includes(d.module) ? mods : [...mods, d.module];
          node.defer_tier = false;
        }
        // Drop the discharged gate from every node's `hyps` (it is a proved lemma now).
        for (const n of Object.values(pj.nodes)) {
          if (Array.isArray(n.hyps)) n.hyps = (n.hyps as string[]).filter((h) => h !== d.gate_id);
        }
      }
      await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
      console.warn(`[causalsmith] substrate-built: deterministically discharged ${builtDecls.map((d) => d.gate_id).join(", ")} in the plan.`);
    }
  }
  let derivedFeasibility: "formalizable-now" | "needs-new-infrastructure" | null = null;
  let planGateOk = true;
  const parsedPlan = planObj ? PlanSchema.safeParse(planObj) : null;
  if (planObj) {
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
    const gate = runPlanGate(planObj, core, { knownDecls });
    planGateOk = gate.ok;
    if (!gate.ok) {
      console.warn(
        `[causalsmith] F1 plan_gate: ${gate.violations.length} violation(s)\n  ` +
          gate.violations.slice(0, 12).map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  "),
      );
    }
    if (parsedPlan?.success) derivedFeasibility = deriveFeasibility(parsedPlan.data);
  }
  // Judge cleanliness by the SAME gate run F1.5's prelint will apply (with knownDecls) — a
  // second knownDecls-less run here would clear the retry directives on a plan the boundary
  // is about to bounce for reuse-existence violations.
  const planGateClean =
    parsed.status === "completed" &&
    !!parsedPlan?.success &&
    planGateOk;
  if (planGateClean) {
    // why: keep retry directives until F1 completed with a parsed, gate-clean plan.
    if (f1Directive) args.state.flags.f1_revise_directive = null;
    if (builtDecls.length) args.state.flags.substrate_built = null;
  }

  // Emit the formalization graph from core + plan (the graph is the interchange the
  // F3/F4 proof loop refreshes off — without it the loop has no graph to refresh).
  // Best-effort: never blocks the stage.
  try {
    const g = buildGraphFromCorePlan(core, args.ctx.specialization, parsedPlan?.success ? parsedPlan.data : null);
    await saveGraph(graphPath(paths.formalizationDir, args.ctx.qid, args.ctx.specialization), g);
    // Bridge .md: the banked human record + causalsmith input + F5 premise-check
    // source, rendered deterministically from the graph (parseNoteBlocks-compatible).
    await writeFile(paths.md, renderBridgeNote(g), "utf8");
  } catch (err) {
    console.warn(`[graph] F1 core+plan emission skipped: ${err instanceof Error ? err.message : String(err)}`);
  }

  // Feasibility is DERIVED from the plan (Defer-tier nodes ⇒ needs-new-infrastructure);
  // fall back to a worker-reported verdict only when no plan was parsed (legacy path).
  const infra = p.infrastructure_needed;
  const feasibility =
    derivedFeasibility ?? (typeof p.feasibility_verdict === "string" ? p.feasibility_verdict : null);
  let infraItems: Array<Record<string, unknown>> = Array.isArray(infra) ? (infra as Array<Record<string, unknown>>) : [];
  // If the plan derives needs-new-infrastructure but the worker JSON listed no
  // items, synthesize the ledger items from the Defer-tier plan nodes.
  if (feasibility === "needs-new-infrastructure" && infraItems.length === 0 && parsedPlan?.success) {
    infraItems = Object.entries(parsedPlan.data.nodes)
      .filter(([, n]) => n.defer_tier)
      .map(([id, n]) => ({ id, kind: n.lean_kind, description: n.notes ?? "", effort: "medium" }));
  }
  const gateIds = new Set(
    parsedPlan?.success
      ? Object.entries(parsedPlan.data.nodes).filter(([, n]) => n.gate).map(([id]) => id)
      : [],
  );
  const gateNames = new Set(
    parsedPlan?.success
      ? Object.values(parsedPlan.data.nodes).filter((n) => n.gate).map((n) => n.lean_name)
      : [],
  );
  if (parsedPlan?.success && gateIds.size > 0) {
    try {
      const coreNl = new Map<string, string>();
      if (core) {
        for (const a of core.assumptions) coreNl.set(a.id, a.condition);
        for (const d of core.definitions) coreNl.set(d.id, d.construction);
        for (const s of core.statements) coreNl.set(s.id, s.statement);
      }
      const citById = new Map(parsedPlan.data.citations.map((c) => [c.id, c] as const));
      const gateRows = Object.entries(parsedPlan.data.nodes)
        .filter(([, n]) => n.gate)
        .map(([id, n]) => {
          const matchingInfra = infraItems.find((it) =>
            String(it.id ?? "") === id ||
            String(it.id ?? "") === n.lean_name ||
            String(it.description ?? "").includes(id) ||
            String(it.description ?? "").includes(n.lean_name)
          );
          const cls = n.gate_class === "cited" ? ("cited" as const) : undefined;
          const cit = n.source ? citById.get(n.source) : undefined;
          const handle = cit?.arxiv ? `arXiv:${cit.arxiv}` : (cit?.doi ?? cit?.url);
          return {
            name: n.lean_name,
            statement: coreNl.get(id) ?? n.notes ?? id,
            classical_fact: cit
              ? `${cit.authors} (${cit.year}) — ${cit.title}`
              : String(matchingInfra?.kind ?? "substrate-gate"),
            missing_infra: String(matchingInfra?.description ?? n.notes ?? "F1 substrate-gate plan node"),
            gate_class: cls,
            source: cls === "cited" && cit
              ? { cite_id: cit.id, locator: cit.locator, url: handle }
              : undefined,
          };
        });
      await recordGateNodes(args.ctx, gateRows);
    } catch (err) {
      console.warn(`[causalsmith] substrate-debt gate ledger write failed: ${err instanceof Error ? err.message : String(err)}`);
    }
  }
  const blockingInfraItems = infraItems.filter((it) => {
    const id = String(it.id ?? "");
    const description = String(it.description ?? "");
    return !gateIds.has(id) &&
      !gateNames.has(id) &&
      ![...gateIds].some((gateId) => description.includes(gateId)) &&
      ![...gateNames].some((gateName) => description.includes(gateName));
  });
  const needsSubstrate = feasibility === "needs-new-infrastructure" && blockingInfraItems.length > 0;

  if (needsSubstrate) {
    try {
      recordMissingArchitecture(missingArchitectureLedgerPath(args.ctx.repoRoot), {
        qid: args.ctx.qid,
        spec: args.ctx.specialization,
        source: "F1 needs-new-infrastructure",
        date: new Date().toISOString().slice(0, 10),
        items: blockingInfraItems.map((it) => ({
          id: typeof it.id === "string" ? it.id : undefined,
          kind: String(it.kind ?? "unknown"),
          description: String(it.description ?? ""),
          effort: typeof it.effort === "string" ? it.effort : undefined,
        })),
        deferred: typeof p.deferred_conjecture === "string" ? p.deferred_conjecture : undefined,
      });
    } catch (err) {
      console.warn(`[causalsmith] missing-architecture ledger write failed: ${err instanceof Error ? err.message : String(err)}`);
    }
    // Substrate-build halt: hand control to the orchestrator so it can dispatch
    // background builders for the Defer-items. It then clears this flag and
    // resumes — F2 scaffolds against the assumed gate; each landed build is
    // discharged later by codex wiring the lemma into the Lean + a rewind to
    // F2.5 to re-review (NOT a rewind to F1). A naive `--resume` is refused
    // (resolveResumeGates) until the flag is dealt with.
    const itemSummary = blockingInfraItems
      .map((it) => `${String(it.id ?? "?")} [${String(it.kind ?? "?")}/${String(it.effort ?? "?")}]: ${String(it.description ?? "").slice(0, 120)}`)
      .join("\n  - ");
    const deferredLine =
      typeof p.deferred_conjecture === "string" && p.deferred_conjecture.trim()
        ? `\nDeferred consumer: ${p.deferred_conjecture.trim()}`
        : "";
    args.state.flags.substrate_build_required =
      `F1 verdict=needs-new-infrastructure. Dispatch a BACKGROUND builder subagent for EACH Defer-item (minimal-but-reusable, capped+isolated, codex-fills-the-proof), then CLEAR flags.substrate_build_required and resume so the run proceeds with the gates assumed (do NOT block). Discharge each landed build at the next checkpoint: codex wires the lemma into the Lean (replacing the assumed gate) and rewind to F2.5 to re-review (NOT F1; plan/scaffold unchanged), re-passing F4 before banking. A gate that cannot be built sorry-free stays honest substrate-debt (→ SUBSTRATE_DEBT.md).\nDefer-items:\n  - ${itemSummary}${deferredLine}`;
  } else if (args.state.flags.substrate_build_required) {
    // A rerun-F1 (after the orchestrator built the crux substrate) produced a plan
    // with no remaining Defer-item: clear the stale gate so `--resume` proceeds.
    args.state.flags.substrate_build_required = null;
  }

  // Paper-scoped: walk the theorem manifest. A theorem is covered if the worker's
  // `theorems[]` manifest lists it OR (rescue) the plan has a statement node whose
  // `local_id` realizes it. Falls back to legacy single-theorem behavior when absent.
  if (args.state.theorems && args.state.theorems.length > 0) {
    const manifest = parsed.theorems ?? [];
    const covered = new Set(manifest.map((m) => m.theorem_local_id));
    for (const entry of args.state.theorems) {
      if (entry.status === "failed" || entry.status === "stuck") continue;
      if (covered.has(entry.theorem_local_id)) {
        entry.stage_completed = "1";
      } else if (planObj && planCoversLocalId(planObj, entry.theorem_local_id)) {
        console.warn(
          `[causalsmith] Stage 1 manifest dropped ${entry.theorem_local_id} but the plan covers it; repairing manifest.`,
        );
        entry.stage_completed = "1";
      } else {
        entry.status = "stuck";
        entry.failure_reason = "Stage 1 did not produce an NL block for this theorem";
      }
    }
  }

  // The plan-audit checkpoint (CKPT 1) moved DOWNSTREAM to F1.5: when F1 produced
  // a usable plan it advances STRAIGHT into the F1.5 reuse-soundness review, so
  // F1 + F1.5 halt together at ONE consolidated CKPT 1 (fewer recall events for
  // the orchestrator). F1 still halts on its own in two cases: (a) the
  // substrate-build gate — hand control to the orchestrator to dispatch
  // background builders for the Defer-items (it then clears the flag and
  // proceeds gated; landed builds discharge later); (b) no usable plan was
  // parsed (blocked-infeasible / parse failure) — there is nothing for F1.5 to
  // review, so surface the artifact to the human now.
  if (needsSubstrate) {
    return {
      stage: "1",
      status: "checkpoint",
      message: `SUBSTRATE-BUILD CHECKPOINT: F1 flagged needs-new-infrastructure — dispatch background builders for the Defer-items, then clear the flag and resume to proceed gated (discharge at the next checkpoint). ${args.state.flags.substrate_build_required ?? ""}`.slice(0, 1200),
      artifacts: parsed.artifacts ?? [paths.plan],
    };
  }
  if (!parsedPlan?.success) {
    return {
      stage: "1",
      status: "checkpoint",
      message: parsed.message ?? "F1 produced no usable plan; inspect the artifact before resume.",
      artifacts: parsed.artifacts ?? [paths.plan],
    };
  }
  return {
    stage: "1",
    status: "completed",
    message: parsed.message ?? "F1 plan authored; advancing to F1.5 reuse-soundness review (consolidated CKPT 1).",
    artifacts: parsed.artifacts ?? [paths.plan],
  };
}
