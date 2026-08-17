// Stage 0.R (core revise) — the in-place editor of the typed core.
//
// D0.R holds the core + the D0.5 findings and edits the CORE in place (directed
// floor + holistic freedom). It edits only core.json. The source preview remains
// the last authoritative D0 render while the edit is provisional; the caller
// publishes a fresh preview only after the complete D0.5 gate passes. The edit
// is bounded by the structural gate, which must re-pass with full discharge.
// Prompt derived from stage0_directed + stage0_salvage.
import { existsSync } from "node:fs";
import { readFile, writeFile, appendFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import {
  discoveryBrief,
  parseStageOutput,
  readPrompt,
  type StageDeps,
} from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { resolveInDir } from "../../paths.js";
import { coreJsonPath } from "./d0_core.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import { CoreSchema, type Core } from "../core/schema.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairCoreLatexSerialization,
} from "../core/latex_serialization.js";
import { loadPaperView, logPaperView } from "../core/paper_view.js";
import { diffCoreProse, type ProseUpdates } from "../core/assemble.js";
import { runGates } from "../framework/gates.js";
import { structuralGate } from "../framework/gate_registrations.js";
import { normalizeTexWhitespace } from "../../shared/tex_text.js";
import type { Stage0_5CoreResult } from "./d0_5_core.js";

export interface Stage0RCoreResult {
  message: string;
  coreJsonPath: string;
  /** Prose-only delta produced by this provisional edit. The caller promotes it
   *  only after the next panel clears every finding this edit was asked to fix. */
  proseUpdates?: ProseUpdates;
  /** Set when D0.R determines a finding cannot be fixed by an in-place edit (it needs
   *  real math / a re-derivation / new substrate, or would force weakening the result).
   *  The typed D0.5 loop turns this into an immediate checkpoint — escalate BEFORE the
   *  revise cap rather than thrashing or crashing. */
  escalate?: { reason: string };
}

const TOPIC_MISMATCH_CODES = [
  "kernel-substituted",
  "direction-only",
  "constructive-object-missing",
] as const;

export interface ProposalFindingRoute {
  labels: string[];
  action: string;
}

/** Findings whose comparison surface lives in durable pipeline state, outside
 * D0.R's core.json edit capability. Exported so the caller can route them before
 * charging an edit round; runStage0RCore repeats the check as a direct-call guard. */
export function proposalFindingRoute(review: Stage0_5CoreResult): ProposalFindingRoute | null {
  const routed = review.verdicts.filter((verdict) => verdict.referee === "decision")
    .flatMap((verdict) => verdict.findings)
    .map((finding) => {
      const raw = String(finding.code ?? "").toLowerCase().replaceAll("_", "-");
      const code = raw.startsWith("novelty-") ? raw.slice("novelty-".length) : raw;
      return { finding, code };
    })
    .filter(({ code }) =>
      TOPIC_MISMATCH_CODES.some((known) => code === known) ||
      code === "assumption-omitted" ||
      code === "proposal-drift" ||
      code === "tier-genuinely-below"
    );
  if (routed.length === 0) return null;

  const actions = new Set<string>();
  if (routed.some(({ code }) => TOPIC_MISMATCH_CODES.some((known) => code === known))) {
    actions.add(
      "either re-derive the promised object or audit and apply the guarded state.proposed_from.topic update",
    );
  }
  if (routed.some(({ code }) => code === "assumption-omitted")) {
    actions.add("repair the theorem statement/premise and re-derive it through the proto");
  }
  if (routed.some(({ code }) => code === "proposal-drift")) {
    actions.add("rewind D-1.2 and redraft/re-anchor the proposal; a topic-only narrowing is not sufficient");
  }
  if (routed.some(({ code }) => code === "tier-genuinely-below")) {
    actions.add("make the novelty-floor/downgrade decision or re-anchor; the delivered kernel already matches the proposal");
  }
  return {
    labels: routed.map(({ finding }) => `${finding.code}@${finding.node_id}`),
    action: [...actions].join("; "),
  };
}

export async function runStage0RCore(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  review: Stage0_5CoreResult;
}): Promise<Stage0RCoreResult> {
  const corePath = coreJsonPath(args.ctx);
  if (!existsSync(corePath)) throw new Error(`Stage 0.R requires a core at ${corePath}`);

  // Edit the SHARED paper view, not raw core.json. The findings this stage must fix
  // were written by the D0.5 panel against the overlaid render; loading the raw core
  // here would hand D0.R stale/empty proof_tex for exactly the nodes whose proofs are
  // provisional — it would "fix" a proof it cannot see, and the divergence would
  // propagate into the protected-statement diff and the escalation decision below.
  const view = await loadPaperView(args.ctx, { corePath });
  logPaperView(view, "D0.R");
  const core = view.core;
  const restoreProtectedCore = async (): Promise<void> => {
    await writeJsonAtomic(corePath, core);
  };
  const preStatementText = new Map(
    core.statements
      .filter((s) => /^(thm|prop|lem):/.test(s.id) && s.kind !== "openendedquestion")
      .map((s) => [s.id, s.statement] as const),
  );
  const findings = args.review.verdicts.flatMap((v) =>
    v.findings.map((f) => ({ referee: v.referee, ...f })),
  );

  // Proposal-promise findings compare the delivered core with the durable topic
  // injected by `discoveryBrief(state.proposed_from.topic)`. D0.R can edit only
  // core.json, so a prose rewrite cannot change that comparison surface: it buys a
  // full model call, then the same finding returns (or a whack-a-mole checkpoint
  // rolls the provisional edit back). Route these directly to the orchestrator,
  // which must choose between substantive re-derivation and the guarded audited
  // topic-update command. Never silently narrow the topic merely to clear review.
  const proposalRoute = proposalFindingRoute(args.review);
  if (proposalRoute) {
    const labels = proposalRoute.labels.join(", ");
    return {
      message: `Stage 0.R escalated proposal-promise mismatch: ${labels}`,
      coreJsonPath: corePath,
      escalate: {
        reason:
          `proposal-promise mismatch (${labels}) is outside D0.R core-edit scope because ` +
          `the relevant proposal/statement state is durable outside core.json; ${proposalRoute.action}`,
      },
    };
  }

  const prompt = [
    await readPrompt(args.ctx, "stage0_R_core.txt"),
    "",
    discoveryBrief(args.ctx, args.state),
    "",
    "=== CURRENT CORE (edit in place) ===",
    JSON.stringify(core, null, 2),
    "",
    "=== D0.5 FINDINGS (the directed floor — every one is must-fix) ===",
    JSON.stringify(findings, null, 2),
    "",
    `CORE_FILE: ${corePath}`,
    "YOUR EDIT SCOPE is the whole CORE EXCEPT a node's STATEMENT/CONCLUSION (the asserted claim). You have FULL freedom over the proof DAG and wiring: `depends_on` edges — ADD a dependency the proof actually uses, DROP a redundant/unused one, re-route edges; added lemmas (incl. classical-source citation-lemmas and derived glue); `proof_tex`; the prose fields; AND — when a finding's honest fix requires it — provisional assumption/DEFINITION alignment (incl. the model class def:law-class, APPLIED PROVISIONALLY + recorded pending-approval, vetted by the orchestrator + next D0.5). MAKE dependency-graph / wiring / redundant-assumption-declaration / faithful def-alignment fixes DIRECTLY — never escalate one of those; they are exactly what you own and they land durably (a passed D0.5 advances without a re-solve).",
    "HARD LIMIT — you MUST NOT change any THEOREM/PROPOSITION/LEMMA STATEMENT or its CONCLUSION: what it asserts, its target object/type, its quantifiers, or its premise-strength. A statement-level finding — ill-typed target, overclaim/positioning, a claim needing narrowing or restating — is NOT yours to fix: a core-JSON statement edit is DISCARDED when the orchestrator re-solves from the proto, so statement changes must land in the proto, which the ORCHESTRATOR owns. Escalate those (do not burn a round editing a statement in place).",
    "DIRECTION-OF-TRUTH on any def/assumption change (the laundering guard): only ALIGN (bring the class/assumption into agreement with what the proofs already use — e.g. add a law-side condition that BOTH sides' objects satisfy, so the converse and the achievability quantify over the SAME class), CORRECT a mis-specified constructed-object formula, or DISCHARGE a dischargeable premise. NEVER NARROW a class to a subclass to force a proof through, never add a hypothesis that assumes the crux or buys a rate — that is laundering and will be rejected. When you ALIGN the class by adding a condition, you MUST re-prove the converse witness / construction still lies in the changed class (update its membership lemma); if it does not, the alignment is invalid — escalate instead.",
    "ESCALATE (status:failed) for a finding whose honest fix needs GENUINELY NEW MATH / substrate the proposal cannot support, OR that requires changing a node's STATEMENT/CONCLUSION (the orchestrator owns statement changes via the proto — see the HARD LIMIT above). Both need an orchestrator rewind. Do NOT escalate — and do NOT burn a round thrashing on — a graph-dependency / wiring / redundant-assumption-declaration / faithful def-alignment fix; make it in place.",
    'Return only JSON on stdout: EITHER {"status":"completed","message":"...","artifacts":["<core.json>"]} when you resolved EVERY finding (by a core edit and/or a faithful provisional def/assumption change), OR {"status":"failed","message":"<list each finding outside in-place core-edit scope>"} to ESCALATE. Use "failed" for a true new-math/statement gap or a durable proposal-topic mismatch — not for a graph, wiring, redundant-assumption-declaration, or faithful def/assumption change you can make directly.',
  ].join("\n");

  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "0.5",
    label: "D0.R directed revise",
    prompt,
    promptSources: ["prompts/D0.5/stage0_R (inline)", "core.json", "findings"],
    model: MODEL_PLAN.mechanicalTier.model,
    reasoningEffort: MODEL_PLAN.mechanicalTier.effort,
    inactivityTimeoutMs: 25 * 60 * 1000,
  });
  // Persist D0.R's raw output + the findings it was handed, appended per round — the only
  // record of what the directed reviser actually did/said (the loop overwrites the core each
  // round). Lets the orchestrator audit whether D0.R fixed, missed, or introduced a finding.
  try {
    const rec = {
      findings_in: findings.map((f) => `${f.code ?? "?"}@${(f as { node_id?: string }).node_id ?? "?"}`),
      stdout: out.stdout,
    };
    await appendFile(
      resolveInDir(path.dirname(corePath), "d0r_raw.jsonl", [`${args.ctx.qid}_d0r_raw.jsonl`]),
      JSON.stringify(rec) + "\n",
      "utf8",
    );
  } catch {
    /* best-effort instrumentation; never block the revise on it */
  }
  const parsedOut = parseStageOutput(out.stdout);
  if (parsedOut.status === "parse_failed") {
    // AUDIT-A: fail closed on unparseable stage output; why: D0.R must not advance on garbage.
    throw new Error("Stage 0.R: D0.R worker output did not parse (parse_failed) - refusing to advance on unparseable output");
  }
  if (parsedOut.status === "failed") {
    // D0.R judged the findings un-fixable in place — escalate gracefully (no throw,
    // no further looping). The loop checkpoints to the orchestrator.
    //
    // Restore first. This was the ONLY escalate path that did not — every other one
    // (gate re-check, protected-statement drift, pending-changes) calls it. The worker
    // edits core.json IN PLACE and may have written it before returning "failed", which
    // would leave core.json mutated and writeup.tex rendered from the pre-edit core: a
    // split-brain across exactly the two artifacts the next reviewer reads. Containment
    // previously depended entirely on the caller's `finally` — correct, but fragile to
    // rely on from here.
    await restoreProtectedCore();
    return {
      message: `Stage 0.R escalated: ${parsedOut.message ?? "(no message)"}`,
      coreJsonPath: corePath,
      escalate: { reason: parsedOut.message ?? "findings not fixable by an in-place edit" },
    };
  }

  // Re-check the edited core: the gate must re-pass (this is what makes holistic
  // freedom safe), with full discharge required. A gate failure here means the in-place
  // edit could not produce a discharged core — escalate rather than throw (the loop
  // surfaces it as a checkpoint for the orchestrator, BEFORE the revise cap).
  //
  // The worker edits core.json IN PLACE and downstream stages re-read those exact
  // bytes, so this is a model boundary: normalize under-escaped TeX backslashes
  // pre-parse, repair post-parse, reject any surviving control character, and
  // persist the canonical form (preserving non-schema keys). An unrecoverable
  // corruption restores the protected core and escalates like every other
  // failed-revise path.
  let edited: Core;
  try {
    edited = CoreSchema.parse(JSON.parse(normalizeRawModelJson(await readFile(corePath, "utf8"))));
    repairCoreLatexSerialization(edited);
    assertNoDecodedControlChars(edited, "Stage 0.R edited core");
    // Persist ONLY the schema-shaped core (core.json carries no sanctioned
    // non-schema keys, and a raw spread would let the worker persist arbitrary
    // extra keys into the artifact downstream prompts inline verbatim).
    await writeJsonAtomic(corePath, edited);
  } catch (err) {
    await restoreProtectedCore();
    return {
      message: `Stage 0.R escalated: D0.R wrote a corrupt core.json (restored the pre-edit core)`,
      coreJsonPath: corePath,
      escalate: {
        reason: `D0.R edited core is corrupt or unparseable: ${err instanceof Error ? err.message : String(err)}`,
      },
    };
  }
  const maintainedBefore = new Map(
    core.assumptions
      .filter((a) => a.maintained !== undefined)
      .map((a) => [a.id, JSON.stringify(a)] as const),
  );
  const maintainedAfter = new Map(
    edited.assumptions
      .filter((a) => a.maintained !== undefined)
      .map((a) => [a.id, JSON.stringify(a)] as const),
  );
  const changedMaintainedIds = new Set<string>();
  for (const [id, before] of maintainedBefore) {
    if (maintainedAfter.get(id) !== before) changedMaintainedIds.add(id);
  }
  for (const id of maintainedAfter.keys()) {
    if (!maintainedBefore.has(id)) changedMaintainedIds.add(id);
  }
  if (changedMaintainedIds.size > 0) {
    // A purported support witness may have been added alongside the protected
    // edit. Restore the whole pre-edit core so none of that unauthorized route
    // leaks into the live package before orchestrator adjudication.
    await restoreProtectedCore();
    return {
      message: "Stage 0.R attempted an orchestrator-maintained assumption edit",
      coreJsonPath: corePath,
      escalate: {
        reason:
          `D0.R changed protected maintained assumption(s) ${[...changedMaintainedIds].join(", ")}; ` +
          "the pre-edit core was restored and the finding requires orchestrator adjudication",
      },
    };
  }
  const findingNodeIds = new Set(
    findings
      .map((f) => (f as { node_id?: string }).node_id)
      .filter((id): id is string => typeof id === "string"),
  );
  const editedAssumptionIds = new Set(edited.assumptions.map((a) => a.id));
  const unauthorizedDeletedAssumptions = core.assumptions
    .filter((a) => !editedAssumptionIds.has(a.id) && !findingNodeIds.has(a.id))
    .map((a) => a.id);
  if (unauthorizedDeletedAssumptions.length > 0) {
    await restoreProtectedCore();
    return {
      message: "Stage 0.R attempted unscoped assumption deletion(s)",
      coreJsonPath: corePath,
      escalate: {
        reason:
          `D0.R deleted unflagged assumption(s) ${unauthorizedDeletedAssumptions.join(", ")}; ` +
          "the pre-edit core was restored and any broader assumption rewrite requires orchestrator review",
      },
    };
  }
  // why: only a real CLAIM change is illegal here; collapse whitespace so a formatting-only
  // rewrite (re-wrapping, trimmed spaces) of a legitimate D0.R repair does not spuriously escalate.
  const normClaim = (t: string) => normalizeTexWhitespace(t); // a \par-only edit to a protected statement must not slip the guard
  const illegalStatementEdits = edited.statements.filter((s) => {
    const before = preStatementText.get(s.id);
    return before !== undefined && normClaim(before) !== normClaim(s.statement);
  });
  if (illegalStatementEdits.length > 0) {
    // why: D0.R may fix proof/DAG content, but statement changes must go through orchestrator-owned proto.
    await restoreProtectedCore();
    return {
      message: `Stage 0.R attempted protected statement edits`,
      coreJsonPath: corePath,
      escalate: { reason: `D0.R changed protected statement text for ${illegalStatementEdits.map((s) => s.id).join(", ")}` },
    };
  }
  const { hard: gateViolations } = runGates([structuralGate], { core: edited, requireDischarged: true });
  if (gateViolations.length > 0) {
    const lines = gateViolations.map((v) => `  ${v.detail}`).join("\n");
    await restoreProtectedCore();
    return {
      message: `Stage 0.R edit did not re-discharge the gate`,
      coreJsonPath: corePath,
      escalate: { reason: `in-place edit left the core undischarged:\n${lines}` },
    };
  }

  // Record any PROVISIONAL def/assumption changes D0.R made this round as pending-approval
  // (same add-prove-approve-later contract as D0-SOLVE): the orchestrator and the next D0.5
  // review vet them; a rejected one rewinds. Diff the edited core against the pre-edit core.
  const preAss = new Map<string, { id: string; condition?: string }>(
    (core.assumptions ?? []).map((a: { id: string; condition?: string }) => [a.id, a]),
  );
  const preDef = new Map<string, string>(
    (core.definitions ?? []).map((d: { id: string; construction: string }) => [d.id, d.construction]),
  );
  const changedAss = edited.assumptions.filter((a) => JSON.stringify(preAss.get(a.id)) !== JSON.stringify(a));
  const removedAss = core.assumptions.filter((a) => !editedAssumptionIds.has(a.id));
  const changedDef = edited.definitions.filter((d) => preDef.get(d.id) !== d.construction);
  const pendingChanges = [
    ...changedAss.map((a) => ({
      kind: "assumption" as const,
      id: a.id,
      from: preAss.get(a.id) ?? null,
      to: a,
    })),
    ...removedAss.map((a) => ({
      kind: "assumption" as const,
      id: a.id,
      from: a,
      to: null,
    })),
    ...changedDef.map((d) => ({
      kind: "definition" as const,
      id: d.id,
      from: preDef.get(d.id) ?? null,
      to: d.construction,
    })),
  ];
  for (const a of changedAss) {
    if (!args.state.added_assumptions.some((x) => x.label === a.id)) {
      args.state.added_assumptions.push({
        label: a.id,
        statement: a.condition,
        user_approved: false,
        source: "D0.R provisional (pending approval)",
        classification: "faithful-refinement",
      });
    }
  }
  if (changedAss.length > 0 || removedAss.length > 0 || changedDef.length > 0) {
    const pendingPath = resolveInDir(path.dirname(corePath), "d0r_pending_changes.json", [
      `${args.ctx.qid}_d0r_pending_changes.json`,
    ]);
    // why: structured from/to diffs survive rewinds better than a free-form design note.
    await writeFile(pendingPath, JSON.stringify({ changes: pendingChanges }, null, 2), "utf8");
    args.state.design_decisions["d0r_pending_approval"] =
      `D0.R made ${changedAss.length + removedAss.length} assumption + ${changedDef.length} definition change(s) PROVISIONALLY ` +
      `(pending approval, direction-of-truth align/correct/discharge): ` +
      [...changedAss.map((a) => a.id), ...removedAss.map((a) => a.id), ...changedDef.map((d) => d.id)].join(", ");
    console.warn(`[D0.R] ${args.state.design_decisions["d0r_pending_approval"]}`);
  }

  const proseUpdates = diffCoreProse(core, edited);
  return {
    message: parsedOut.message ?? "Stage 0.R revised core.json provisionally",
    coreJsonPath: corePath,
    ...(proseUpdates ? { proseUpdates } : {}),
  };
}
