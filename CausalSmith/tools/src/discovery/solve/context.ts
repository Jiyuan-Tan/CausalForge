// D0-SOLVE step 1/5 — assembleContext (spec §Stage kernel).
//
// Everything runStage0Solve establishes BEFORE any agent is dispatched, moved
// verbatim from stage0_solve.ts in the T1 carve: the proto→core clone, the
// incremental-reuse carry across escalation rounds (working-state load, revision
// guard, supersession preservation, escalation-log consumption), resolved-OEQ
// re-application, the carry plan, lemma/member carry, stale-agent recovery, and
// required-target recovery from the prior published core.
import { existsSync } from "node:fs";
import { mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StateJson } from "../../types.js";
import { clusterFor, loadDiscoveryClusterSetupBlock } from "../cluster_setup.js";
import { coreJsonPath } from "../stages/d0_core.js";
import { protoCoreJsonPath } from "../stages/neg1_2_author.js";
import { CoreSchema, type Core, type CoreStatement } from "../core/schema.js";
import { recordProof } from "../working_writer.js";
import { planCarry } from "../carry_plan.js";
import { solvedStatus } from "../core/status.js";
import {
  type WorkingState,
  loadWorkingState,
  proposalRevision,
  readEscalationLog,
  formatEscalationContext,
  computeValidNodes,
} from "../stages/d0_working.js";
import type { RawCoreEdit } from "../stages/d0_apply.js";
import { loadSemanticManifest, validateCoreManifest, type SemanticManifest } from "../semantic_manifest.js";
import { emptyProposals, readRoundProposals } from "./proposals.js";
import { readTypedCore } from "../core/core_io.js";

/** Mathematical identity of an OEQ resolution source. Motivation prose is deliberately
 * absent: changing a gap/consumer note cannot make a theorem stop answering the same
 * question. Dependencies are a set throughout proof reuse, so order/repeats are
 * canonicalized here too. */
export function oeqSourceFingerprint(s: CoreStatement): string {
  return JSON.stringify({
    kind: s.kind,
    statement: s.statement,
    depends_on: [...new Set(s.depends_on)].sort(),
  });
}

/** Accept fingerprints written by the earlier, prose-sensitive format when their
 * mathematical source is unchanged. The next successful carry rewrites them in the
 * canonical format, avoiding a one-time re-answer across existing runs. */
export function oeqSourceFingerprintMatches(s: CoreStatement, fingerprint: string): boolean {
  try {
    const prior = JSON.parse(fingerprint) as { kind?: unknown; statement?: unknown; depends_on?: unknown };
    if (prior.kind !== s.kind || prior.statement !== s.statement || !Array.isArray(prior.depends_on)) return false;
    if (!prior.depends_on.every((x) => typeof x === "string")) return false;
    const deps = (xs: string[]): string[] => [...new Set(xs)].sort();
    return JSON.stringify(deps(prior.depends_on)) === JSON.stringify(deps(s.depends_on));
  } catch {
    return false;
  }
}

// A `cited` statement is INVOKED (its justification IS the citation), never
// derived by us — assembly must PRESERVE `cited` (and its `source`). Forcing a
// solved/carried node to `proved` unconditionally keeps the `source` on a
// non-cited status and trips the schema's G-cited gate, and would launder an
// invoked result as one we proved. So a solved node becomes `proved` ONLY if it
// was not already `cited`.
const invalidatedCatalogNode = (s: CoreStatement): CoreStatement =>
  s.source !== undefined
    ? { ...s, status: "cited", proof_tex: undefined }
    : { ...s, status: "to-prove", proof_tex: undefined, source: undefined };
export const openSolveTarget = (s: CoreStatement): CoreStatement => ({
  ...s,
  status: "to-prove",
  proof_tex: undefined,
  // `source` is legal iff status=cited. The source remains durable on the
  // partial catalog node above and the solver must re-emit it to discharge.
  source: undefined,
});

/** Everything the later solve steps (dispatch/merge/gates/commit) read or mutate.
 *  `core`, `proto` and `next` are shared mutable state threaded through the round. */
export interface SolveRoundContext {
  proto: Core;
  core: Core;
  protoPath: string;
  corePath: string;
  semanticManifest: SemanticManifest | null;
  clusterSetupBlock: string;
  prev: WorkingState | null;
  next: WorkingState;
  validIds: Set<string>;
  sourceById: Map<string, CoreStatement>;
  persistedOeqReplacements: Map<string, string>;
  carriedMembers: number;
  staleAgentTargets: CoreStatement[];
  pendingSupersessionEdits: Array<Extract<RawCoreEdit, { kind: "statement-delete" }>>;
  hasPendingDirective: boolean;
  requiresCoreChanges: boolean;
  requiredCoreTargets: Set<string>;
  escContext: string;
}

export async function assembleSolveContext(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<SolveRoundContext> {
  const { ctx, state } = args;
  const protoPath = protoCoreJsonPath(ctx);
  if (!existsSync(protoPath)) {
    throw new Error(`Stage 0-SOLVE requires the frozen proposal core at ${protoPath} (run D-1.2 first)`);
  }
  const proto = await readTypedCore(protoPath);
  const semanticManifest = await loadSemanticManifest(ctx);
  validateCoreManifest(semanticManifest, "proto", proto);
  // The solved core starts as a verbatim copy of the frozen proposal core; the
  // solver fills proofs + adds lemmas, but never silently edits frozen claims.
  const core: Core = CoreSchema.parse(JSON.parse(JSON.stringify(proto)));
  const corePath = coreJsonPath(ctx);
  await mkdir(path.dirname(corePath), { recursive: true });
  const clusterSetupBlock = await loadDiscoveryClusterSetupBlock(ctx, clusterFor(ctx, state));

  // --- Incremental reuse across escalation rounds. Carry still-valid proofs from the
  // prior round; dispatch only the WCC groups a correction actually invalidated (open
  // members), handing each open group its established proofs + the orchestrator
  // escalation log as context so it builds on the prior solution instead of redoing it.
  const loadedPrev = await loadWorkingState(ctx);
  const currentProposalRevision = proposalRevision(state);
  const proposalRevisionChanged =
    loadedPrev !== null &&
    loadedPrev.proposal_revision !== currentProposalRevision &&
    (loadedPrev.proposal_revision !== undefined || currentProposalRevision !== undefined);
  // Member snapshots deliberately support incremental D0 edits inside one
  // accepted proposal revision.  They cannot authorize reuse across D-1.2
  // source rewinds: removed source claims may otherwise remain as valid-looking
  // agent-added lemmas/theorems and resurrect in the assembled core.
  const prev = proposalRevisionChanged ? null : loadedPrev;
  // Supersession is one semantic operation split across an immediately assembled
  // replacement and a gated statement-delete. Preserve the gated half across retries;
  // otherwise constructing `next.proposals` from this round alone erases the only A→A'
  // relation and a later clean round can publish both chains as proved.
  const pendingSupersessionEdits = prev === null
    ? []
    : (await readRoundProposals(ctx, prev)).coreEdits.filter(
        (edit): edit is Extract<RawCoreEdit, { kind: "statement-delete" }> =>
          edit.kind === "statement-delete" && edit.replacement_id !== undefined,
      );
  if (proposalRevisionChanged) {
    console.warn(
      `[D0-SOLVE] proposal revision changed (${loadedPrev?.proposal_revision ?? "legacy"} -> ` +
        `${currentProposalRevision ?? "unversioned"}); invalidating all carried D0 proofs.`,
    );
  }
  const escalationLog = await readEscalationLog(ctx);
  const consumedEscalations = Math.min(
    loadedPrev?.escalation_entries_consumed ?? 0,
    escalationLog.length,
  );
  const pendingEscalations = escalationLog.slice(consumedEscalations);
  // Provenance-only entries are rendered into the escalation CONTEXT (the solver still
  // reads them) but never count as a re-solve directive. Without this split, an entry
  // whose only purpose is to preserve a paid verdict would set `hasPendingDirective`
  // with no targets, and the branch below would force EVERY statement open — a
  // whole-paper re-derivation triggered by an act of bookkeeping.
  const hasPendingDirective = pendingEscalations.some(
    (entry) =>
      entry.provenance_only !== true &&
      typeof entry.directive === "string" &&
      entry.directive.trim().length > 0,
  );
  const requiresCoreChanges = pendingEscalations.some((entry) => entry.require_core_changes === true);
  const requiredCoreTargets = new Set(pendingEscalations.flatMap((entry) => entry.required_core_targets ?? []));
  const escContext = formatEscalationContext(pendingEscalations);
  const round = (loadedPrev?.round ?? 0) + 1;
  // (The historical `proposed_proofs.json` mirror and its round-lifecycle
  // invariant are retired: `working.proposals` is rebuilt wholesale on every
  // commit, so a provisional proof cannot outlive its round.)
  // Directive delivery and mathematical proof validity are separate concerns.
  // Keep ordinary snapshot validity intact; a forced-target overlay below delivers
  // the directive without converting unrelated carried proofs into partial debt.
  let validIds = computeValidNodes(prev, proto);
  const next: WorkingState = {
    round,
    proposal_revision: currentProposalRevision,
    escalation_entries_consumed: escalationLog.length,
    solved: {},
    resolved_oeqs: {},
    // CARRY THE CONSUMED MARKER. `readRoundProposals` treats an ABSENT `proposals`
    // field with legacy leftovers on disk as an unmigrated run and fails loud, so the
    // rebuilt state always carries an explicit (empty) payload. A round that surfaces
    // proposals overwrites this below.
    proposals: emptyProposals() as unknown as WorkingState["proposals"],
  };

  // A resolved OEQ has a two-part durable representation: its answer theorem is
  // an agent-added node in `solved`, while its original question remains in the
  // frozen proto. Re-apply every still-valid source -> theorem replacement before
  // carrying proofs or computing the next open frontier. Without this, a retry
  // carries the answer theorem AND dispatches the old OEQ again, eventually
  // colliding on the theorem id or reintroducing an open question into F1.
  const sourceById = new Map(proto.statements.map((s) => [s.id, s] as const));
  const resolutionCandidates = new Map<string, { theoremId: string; sourceFingerprint: string }>();
  const resolutionTheoremIds = new Set<string>();
  for (const [sourceId, raw] of Object.entries(prev?.resolved_oeqs ?? {})) {
    if (typeof raw === "string") {
      // The first implementation stored only a theorem id. Its source may have
      // changed before this resume, which cannot be established from that state;
      // re-solve conservatively, while suppressing the stale theorem below.
      resolutionTheoremIds.add(raw);
    } else {
      resolutionCandidates.set(sourceId, { theoremId: raw.theorem_id, sourceFingerprint: raw.source_fingerprint });
      resolutionTheoremIds.add(raw.theorem_id);
    }
  }
  // Compatibility handling for working states written before `resolved_oeqs`:
  // those records cannot establish that the frozen OEQ still matches the answer,
  // and a historical OEQ-led group could have added another theorem helper. Do
  // not guess a mapping; re-solve the OEQ and omit every stale owner-marked
  // theorem so it cannot collide with the freshly emitted answer.
  // Once the explicit mapping exists, owner is only provenance: an OEQ-led
  // solve unit may legitimately emit additional theorem helpers. Classifying
  // every such theorem as the OEQ replacement discards those helpers on retry.
  if (prev && !Object.prototype.hasOwnProperty.call(prev, "resolved_oeqs")) {
    for (const [theoremId, rec] of Object.entries(prev.solved ?? {})) {
      if (
        rec.node?.kind === "theorem" &&
        typeof rec.owner === "string" &&
        sourceById.get(rec.owner)?.kind === "openendedquestion"
      ) {
        resolutionTheoremIds.add(theoremId);
      }
    }
  }
  const persistedOeqReplacements = new Map<string, string>();
  for (const [sourceId, candidate] of resolutionCandidates) {
    const source = sourceById.get(sourceId);
    const theorem = prev?.solved[candidate.theoremId];
    // NOT gated on the answer being VALID. A stale answer means "this proof needs
    // refreshing", not "this is no longer the answer" — and conflating the two was
    // expensive. Requiring validity here dropped the whole mapping whenever anything in
    // the answer's content closure moved, which returned the OEQ to the open frontier
    // and made the solver invent a NEW answer under a NEW id. Observed twice in one
    // run (`…-boundary-not-necessary` → `…-learning-boundary-not-necessary`,
    // `…-diameter-obstruction` → `…-diameter-lower-bound`), each costing a full solve
    // round to re-derive a result that only needed its proof re-checked, and churning
    // every downstream reference. Worse, the answer was excluded from the ordinary
    // carry AND from stale recovery, so it fell through both and vanished with its
    // statement definition — the silent loss of a finished theorem.
    //
    // The FINGERPRINT is what legitimately invalidates a resolution: if the QUESTION
    // changed, the old answer may no longer answer it. That check stays.
    if (
      source?.kind === "openendedquestion" &&
      theorem?.node &&
      oeqSourceFingerprintMatches(source, candidate.sourceFingerprint)
    ) {
      persistedOeqReplacements.set(sourceId, candidate.theoremId);
      next.resolved_oeqs![sourceId] = {
        theorem_id: candidate.theoremId,
        source_fingerprint: oeqSourceFingerprint(source),
      };
    }
  }
  // Validity follows statement dependencies transitively. Consumers in the frozen
  // proto still name the OEQ, but after a durable resolution they semantically
  // depend on its theorem answer. Normalize that edge for the reuse calculation,
  // otherwise every consumer is needlessly invalidated by the absent OEQ record.
  if (persistedOeqReplacements.size > 0) {
    const protoWithResolvedDeps: Core = {
      ...proto,
      statements: proto.statements.map((s) => ({
        ...s,
        depends_on: s.depends_on.map((d) => persistedOeqReplacements.get(d) ?? d),
      })),
    };
    validIds = computeValidNodes(prev, protoWithResolvedDeps);
  }
  if (persistedOeqReplacements.size > 0) {
    core.statements = core.statements
      .filter((s) => !persistedOeqReplacements.has(s.id))
      .map((s) => ({ ...s, depends_on: s.depends_on.map((d) => persistedOeqReplacements.get(d) ?? d) }));
    // The core is rebuilt from the frozen proto, whose `used_by` still names the OEQ, so the
    // reverse edge needs the same remap the fresh-resolution path applies below.
    core.assumptions = core.assumptions.map((a) =>
      a.used_by ? { ...a, used_by: a.used_by.map((u) => persistedOeqReplacements.get(u) ?? u) } : a,
    );
    for (const theoremId of persistedOeqReplacements.values()) {
      // A STALE answer is inserted by the stale-recovery path below instead, as an open
      // target under the SAME id — which is the whole point: the question stays answered,
      // so the OEQ never returns to the frontier and no new answer id is invented.
      if (!validIds.has(theoremId)) continue;
      const theorem = prev!.solved[theoremId];
      core.statements.push({
        ...theorem.node!,
        proof_tex: theorem.proof_tex,
        status: solvedStatus(theorem.node!),
        depends_on: theorem.node!.depends_on.map((d) => persistedOeqReplacements.get(d) ?? d),
      });
    }
  }

  // ONE decision point for "does this node survive the round?". Every branch below
  // executes this plan rather than re-deriving the predicate; `carryPlan.explain(id)`
  // answers "why did X vanish?" without tracing the assembly.
  const carryPlan = planCarry({
    prev,
    protoIds: new Set(sourceById.keys()),
    validIds,
    resolutionTheoremIds,
    persistedOeqReplacements,
  });
  // A dropped node leaves the working state with no record anywhere, so this is the
  // only chance to say so. Silence here is what made a lost theorem undiagnosable.
  for (const id of carryPlan.ids("dropped")) {
    console.warn(`[D0-SOLVE] carry: ${carryPlan.explain(id)}`);
  }

  // Carry valid agent-added LEMMAS (not in the proto) into the assembled core + state.
  for (const [id, rec] of Object.entries(prev?.solved ?? {})) {
    const verdict = carryPlan.verdicts.get(id);
    if (rec.node && verdict?.fate === "carried" && verdict.as !== "proto-member") {
      // Resolved OEQ theorems were inserted above while replacing their source.
      if (!core.statements.some((s) => s.id === id)) {
        core.statements.push({ ...rec.node, proof_tex: rec.proof_tex, status: solvedStatus(rec.node) });
      }
      next.solved[id] = rec;
    }
  }

  // Carry valid SPEC members. They are then EXCLUDED from the coupling graph below,
  // so a proved-and-stable shared lemma/prop no longer force-merges its (otherwise
  // independent) consumers into one agent — a frozen node can transmit no change, so
  // there is nothing to reconcile through it. The node still lives in the assembled
  // core (and the final graph/.tex); it just stops being a coupling EDGE.
  let carriedMembers = 0;
  // Deliberately NOT routed through `carryPlan`: a frozen member's reusability is
  // exactly `validIds`, and that question overlaps the plan's rather than partitioning
  // with it (a node can be both a frozen member and an OEQ answer). Forcing one verdict
  // onto both changed behaviour in that overlap.
  for (const m of proto.statements) {
    if (validIds.has(m.id)) {
      const rec = prev!.solved[m.id];
      const cs = core.statements.find((s) => s.id === m.id);
      if (cs) {
        cs.proof_tex = rec.proof_tex;
        cs.status = solvedStatus(cs);
      }
      next.solved[m.id] = rec;
      carriedMembers += 1;
    } else if (prev?.solved[m.id] !== undefined && next.solved[m.id] === undefined) {
      // An INVALID frozen-member record still carries durable state later rounds
      // need: the reopen marker (`partial`) of a cited leaf awaiting revalidation,
      // and the node's hot partial proof bytes (its single repair basis). `next`
      // replaces the cursor WHOLESALE at commit, so dropping the record here erased
      // that state on any round that did not re-record the id — observed shape: a
      // withheld revalidation receipt committed a cursor without the reopen marker,
      // and the stale citation silently re-certified the narrowed claim next round.
      // Carry it as PARTIAL debt (never reusable proof — `partial` outranks the cited
      // exemption at every discharge gate); a successful re-proof or revalidation
      // receipt overwrites this record within the round that discharges it.
      next.solved[m.id] = { ...prev.solved[m.id], partial: true };
    }
  }

  // Agent-added result nodes are not frozen into proto_core.json. If a later
  // structured edit changes one of their dependencies, snapshot reuse correctly
  // invalidates them, but a proto-only frontier would then forget that they need
  // re-proving. Recover every invalid non-lemma result root and its invalid
  // agent-added dependency closure as explicit to-prove targets. Actual OEQ
  // replacement theorems remain governed by the source->answer mapping above.
  const staleAgentById = new Map<string, WorkingState["solved"][string]>();
  for (const [id, rec] of Object.entries(prev?.solved ?? {})) {
    const verdict = carryPlan.verdicts.get(id);
    // `oeq-answer` joins `agent-node` here: a still-mapped but stale OEQ answer is
    // recovered as an ordinary to-prove target under its own id, rather than being
    // discarded and re-invented. Both live only in `solved`, so both would otherwise
    // lose their statement definition outright.
    if (rec.node && verdict?.fate === "re-derive" && (verdict.as === "agent-node" || verdict.as === "oeq-answer")) {
      staleAgentById.set(id, rec);
      // `solved` is also the durable catalog for agent-authored statements.
      // Proof invalidation must not delete the statement definition: preserve an
      // explicit to-prove record before any proposal checkpoint can clear core.json.
      // A D-1.2 proposal-revision change sets prev=null above, and explicit
      // statement-delete removes the record in stage0_apply, so those remain the
      // only two ways an active agent node leaves the cursor.
      next.solved[id] = {
        ...rec,
        node: invalidatedCatalogNode(rec.node),
        partial: true,
      };
    }
  }
  const staleTargetIds = new Set<string>();
  const addStaleClosure = (id: string): void => {
    if (staleTargetIds.has(id)) return;
    const rec = staleAgentById.get(id);
    if (!rec?.node) return;
    staleTargetIds.add(id);
    for (const dependency of rec.node.depends_on ?? []) addStaleClosure(dependency);
  };
  for (const [id, rec] of staleAgentById) {
    // Ordinary helper lemmas are pulled in through an invalid result root, but an
    // explicitly required stale lemma is itself the directed repair root. Without
    // this exception a partial agent-authored cited lemma disappears from the solve
    // frontier: it is absent from proto, present in working (so prior-core recovery
    // declines it), yet never dispatched and therefore can never be revalidated.
    if (rec.node?.kind !== "lemma" || requiredCoreTargets.has(id)) addStaleClosure(id);
  }
  const staleAgentTargets: CoreStatement[] = [];
  for (const id of staleTargetIds) {
    const rec = staleAgentById.get(id)!;
    const target = openSolveTarget(rec.node!);
    if (!core.statements.some((statement) => statement.id === id)) core.statements.push(target);
    staleAgentTargets.push(target);
  }

  // A proposed-change checkpoint can leave an agent-added result in the last
  // schema-valid assembled core as `to-prove` while (correctly) omitting it from
  // `working.solved`: there is no completed proof to carry. Because such a result
  // never lived in the frozen proto, the next directed round would otherwise forget
  // the node entirely and make an exact `required_core_targets` directive impossible
  // to satisfy. Recover only explicitly required targets, only within the same
  // proposal revision, and only from the current validated core. This is deliberately
  // narrower than treating core.json as a second proto: ordinary stale/orphan nodes
  // must not be resurrected, especially across a D-1.2 source rewind.
  if (
    requiredCoreTargets.size > 0 &&
    prev !== null &&
    !proposalRevisionChanged &&
    existsSync(corePath)
  ) {
    const missingRequiredTargets = [...requiredCoreTargets].filter((id) =>
      !sourceById.has(id) &&
      prev.solved[id] === undefined &&
      !core.statements.some((statement) => statement.id === id),
    );
    // Read the prior published core only when a required agent-authored target is
    // genuinely absent from both the proto and working cursor. A killed D0 round
    // can leave an intermediate, intentionally undischarged core on disk; eagerly
    // schema-parsing it here blocks the working cursor from completing recovery.
    const priorCore = missingRequiredTargets.length > 0
      ? await readTypedCore(corePath)
      : null;
    for (const id of missingRequiredTargets) {
      const priorNode = priorCore!.statements.find((statement) => statement.id === id);
      if (!priorNode) continue; // a genuinely new required node must still be emitted as an addition.
      const target = openSolveTarget(priorNode);
      core.statements.push(target);
      staleAgentTargets.push(target);
      recordProof(next, proto, {
        id,
        snapshotOf: priorNode,
        proofTex: priorNode.proof_tex ?? "",
        node: target,
        partial: true,
      });
    }
  }

  return {
    proto,
    core,
    protoPath,
    corePath,
    semanticManifest,
    clusterSetupBlock,
    prev,
    next,
    validIds,
    sourceById,
    persistedOeqReplacements,
    carriedMembers,
    staleAgentTargets,
    pendingSupersessionEdits,
    hasPendingDirective,
    requiresCoreChanges,
    requiredCoreTargets,
    escContext,
  };
}
