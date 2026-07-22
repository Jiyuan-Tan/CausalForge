/**
 * Pure helpers for gate registration / DISCHARGE bookkeeping shared by `bin/gate.ts`.
 * Kept side-effect-free so the register/ungate logic is unit-testable without touching
 * the plan/graph/state files on disk.
 */

export interface PlanNodeLike {
  hyps?: string[];
  lean_name?: string;
}
export interface GraphEdgeLike {
  kind: string;
  from: string;
  to: string;
}
export interface AddedAssumptionLike {
  label?: string;
  anchor?: string;
  statement?: string;
  source?: string;
  classification?: string;
}

/** A node as seen by {@link auditSubstrateGates} — plan side carries the gate keys. */
export interface AuditPlanNode {
  id: string;
  lean_name?: string;
  gate?: boolean;
  gate_class?: string;
}
/**
 * A node as seen by {@link auditSubstrateGates} — graph side carries `kind`, and names its Lean
 * realization under `lean.decl_name` (fully qualified) rather than the plan's flat `lean_name`.
 */
export interface AuditGraphNode {
  id: string;
  kind?: string;
  lean_name?: string;
  lean?: { decl_name?: string } | null;
}
/** One unregistered-gate finding. */
export interface SubstrateGateFinding {
  label: string;
  reason: string;
}

/**
 * The consumers of a gate node — the theorems that thread it as a hypothesis. Derived
 * from graph `proof-uses` edges (consumer → node) UNION plan nodes whose `hyps` list the
 * node. Lets `--ungate` find the consumers automatically, so the caller need not re-supply
 * the exact `--consumers` used at registration (a footgun in the old `--unset`).
 */
export function deriveGateConsumers(
  edges: GraphEdgeLike[],
  planNodes: Record<string, PlanNodeLike> | null | undefined,
  nodeId: string,
): string[] {
  const fromGraph = edges
    .filter((e) => e.kind === "proof-uses" && e.to === nodeId)
    .map((e) => e.from);
  const fromPlan = planNodes
    ? Object.keys(planNodes).filter((k) => (planNodes[k]?.hyps ?? []).includes(nodeId))
    : [];
  return [...new Set([...fromGraph, ...fromPlan])];
}

/**
 * Every string that can identify this gate in a disclosure/debt line: the node id plus
 * any Lean realization name(s) (the plan `lean_name`, an explicit `--lean-name`). F5 keys
 * its derived disclosure by the Lean TYPE name while `gate.ts` keys its own by the node id,
 * so a robust discharge must match both.
 */
export function gateIdentityStrings(nodeId: string, ...leanNames: (string | undefined | null)[]): string[] {
  return [...new Set([nodeId, ...leanNames.filter((s): s is string => !!s)])];
}

/**
 * True if an `added_assumptions` entry discloses THIS gate — matched precisely by the entry
 * label being, or ending in `:<id>`, for one of the gate's identity strings. (Label-suffix,
 * not a free substring scan, so an unrelated assumption that merely mentions the name in prose
 * is not swept away.)
 */
export function isGateDisclosure(entry: AddedAssumptionLike, ids: string[]): boolean {
  const label = entry.label ?? "";
  return ids.some((id) => label === id || label.endsWith(":" + id));
}

/**
 * A plan node with its gate-specific keys removed (used on discharge). The plan schema requires
 * `gate_class` to be `'gated' | 'cited'` or ABSENT — a leftover `gate_class: null` trips the F2
 * post-sync `plan_gate` schema check — so discharge DELETES the keys rather than nulling them.
 */
export function withoutGateKeys<T extends Record<string, unknown>>(node: T): Omit<T, "gate" | "gate_class"> {
  const { gate: _g, gate_class: _gc, ...rest } = node;
  return rest;
}

/**
 * True if a `SUBSTRATE_DEBT.md` line is a `gate.ts`-APPENDED debt bullet for this gate:
 * `- **<id>** (<class>) — …`. Deliberately does NOT match hand-authored prose such as
 * `- **<id>** — **RESOLVED**` (no ` (` after the bold id), so a user's discharge note survives.
 */
export function isGateDebtBullet(line: string, ids: string[]): boolean {
  const t = line.trimStart();
  return ids.some((id) => t.startsWith(`- **${id}** (`));
}

/** A persisted cited source-match verdict (`state.cited_checks`). */
export interface CitedCheckLike {
  name: string;
  check_status?: string;
}

/**
 * The cited verdicts that HARD-BLOCK banking: `cited-mismatch` (the Lean `def` does not faithfully
 * encode the cited statement) and `cited-underspecified` (the `def` is not self-contained).
 *
 * The proof–review loop escalates on these, but that check is in-process only — it cannot stop a
 * later `bank_entry.ts --tier accepted`, nor a resume re-entering at F5. `bankEntry` re-checks the
 * durable `state.cited_checks` with this predicate, so the documented block holds at the one
 * irreversible moment. Other verdicts (verified / attested / unverifiable) pass.
 */
export function citedBlockers(checks: CitedCheckLike[]): CitedCheckLike[] {
  return checks.filter(
    (c) => c.check_status === "cited-mismatch" || c.check_status === "cited-underspecified",
  );
}

/**
 * Lint: every `added_assumptions` entry classified `substrate-gate` must correspond to a node
 * REGISTERED as a gate (`gate:true` in the plan, or `kind:"gate"` in the graph).
 *
 * A disclosed-but-unregistered gate is the silent-drift failure this catches. The disclosure makes
 * the debt *visible* in `SUBSTRATE_DEBT.md`, but nothing mechanically enforces "build before
 * banking", and — worse — the hypothesis lives only as hand-written Lean, which the next F2
 * re-scaffold drops (it rebuilds statements from `plan.json`), silently turning the theorem's
 * premise into a `sorry`. Registration is what makes a gate durable and machine-visible.
 *
 * Observed in the wild on `exp_bipartite_minimax_design/v1` (`EnvelopeLineC2Data`), which banked
 * `accepted` carrying an undischarged proof-step gate that no store recorded as a gate.
 *
 * The disclosure's `label` is matched against both the node id and the node's Lean name, because
 * F5 keys its derived disclosure by the Lean type name while `gate.ts` keys its own by node id.
 *
 * @returns one finding per offending disclosure; `[]` means clean.
 */
export function auditSubstrateGates(args: {
  addedAssumptions: AddedAssumptionLike[];
  planNodes: AuditPlanNode[];
  graphNodes: AuditGraphNode[];
}): SubstrateGateFinding[] {
  const findings: SubstrateGateFinding[] = [];
  for (const entry of args.addedAssumptions) {
    if (entry.classification !== "substrate-gate") continue;
    const label = entry.label ?? "";

    // Candidate nodes this disclosure could refer to: label === id, or label ends in `:<id>`,
    // for either the node id or its Lean name (see `isGateDisclosure` / `gateIdentityStrings`).
    const matches = (id: string | undefined): boolean =>
      !!id && (label === id || label.endsWith(":" + id));

    const plan = args.planNodes.find((n) => matches(n.id) || matches(n.lean_name));
    const graph = args.graphNodes.find(
      (n) => matches(n.id) || matches(n.lean_name) || matches(n.lean?.decl_name?.split(".").pop()),
    );

    if (!plan && !graph) {
      findings.push({
        label,
        reason: `classified substrate-gate but has no plan/graph node — the debt is prose-only and unenforceable.`,
      });
      continue;
    }
    const registered = plan?.gate === true || graph?.kind === "gate";
    if (!registered) {
      findings.push({
        label,
        reason:
          `classified substrate-gate but the node is not registered as a gate ` +
          `(plan gate:true / graph kind:"gate"). Register it with bin/gate.ts before banking — ` +
          `an unregistered gate is dropped by the next F2 re-scaffold and becomes a silent sorry.`,
      });
    }
  }
  return findings;
}
