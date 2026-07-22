import type { FormalizationGraph } from "./types.js";

/**
 * Frozen-note immutability guard.
 *
 * Why this exists (2026-06-17): the `.md`/graph NL of a from-note (frozen) node is one of TWO
 * parallel representations of the paper's claim — the other being the `.tex` / paper draft that
 * causalsmith's P3 equivalence gate consumes. F3 (NL↔Lean) consumes the graph NL. If a proof-loop
 * stage MUTATES a frozen NL to make it match the Lean (rather than fixing the Lean), it desyncs the
 * two representations: the `.tex` still states the strong claim, the NL is quietly weakened, and the
 * over-claim slips past F3 while P3 keeps (correctly) flagging it. This actually happened — the
 * legacy F3.5 "delaunder" repair (decision D1) weakened A-1's `cond_exch` from the primitive
 * `(Y(0),Y(1))⊥A∣X` down to the moment-identity bundle it implies, to clear an unused-hypothesis
 * finding. The note is the FROZEN CONTRACT: a stage may edit Lean, never the frozen NL.
 *
 * This guard snapshots every frozen node's NL at loop entry and asserts it is byte-stable across
 * each refresh. A violation is a stage misbehaving (laundering by note-weakening) — surface it
 * loudly rather than letting the weakened note bank.
 */

/** A frozen node = a paper object: `nl.frozen === true` (equivalently from-note provenance). */
function isFrozen(n: FormalizationGraph["nodes"][number]): boolean {
  return n.nl?.frozen === true || n.provenance === "from-note";
}

/** Snapshot id → exact `nl.statement` for every frozen node. */
export function frozenNlFingerprint(graph: FormalizationGraph): Map<string, string> {
  const m = new Map<string, string>();
  for (const n of graph.nodes) {
    if (isFrozen(n)) m.set(n.id, n.nl?.statement ?? "");
  }
  return m;
}

export interface FrozenNlChange {
  id: string;
  before: string;
  after: string | null; // null = the frozen node vanished
}

/** Thrown when a frozen node's NL changed (or the node disappeared) since the baseline. */
export class FrozenNlMutationError extends Error {
  constructor(public readonly changed: FrozenNlChange[]) {
    super(
      `frozen-note immutability violated — ${changed.length} from-note NL(s) mutated mid-loop ` +
        `(a stage weakened the frozen contract instead of fixing the Lean): ` +
        changed
          .map((c) => `${c.id}${c.after === null ? " (deleted)" : `: "${snippet(c.before)}" → "${snippet(c.after)}"`}`)
          .join("; "),
    );
    this.name = "FrozenNlMutationError";
  }
}

function snippet(s: string): string {
  const one = s.replace(/\s+/g, " ").trim();
  return one.length > 80 ? one.slice(0, 77) + "…" : one;
}

/**
 * Assert that every frozen node in `baseline` is still present in `graph` with an UNCHANGED
 * `nl.statement`. Throws `FrozenNlMutationError` listing every drift. New frozen nodes appearing
 * are not flagged here (the loop adds agent-introduced nodes, never frozen ones; a spurious new
 * frozen node is caught by the from-note provenance checks elsewhere).
 */
export function assertFrozenNlStable(baseline: Map<string, string>, graph: FormalizationGraph): void {
  const changed = frozenNlChanges(baseline, graph);
  if (changed.length > 0) throw new FrozenNlMutationError(changed);
}

/** The set of frozen NLs that drifted from `baseline` (present-but-changed, or deleted). */
export function frozenNlChanges(baseline: Map<string, string>, graph: FormalizationGraph): FrozenNlChange[] {
  const now = new Map(graph.nodes.filter(isFrozen).map((n) => [n.id, n.nl?.statement ?? ""] as const));
  const changed: FrozenNlChange[] = [];
  for (const [id, before] of baseline) {
    if (!now.has(id)) changed.push({ id, before, after: null });
    else if (now.get(id) !== before) changed.push({ id, before, after: now.get(id)! });
  }
  return changed;
}

/** Non-throwing variant for inline loop checkpoints: returns a one-line escalation reason naming
 *  the mutated frozen NLs, or `null` if the frozen contract is intact. */
export function frozenMutationReason(baseline: Map<string, string>, graph: FormalizationGraph): string | null {
  const changed = frozenNlChanges(baseline, graph);
  return changed.length === 0 ? null : new FrozenNlMutationError(changed).message;
}
