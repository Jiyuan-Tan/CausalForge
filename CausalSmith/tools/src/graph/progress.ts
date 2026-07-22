import { isUndeliveredNode, type FormalizationGraph, type GraphNode } from "./types.js";

const DEP_KINDS = new Set(["statement-uses", "proof-uses"]);

/** Every frozen theorem + its transitive uses-closure (the nodes that must be done). */
function frozenScope(graph: FormalizationGraph): Set<string> {
  const adj = new Map<string, string[]>();
  for (const e of graph.edges) {
    if (!DEP_KINDS.has(e.kind)) continue;
    if (!adj.has(e.from)) adj.set(e.from, []);
    adj.get(e.from)!.push(e.to);
  }
  const scope = new Set<string>();
  for (const n of graph.nodes) {
    if (n.kind !== "theorem" || n.provenance !== "from-note" || isUndeliveredNode(n)) continue;
    scope.add(n.id);
    const stack = [n.id];
    while (stack.length) {
      const cur = stack.pop()!;
      for (const v of adj.get(cur) ?? []) if (!scope.has(v)) { scope.add(v); stack.push(v); }
    }
  }
  return scope;
}

/** A node is "settled" iff: any theorem/lemma it is has a complete proof, AND any
 *  node the REVIEWER actually judges (a from-note theorem statement, or any
 *  assumption) has a matched/derived verdict. Definitions are checked transitively
 *  via their theorem's statement unfold (not a separate verdict); setup is the
 *  environment, and library/gate nodes are external/visible-debt — none of those
 *  carry a review requirement, so requiring it would deadlock the loop.
 *
 *  NOTE this is the STRICT graph-only check (every closure node must have a complete proof). A note
 *  lemma proven INLINE has no standalone decl, so it never reaches `complete` here — which is why the
 *  loop does NOT rely on this alone: it ALSO completes via `frozenTheoremsProven` + a tree-wide
 *  no-real-`sorry` guard (see proof_review_loop), which discharges inlined lemmas soundly. */
function settled(n: GraphNode): boolean {
  if ((n.kind === "theorem" || n.kind === "lemma") && n.proof.state !== "complete") return false;
  const reviewerJudges = (n.kind === "theorem" && n.provenance === "from-note") || n.kind === "assumption";
  if (reviewerJudges && n.review.status !== "matched" && n.review.status !== "derived") return false;
  return true;
}

/** Termination: every frozen theorem's uses-closure is proven + faithful. */
export function frozenClosuresComplete(graph: FormalizationGraph): boolean {
  const scope = frozenScope(graph);
  if (scope.size === 0) return false; // no frozen theorem yet → not done
  return graph.nodes.filter((n) => scope.has(n.id)).every(settled);
}

/** Every from-note headline theorem is a LINKED, complete Lean decl (the result is genuinely in
 *  Lean with no `sorry`). Paired with a tree-wide no-real-sorry guard, this is the proof-phase
 *  completeness signal: no open sorry anywhere + every headline proven ⇒ all inlined intermediate
 *  lemmas are discharged. Faithfulness of statements/assumptions is then judged by the F4
 *  convergence review, not here. */
export function frozenTheoremsProven(graph: FormalizationGraph): boolean {
  const thms = graph.nodes.filter(
    (n) => n.kind === "theorem" && n.provenance === "from-note" && !isUndeliveredNode(n),
  );
  if (thms.length === 0) return false;
  return thms.every((n) => !!n.lean?.decl_name && n.proof.state === "complete");
}

/** Did any node advance (open→complete proof, or non-matched→matched/derived review)? */
export function progressed(prev: FormalizationGraph, cur: FormalizationGraph): boolean {
  const prevById = new Map(prev.nodes.map((n) => [n.id, n] as const));
  for (const n of cur.nodes) {
    const p = prevById.get(n.id);
    if (!p) return true; // a new node appeared (decomposition / assumption)
    if (p.proof.state !== "complete" && n.proof.state === "complete") return true;
    const wasMatched = p.review.status === "matched" || p.review.status === "derived";
    const nowMatched = n.review.status === "matched" || n.review.status === "derived";
    if (!wasMatched && nowMatched) return true;
  }
  return false;
}
