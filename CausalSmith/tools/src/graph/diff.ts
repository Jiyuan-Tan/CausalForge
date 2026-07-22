import type { FormalizationGraph } from "./types.js";
import { statementHash } from "./hash.js";

/**
 * Node ids needing re-review. Seed = nodes whose fresh hash differs from the
 * recorded passed_hash (or that were never passed). Then propagate to dependents
 * ONLY along `statement-uses` edges: a node's STATEMENT faithfulness depends on the
 * objects its statement references, so a changed statement-dep makes it dirty. It does
 * NOT depend on its PROOF's dependencies — propagating through `proof-uses` would drag
 * every theorem perpetually dirty off its never-reviewed proof lemmas (L-blocks stay
 * `passed_hash:null` since lemmas aren't review targets), defeating the short-circuit.
 * Proof-completeness is tracked separately (proof.state), not via the review dirty frontier.
 *
 * Freshness fallback: a node with no Lean-extracted hash (a hypothesis-backed node whose
 * Lean realization lives INSIDE a host theorem's signature, not a standalone `@node:`-tagged
 * decl) falls back to the hash of its NL statement — the SAME convention `applyVerdictsToGraph`
 * uses when recording its `passed_hash`. This keeps the comparison symmetric: such a node is
 * verifiable (re-reviewed exactly when its recorded NL spec changes) instead of trusted forever
 * behind a constant sentinel. Its Lean-side drift is still caught via the host theorem's own hash.
 */
export function dirtyFrontier(graph: FormalizationGraph, freshHashes: Record<string, string>): string[] {
  const dirty = new Set<string>();
  for (const n of graph.nodes) {
    const fresh = freshHashes[n.id] ?? statementHash(n.nl.statement);
    // Genuine statement change (a previously-recorded hash no longer matches) → always re-review.
    const genuineChange = n.review.passed_hash !== null && fresh !== n.review.passed_hash;
    // Never reviewed → a dirty source ONLY if it is a paper-originated node we actually review.
    // Agent-introduced / library defs are never review targets, so their `passed_hash` stays `null`
    // forever; treating that as "dirty" would perpetually re-dirty every statement that references
    // them (e.g. t1 statement-uses the agent-introduced `aux_CrossFitNuisancesRandom`). Their
    // content is checked transitively when the from-note statement that uses them is reviewed.
    // Setup containers (S1/S2/S3) are not reviewer targets; their actual audit
    // surface is the per-symbol cluster ledger. Seeding them here reports a
    // broad dirty frontier that no node reviewer can clear. The remaining
    // kinds mirror reviewTargets/convergenceTargets.
    const reviewableFromNote =
      n.provenance === "from-note" &&
      (n.kind === "theorem" ||
        n.kind === "assumption" ||
        n.kind === "definition" ||
        n.kind === "lemma" ||
        (n.kind === "gate" && n.gate?.gate_class === "cited"));
    const firstReviewNeeded = n.review.passed_hash === null && reviewableFromNote;
    if ((genuineChange && n.kind !== "setup") || firstReviewNeeded) dirty.add(n.id);
  }
  // reverse adjacency: X statement-uses Y ⇒ edge X->Y; if Y dirty, X dirty.
  const dependents = new Map<string, string[]>();
  for (const e of graph.edges) {
    if (e.kind !== "statement-uses") continue;
    if (!dependents.has(e.to)) dependents.set(e.to, []);
    dependents.get(e.to)!.push(e.from);
  }
  const queue = [...dirty];
  while (queue.length) {
    const cur = queue.shift()!;
    for (const dep of dependents.get(cur) ?? []) {
      if (!dirty.has(dep)) {
        dirty.add(dep);
        queue.push(dep);
      }
    }
  }
  return [...dirty].sort();
}
