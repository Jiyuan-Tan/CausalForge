// One definition of "walk the core's dependency graph".
//
// Five closure walks exist across the D-stage — `computeValidNodes`'s staleness
// fixpoint, `pruneOrphanLemmas`'s reachability DFS, `stage0_solve`'s `addStaleClosure`
// recursion, `wireStatementProofDependencies`'s cycle guard, and `pruneDeadAssumptions`'s
// aliveness closure. They re-implement the same visited-set traversal, but they differ
// in direction (forward vs reverse) and in what they do at each node, and — checked, not
// assumed — ALL FIVE are correctly cycle-guarded today.
//
// So this module is NOT a mandate to fold them in. They are individually correct, none
// has caused a defect, and rewriting five working traversals to share a helper is
// transcription risk bought with no safety. It exists for NEW callers (and for
// `dependentsOf`, which had no implementation at all), so the count stops growing.
//
// The traversal is the part worth sharing; the per-node policy is not. So these take
// the edge function as a parameter and return a plain set, leaving each caller's
// policy where it is.

import type { Core } from "./schema.js";

/**
 * Every id reachable from `roots` by repeatedly following `edgesOf`, including the
 * roots themselves.
 *
 * Cycle-safe: a node is expanded at most once. Core graphs are supposed to be acyclic
 * and `wireStatementProofDependencies` actively refuses to introduce a cycle, but a
 * hand-authored proto edit can still produce one, and a walk that recurses forever on
 * it turns a bad edit into a hung pipeline rather than a diagnosable error.
 */
export function reachableFrom(roots: Iterable<string>, edgesOf: (id: string) => Iterable<string>): Set<string> {
  const seen = new Set<string>();
  const stack = [...roots];
  while (stack.length > 0) {
    const id = stack.pop() as string;
    if (seen.has(id)) continue;
    seen.add(id);
    for (const next of edgesOf(id)) if (!seen.has(next)) stack.push(next);
  }
  return seen;
}

/**
 * Every statement that depends on any of `targets`, transitively — the REVERSE
 * closure over `depends_on`.
 *
 * This is the blast radius of editing a node: exactly the statements whose proofs may
 * no longer hold. `targets` themselves are excluded from the result unless some other
 * statement reaches them, since an assumption or definition is not itself a proof
 * that needs redoing.
 */
export function dependentsOf(core: Core, targets: Iterable<string>): Set<string> {
  const targetSet = new Set(targets);
  // Reverse adjacency: dependency id -> statements naming it.
  const consumers = new Map<string, string[]>();
  for (const s of core.statements) {
    for (const dep of s.depends_on ?? []) {
      const list = consumers.get(dep);
      if (list) list.push(s.id);
      else consumers.set(dep, [s.id]);
    }
  }
  const reached = reachableFrom(targetSet, (id) => consumers.get(id) ?? []);
  for (const t of targetSet) reached.delete(t);
  return reached;
}
