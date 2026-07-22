import { isUndeliveredNode, type FormalizationGraph } from "./types.js";

const DEP_KINDS = new Set(["statement-uses", "proof-uses"]);

export interface ReviewTargets {
  /** Frozen (from-note) theorem nodes, dirty → re-check NL↔Lean statement equivalence. */
  statementTargets: string[];
  /** Assumption nodes that lie in some frozen theorem's uses-closure AND are dirty/unreviewed
   *  → re-check faithfulness (faithful/regularity/substrate-gate/content-gate). Dependency-
   *  scoped so a crux laundered onto a HELPER (not a theorem) is still caught. */
  assumptionTargets: string[];
  /** `from-note` definition nodes (paper-originated objects), dirty/unreviewed → re-check the
   *  Lean def faithfully encodes its `.tex` definition. NOT closure-gated: a from-tex def reached
   *  only through a lemma (never the frozen theorem's statement) would otherwise escape review,
   *  yet a drifted def silently changes the meaning of every statement built on it. `library`
   *  (imported/standard) and `agent-introduced` (scaffolding) defs stay out — the latter are
   *  caught transitively when a from-note statement that uses them is judged. */
  definitionTargets: string[];
  /** `from-note` LEMMA nodes (paper-originated lemmas the note declares as `L-k` blocks and that
   *  render as `lemmav` envs). Judged exactly like statements/definitions: NOT closure-gated, since
   *  a from-note lemma is a paper claim a reader relies on, and a mis-anchored / over-claimed lemma
   *  (the l3-style "oracle mean identity" anchored to a drift lemma) silently ships an unfaithful
   *  statement. `agent-introduced` helper lemmas stay out (frozen=false, not in paper). */
  lemmaTargets: string[];
  /** Nodes intentionally omitted from Lean delivery. These are NOT statement/proof targets: F4
   *  independently audits that each omission is genuinely secondary (or a cited node), is neither
   *  a headline nor headline-support, and has no delivered consumer. Kept out of delta/F2.5 so an
   *  omission cannot be mistaken for a dirty Lean declaration and routed back to scaffolding. */
  deliveryTargets: string[];
}

/** uses-closure (statement-uses + proof-uses, transitive) of every frozen theorem. */
function frozenUsesClosure(graph: FormalizationGraph): Set<string> {
  const adj = new Map<string, string[]>();
  for (const e of graph.edges) {
    if (!DEP_KINDS.has(e.kind)) continue;
    if (!adj.has(e.from)) adj.set(e.from, []);
    adj.get(e.from)!.push(e.to);
  }
  const closure = new Set<string>();
  for (const n of graph.nodes) {
    if (n.kind !== "theorem" || n.provenance !== "from-note" || isUndeliveredNode(n)) continue;
    const stack = [n.id];
    while (stack.length) {
      const cur = stack.pop()!;
      for (const v of adj.get(cur) ?? []) {
        if (!closure.has(v)) {
          closure.add(v);
          stack.push(v);
        }
      }
    }
  }
  return closure;
}

/**
 * Compute what the unified reviewer must judge this iteration, from the graph + the
 * dirty frontier: frozen-theorem statement drift, and new/changed assumptions in any
 * frozen theorem's uses-closure.
 */
export function reviewTargets(graph: FormalizationGraph, dirty: string[]): ReviewTargets {
  const dirtySet = new Set(dirty);
  const closure = frozenUsesClosure(graph);
  // A target needs review if its statement changed (dirty) OR it is not yet cleared. A node
  // flagged `drift` (or never reviewed) must stay in scope until it is `matched`/`derived` —
  // otherwise a drift whose hash didn't change since the last pass would silently slip the gate.
  const needsReview = (id: string, status: string) =>
    dirtySet.has(id) || (status !== "matched" && status !== "derived");
  const statementTargets: string[] = [];
  const assumptionTargets: string[] = [];
  const definitionTargets: string[] = [];
  const lemmaTargets: string[] = [];
  const deliveryTargets: string[] = [];
  for (const n of graph.nodes) {
    if (isUndeliveredNode(n)) continue;
    if (n.kind === "theorem" && n.provenance === "from-note" && needsReview(n.id, n.review.status)) {
      statementTargets.push(n.id);
    }
    if (n.kind === "assumption" && closure.has(n.id) && needsReview(n.id, n.review.status)) {
      assumptionTargets.push(n.id);
    }
    // A `cited` gate is reviewed in the assumption tier (its source-match). NOT closure-gated:
    // even an isolated/supportive comparator (consumed by nobody) must have its def verified
    // against the cited source.
    if (n.kind === "gate" && n.gate?.gate_class === "cited" && needsReview(n.id, n.review.status)) {
      assumptionTargets.push(n.id);
    }
    if (n.kind === "definition" && n.provenance === "from-note" && needsReview(n.id, n.review.status)) {
      definitionTargets.push(n.id);
    }
    if (n.kind === "lemma" && n.provenance === "from-note" && needsReview(n.id, n.review.status)) {
      lemmaTargets.push(n.id);
    }
  }
  return { statementTargets, assumptionTargets, definitionTargets, lemmaTargets, deliveryTargets };
}

/**
 * The FULL faithfulness surface for the final dual-model convergence review (old F4): EVERY frozen
 * theorem + EVERY assumption in its uses-closure + EVERY from-tex definition — UNCONDITIONALLY, i.e.
 * ignoring dirty/matched. The convergence gate must independently re-verify the headline claims with
 * both models even when single-model delta reviews already marked them matched; gating it on the
 * incremental `needsReview` would make it run vacuously (empty targets) in the happy path.
 */
export function convergenceTargets(graph: FormalizationGraph): ReviewTargets {
  const closure = frozenUsesClosure(graph);
  const statementTargets: string[] = [];
  const assumptionTargets: string[] = [];
  const definitionTargets: string[] = [];
  const lemmaTargets: string[] = [];
  const deliveryTargets: string[] = [];
  for (const n of graph.nodes) {
    if (isUndeliveredNode(n)) {
      deliveryTargets.push(n.id);
      continue;
    }
    if (n.kind === "theorem" && n.provenance === "from-note") statementTargets.push(n.id);
    else if (n.kind === "assumption" && closure.has(n.id)) assumptionTargets.push(n.id);
    else if (n.kind === "gate" && n.gate?.gate_class === "cited") assumptionTargets.push(n.id);
    else if (n.kind === "definition" && n.provenance === "from-note") definitionTargets.push(n.id);
    else if (n.kind === "lemma" && n.provenance === "from-note") lemmaTargets.push(n.id);
  }
  return { statementTargets, assumptionTargets, definitionTargets, lemmaTargets, deliveryTargets };
}

/**
 * Incremental review scope for SETUP/ENVIRONMENT symbol clusters (the `sym:<symbol>` tier), the
 * symbol-level analogue of `reviewTargets`. Symbols are not graph nodes, so their prior verdict +
 * cluster hash are carried on `graph.symbolReview` instead of `node.review`. A `delta` pass reviews
 * only symbols that are NEW (no prior entry), previously non-passing (drift), or whose cluster hash
 * CHANGED since the last pass (e.g. the scaffolder added an `@realizes` tag) — skipping
 * matched/untagged-and-unchanged symbols so it does not re-spend model calls on already-cleared
 * symbols. `convergence` (final F4 gate) reviews EVERY symbol unconditionally. `isPass` classifies a
 * stored verdict string (passed in to avoid a dependency on the reviewer's verdict vocabulary).
 */
export function incrementalSymbolRows<T extends { id: string; hash: string }>(
  built: T[],
  priorSym: Record<string, { verdict: string; hash: string }> | undefined,
  mode: "delta" | "convergence",
  isPass: (verdict: string) => boolean,
): T[] {
  if (mode === "convergence") return built;
  const prior = priorSym ?? {};
  return built.filter((s) => {
    const prev = prior[s.id];
    return !(prev && prev.hash === s.hash && isPass(prev.verdict));
  });
}
