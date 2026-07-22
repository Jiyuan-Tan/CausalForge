import { isUndeliveredNode, type FormalizationGraph, type Finding, type ValidationResult } from "./types.js";

/** Edges that constitute logical dependency (used for cycle detection). */
const DEP_KINDS = new Set(["statement-uses", "proof-uses"]);

function detectCycle(graph: FormalizationGraph): string[] | null {
  const adj = new Map<string, string[]>();
  for (const n of graph.nodes) adj.set(n.id, []);
  for (const e of graph.edges) {
    if (DEP_KINDS.has(e.kind) && adj.has(e.from)) adj.get(e.from)!.push(e.to);
  }
  const WHITE = 0,
    GRAY = 1,
    BLACK = 2;
  const color = new Map<string, number>(graph.nodes.map((n) => [n.id, WHITE]));
  const stack: string[] = [];
  let found: string[] | null = null;
  const dfs = (u: string): void => {
    if (found) return;
    color.set(u, GRAY);
    stack.push(u);
    for (const v of adj.get(u) ?? []) {
      if (!color.has(v)) continue;
      if (color.get(v) === GRAY) {
        found = stack.slice(stack.indexOf(v));
        return;
      }
      if (color.get(v) === WHITE) dfs(v);
      if (found) return;
    }
    stack.pop();
    color.set(u, BLACK);
  };
  for (const n of graph.nodes) if (color.get(n.id) === WHITE) dfs(n.id);
  return found;
}

export interface ValidateOpts {
  /** SUBSTRATE_DEBT entry names, for INV gate-ledger. Omit to skip that check. */
  substrateDebtNames?: string[];
  /** CITED_DEPENDENCIES entry names — a cited gate is recorded here, not in
   * SUBSTRATE_DEBT. A gate node is satisfied if it appears in EITHER ledger. */
  citedDependencyNames?: string[];
}

export function validate(graph: FormalizationGraph, opts: ValidateOpts = {}): ValidationResult {
  const findings: Finding[] = [];
  const nodeCounts = new Map<string, number>();
  for (const n of graph.nodes) nodeCounts.set(n.id, (nodeCounts.get(n.id) ?? 0) + 1);
  for (const [id, count] of nodeCounts) {
    if (count > 1) {
      findings.push({
        invariant: "schema",
        severity: "error",
        node: id,
        message: `duplicate node id ${id} appears ${count} times`,
      });
    }
  }
  const edgeCounts = new Map<string, number>();
  for (const e of graph.edges) {
    const key = `${e.kind}:${e.from}->${e.to}`;
    edgeCounts.set(key, (edgeCounts.get(key) ?? 0) + 1);
  }
  for (const [key, count] of edgeCounts) {
    if (count > 1) {
      findings.push({
        invariant: "schema",
        severity: "error",
        message: `duplicate edge ${key} appears ${count} times`,
      });
    }
  }
  const ids = new Set(graph.nodes.map((n) => n.id));

  // INV coverage: every from-note node must have a Lean link.
  for (const n of graph.nodes) {
    if (isUndeliveredNode(n)) {
      if (n.lean.decl_name !== null || n.lean.file !== null) {
        findings.push({
          invariant: "coverage",
          severity: "error",
          node: n.id,
          message: `undelivered node ${n.id} must not retain a Lean declaration or file anchor`,
        });
      }
      continue;
    }
    if (n.kind === "setup") continue;
    if (n.provenance === "from-note" && n.lean.decl_name === null) {
      findings.push({
        invariant: "coverage",
        severity: "error",
        node: n.id,
        message: `from-note node ${n.id} has no Lean link (missing -- @node: ${n.id} annotation?)`,
      });
    }
  }

  // INV edge-integrity: endpoints exist; no dependency cycle.
  for (const e of graph.edges) {
    if (!ids.has(e.from) || !ids.has(e.to)) {
      findings.push({
        invariant: "edge-integrity",
        severity: "error",
        message: `dangling edge ${e.from} -> ${e.to} (${e.kind})`,
      });
    }
  }
  const cycle = detectCycle(graph);
  if (cycle) {
    findings.push({
      invariant: "edge-integrity",
      severity: "error",
      message: `dependency cycle: ${cycle.join(" -> ")} -> ${cycle[0]}`,
    });
  }

  // INV setup-binding: every theorem has a setup-of edge into it.
  const setupTargets = new Set(graph.edges.filter((e) => e.kind === "setup-of").map((e) => e.to));
  for (const n of graph.nodes) {
    if (n.kind === "theorem" && !isUndeliveredNode(n) && !setupTargets.has(n.id)) {
      findings.push({
        invariant: "setup-binding",
        severity: "error",
        node: n.id,
        message: `theorem ${n.id} has no setup-of edge`,
      });
    }
  }

  // INV assumption-accounting: an assumption used by no node is a candidate dead hypothesis.
  const usedTargets = new Set(graph.edges.filter((e) => e.kind === "proof-uses").map((e) => e.to));
  for (const n of graph.nodes) {
    if (n.kind === "assumption" && !usedTargets.has(n.id)) {
      findings.push({
        invariant: "assumption-accounting",
        severity: "warn",
        node: n.id,
        message: `assumption ${n.id} is not used by any node (candidate dead hypothesis)`,
      });
    }
  }

  // INV gate-ledger: gate nodes ≡ a ledger entry (when a ledger is supplied). A
  // `gated` node lives in SUBSTRATE_DEBT, a `cited` node in CITED_DEPENDENCIES;
  // membership in EITHER satisfies the invariant.
  if (opts.substrateDebtNames || opts.citedDependencyNames) {
    const recorded = new Set([
      ...(opts.substrateDebtNames ?? []),
      ...(opts.citedDependencyNames ?? []),
    ]);
    for (const n of graph.nodes) {
      if (n.kind === "gate" && !recorded.has(n.id)) {
        findings.push({
          invariant: "gate-ledger",
          severity: "error",
          node: n.id,
          message: `gate ${n.id} is not recorded in SUBSTRATE_DEBT or CITED_DEPENDENCIES`,
        });
      }
    }
  }

  // INV note-faithfulness: a reviewed node (any non-unreviewed verdict) must carry
  // the statement hash it was reviewed at (internal consistency).
  for (const n of graph.nodes) {
    if (n.review.status !== "unreviewed" && n.review.passed_hash === null) {
      findings.push({
        invariant: "note-faithfulness",
        severity: "error",
        node: n.id,
        message: `node ${n.id} has review status ${n.review.status} without a passed_hash`,
      });
    }
  }

  return { ok: findings.every((f) => f.severity !== "error"), findings };
}
