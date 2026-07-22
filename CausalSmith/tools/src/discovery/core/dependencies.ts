import type { Core, CoreStatement } from "./schema.js";
import { extractNodeRefs } from "./node_ids.js";

/** Does a proof's authored/declared content closure touch any proposed mathematical
 * edit? Definition and assumption text are part of the walk: real cores sometimes
 * encode a nested `def:`/`ass:` reference in a construction rather than as a literal
 * `inputs` entry, and overlooking that edge can certify a proof against a definition
 * that the same round proposes changing. Used by the solve merge (same-round proof
 * deferral) and by apply (paired-proof promotion). */
export function proofContentClosureIntersects(args: {
  core: Core;
  node: CoreStatement;
  proofText?: string;
  changedIds: ReadonlySet<string>;
  extraStatements?: CoreStatement[];
}): boolean {
  const statementById = new Map<string, CoreStatement>([
    ...(args.extraStatements ?? []).map((statement) => [statement.id, statement] as const),
    ...args.core.statements.map((statement) => [statement.id, statement] as const),
    [args.node.id, args.node] as const,
  ]);
  const definitionById = new Map(args.core.definitions.map((definition) => [definition.id, definition] as const));
  const assumptionById = new Map(args.core.assumptions.map((assumption) => [assumption.id, assumption] as const));
  const seen = new Set<string>();
  const visitText = (text: string | undefined): boolean =>
    extractNodeRefs(text ?? "").some(visit);
  const visit = (id: string): boolean => {
    if (args.changedIds.has(id)) return true;
    if (seen.has(id)) return false;
    seen.add(id);
    const statement = statementById.get(id);
    if (statement) {
      return (statement.depends_on ?? []).some(visit) ||
        visitText(statement.statement) ||
        visitText(statement.source?.verbatim_statement);
    }
    const definition = definitionById.get(id);
    if (definition) {
      return [...(definition.inputs ?? []), ...(definition.by_member_properties ?? [])].some(visit) ||
        visitText(definition.construction) ||
        (definition.inputs ?? []).some(visitText);
    }
    const assumption = assumptionById.get(id);
    if (assumption) {
      return visitText(assumption.condition) || (assumption.free_symbols ?? []).some(visitText);
    }
    return false;
  };
  return visit(args.node.id) || visitText(args.proofText);
}

/** Add every literal, existing node citation in a claim or proof to the statement's
 * direct dependencies. This must run after OEQ replacement because replacement
 * theorems are assembled after the first solver-output wiring pass. */
export function wireStatementProofDependencies(core: Core): void {
  const allNodeIds = new Set([
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
    ...core.statements.map((s) => s.id),
  ]);
  const stmtIds = new Set(core.statements.map((s) => s.id));
  const depsById = new Map(core.statements.map((s) => [s.id, new Set(s.depends_on ?? [])] as const));
  /** Would adding `from → to` close a cycle? (i.e. is `from` already reachable from `to`?) */
  const wouldCycle = (from: string, to: string): boolean => {
    if (!stmtIds.has(to)) return false; // only statement→statement edges can cycle
    const seen = new Set<string>();
    const stack = [to];
    while (stack.length > 0) {
      const cur = stack.pop()!;
      if (cur === from) return true;
      if (seen.has(cur)) continue;
      seen.add(cur);
      for (const next of depsById.get(cur) ?? []) stack.push(next);
    }
    return false;
  };
  for (const statement of core.statements) {
    const dependencies = depsById.get(statement.id)!;
    for (const id of extractNodeRefs(`${statement.statement}\n${statement.proof_tex ?? ""}`)) {
      if (id === statement.id || !allNodeIds.has(id)) continue;
      // Prose citation is a WEAK signal — "the dual of lem:a" in lem:a's own counterpart
      // is a mention, not a dependency. Since this pass now matches case-insensitively
      // and includes `oeq:`, it discovers strictly more citations than before, and a
      // mutual pair of prose mentions would introduce a cycle that gate.ts reports as a
      // G4 violation on a core that previously passed. An inferred edge is never worth
      // breaking the graph over: skip it and leave the explicit `depends_on` authoritative.
      if (wouldCycle(statement.id, id)) continue;
      dependencies.add(id);
    }
    statement.depends_on = [...dependencies];
  }
}

/** Rebuild assumption reverse edges from the FINAL graph. Class definitions
 * declare membership structurally; constructed definitions may also cite an
 * assumption id literally in their formula (for example a target-law premise).
 * Both are direct definition consumers, alongside statement depends_on edges. */
export function rebuildAssumptionUsedBy(core: Core): void {
  const directUsers = new Map(core.assumptions.map((a) => [a.id, new Set<string>()] as const));
  for (const statement of core.statements) {
    for (const dependency of statement.depends_on ?? []) directUsers.get(dependency)?.add(statement.id);
  }
  for (const definition of core.definitions) {
    for (const dependency of definition.by_member_properties ?? []) directUsers.get(dependency)?.add(definition.id);
    for (const input of definition.inputs ?? []) {
      for (const cited of extractNodeRefs(input)) directUsers.get(cited)?.add(definition.id);
    }
    for (const cited of extractNodeRefs(definition.construction)) directUsers.get(cited)?.add(definition.id);
  }
  for (const assumption of core.assumptions) {
    const users = [...(directUsers.get(assumption.id) ?? [])].sort();
    if (users.length === 0) delete assumption.used_by;
    else assumption.used_by = users;
  }
}
