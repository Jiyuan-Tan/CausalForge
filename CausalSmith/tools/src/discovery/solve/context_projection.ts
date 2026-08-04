// Deterministic D0 solver-context projection.
//
// Ordinary solve units receive the target neighborhood inline and a compact
// manifest for everything omitted. The complete, same-round core is available
// through a content-addressed snapshot path supplied by dispatch.ts. A unit that
// owns paper-wide prose or cross-cutting structured edits keeps the full inline
// view because its work is intentionally non-local.
import { createHash } from "node:crypto";
import type {
  Core,
  CoreAssumption,
  CoreDefinition,
  CoreStatement,
  CoreSymbol,
} from "../core/schema.js";
import {
  definitionRevision,
  stampDefinitionRevision,
  statementRevision,
} from "../core/revision.js";
import { extractNodeRefs } from "../core/node_ids.js";

type FrozenStatement = Pick<CoreStatement, "id" | "kind" | "statement" | "depends_on"> & {
  revision: string;
};

export interface FrozenCoreInlineView {
  symbols: CoreSymbol[];
  assumptions: CoreAssumption[];
  definitions: Array<CoreDefinition & { revision: string }>;
  target_estimand: string;
  estimand_functional?: string;
  statements: FrozenStatement[];
}

export interface FrozenCoreOmissionManifest {
  mode: "full" | "projected";
  /** Transitive consumers of a target. Their ids/revisions remain in `omitted`
   * unless independently required upstream; inspect them before a change that
   * could alter their claim or dependency contract. */
  affected_downstream_statement_ids: string[];
  included: {
    symbols: string[];
    assumptions: string[];
    definitions: string[];
    statements: string[];
  };
  omitted: {
    symbols: string[];
    assumptions: string[];
    definitions: Array<{ id: string; revision: string }>;
    statements: Array<{
      id: string;
      kind: CoreStatement["kind"];
      depends_on: string[];
      revision: string;
    }>;
  };
}

export interface FrozenCoreProjection {
  inline: FrozenCoreInlineView;
  manifest: FrozenCoreOmissionManifest;
}

const frozenStatement = (statement: CoreStatement): FrozenStatement => ({
  id: statement.id,
  kind: statement.kind,
  statement: statement.statement,
  depends_on: statement.depends_on,
  revision: statementRevision(statement),
});

/** Complete content-addressed snapshot payload. Unlike the inline formal view,
 * this retains prose, sources, bibliography, and proof bytes for selective reads. */
export function frozenCoreSnapshot(core: Core): object {
  return {
    ...core,
    definitions: core.definitions.map((definition) => stampDefinitionRevision(definition)),
    statements: core.statements.map((statement) => ({
      ...statement,
      revision: statementRevision(statement),
    })),
  };
}

export function serializeFrozenCoreSnapshot(core: Core): { bytes: string; sha256: string } {
  const bytes = JSON.stringify(frozenCoreSnapshot(core), null, 2) + "\n";
  return { bytes, sha256: createHash("sha256").update(bytes).digest("hex") };
}

/** Select a target's upstream statement neighborhood and its catalog/symbol
 * closure. Downstream consumers are named in the manifest rather than copied
 * inline; the worker can inspect precisely those nodes if a proposed change
 * could affect them. */
export function projectFrozenCore(
  core: Core,
  targetIds: ReadonlySet<string>,
  full: boolean,
): FrozenCoreProjection {
  const statementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
  const assumptionById = new Map(core.assumptions.map((assumption) => [assumption.id, assumption] as const));
  const definitionById = new Map(core.definitions.map((definition) => [definition.id, definition] as const));
  const symbolByName = new Map(core.symbols.map((symbol) => [symbol.name, symbol] as const));

  const statementIds = full ? new Set(statementById.keys()) : new Set(targetIds);
  const affectedDownstreamIds = new Set<string>();
  if (!full) {
    // Upstream dependency closure.
    const queue = [...statementIds];
    while (queue.length > 0) {
      const statement = statementById.get(queue.pop()!);
      if (!statement) continue;
      for (const dependency of statement.depends_on) {
        if (!statementById.has(dependency) || statementIds.has(dependency)) continue;
        statementIds.add(dependency);
        queue.push(dependency);
      }
    }
    // A changed target can invalidate every transitive consumer. Name that
    // closure explicitly in the manifest without paying to inline every branch.
    const downstreamFrontier = new Set(targetIds);
    let changed = true;
    while (changed) {
      changed = false;
      for (const statement of core.statements) {
        if (downstreamFrontier.has(statement.id)) continue;
        if (statement.depends_on.some((dependency) => downstreamFrontier.has(dependency))) {
          downstreamFrontier.add(statement.id);
          affectedDownstreamIds.add(statement.id);
          changed = true;
        }
      }
    }
  }

  const assumptionIds = new Set<string>();
  const definitionIds = new Set<string>();
  const symbolNames = new Set<string>();
  // Symbol declarations are small and `free_symbols` drift is deliberately only
  // warn-tier in production: a present declaration can still be incomplete.
  // Therefore every projected view carries the complete symbol table. Trusting
  // only declared names here would make projection stricter than the gate and
  // silently omit a symbol that visibly occurs in an included condition/claim.
  const includeAllSymbols = true;

  const collectDeclaredSymbols = (freeSymbols: string[] | undefined): void => {
    if (freeSymbols !== undefined) {
      for (const name of freeSymbols) if (symbolByName.has(name)) symbolNames.add(name);
    }
  };
  const collectNodeId = (id: string): void => {
    if (assumptionById.has(id)) assumptionIds.add(id);
    if (definitionById.has(id)) definitionIds.add(id);
  };
  // Literal `def:`/`ass:` references inside TeX bodies are real dependency edges
  // (definition ordering already treats them as such), so an included node's text
  // must pull its cited catalog nodes inline rather than leaving them to a
  // snapshot lookup the worker may skip.
  const collectTextRefs = (text: string): void => {
    for (const ref of extractNodeRefs(text)) collectNodeId(ref);
  };

  for (const statement of core.statements) {
    if (!statementIds.has(statement.id)) continue;
    for (const dependency of statement.depends_on) collectNodeId(dependency);
    collectDeclaredSymbols(statement.free_symbols);
    collectTextRefs(statement.statement);
  }

  // Definitions can pull in member-property assumptions and symbols; symbols
  // can point back to definitions. Iterate to a fixed point.
  let catalogChanged = true;
  while (catalogChanged) {
    const before = assumptionIds.size + definitionIds.size + symbolNames.size;
    for (const id of [...definitionIds]) {
      const definition = definitionById.get(id)!;
      for (const property of definition.by_member_properties ?? []) collectNodeId(property);
      for (const input of definition.inputs ?? []) {
        collectNodeId(input);
        if (symbolByName.has(input)) symbolNames.add(input);
      }
      collectDeclaredSymbols(definition.free_symbols);
      collectTextRefs(definition.construction);
    }
    for (const id of [...assumptionIds]) {
      const assumption = assumptionById.get(id)!;
      collectDeclaredSymbols(assumption.free_symbols);
      collectTextRefs(assumption.condition);
    }
    if (includeAllSymbols) for (const name of symbolByName.keys()) symbolNames.add(name);
    for (const name of [...symbolNames]) {
      const symbol = symbolByName.get(name)!;
      if (symbol.ref) collectNodeId(symbol.ref);
      for (const referencedName of symbol.refs ?? []) {
        if (symbolByName.has(referencedName)) symbolNames.add(referencedName);
      }
    }
    const after = assumptionIds.size + definitionIds.size + symbolNames.size;
    catalogChanged = after !== before;
  }

  if (full) {
    for (const id of assumptionById.keys()) assumptionIds.add(id);
    for (const id of definitionById.keys()) definitionIds.add(id);
    for (const name of symbolByName.keys()) symbolNames.add(name);
  }

  const symbols = core.symbols.filter((symbol) => symbolNames.has(symbol.name));
  const assumptions = core.assumptions.filter((assumption) => assumptionIds.has(assumption.id));
  const definitions = core.definitions
    .filter((definition) => definitionIds.has(definition.id))
    .map((definition) => stampDefinitionRevision(definition));
  const statements = core.statements
    .filter((statement) => statementIds.has(statement.id))
    .map(frozenStatement);

  return {
    inline: {
      symbols,
      assumptions,
      definitions,
      target_estimand: core.target_estimand,
      ...(core.estimand_functional !== undefined ? { estimand_functional: core.estimand_functional } : {}),
      statements,
    },
    manifest: {
      mode: full ? "full" : "projected",
      affected_downstream_statement_ids: full
        ? []
        : core.statements
            .filter((statement) => affectedDownstreamIds.has(statement.id))
            .map((statement) => statement.id),
      included: {
        symbols: symbols.map((symbol) => symbol.name),
        assumptions: assumptions.map((assumption) => assumption.id),
        definitions: definitions.map((definition) => definition.id),
        statements: statements.map((statement) => statement.id),
      },
      omitted: {
        symbols: core.symbols.filter((symbol) => !symbolNames.has(symbol.name)).map((symbol) => symbol.name),
        assumptions: core.assumptions
          .filter((assumption) => !assumptionIds.has(assumption.id))
          .map((assumption) => assumption.id),
        definitions: core.definitions
          .filter((definition) => !definitionIds.has(definition.id))
          .map((definition) => ({ id: definition.id, revision: definitionRevision(definition) })),
        statements: core.statements
          .filter((statement) => !statementIds.has(statement.id))
          .map((statement) => ({
            id: statement.id,
            kind: statement.kind,
            depends_on: statement.depends_on,
            revision: statementRevision(statement),
          })),
      },
    },
  };
}
