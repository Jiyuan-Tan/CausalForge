// Deterministic D0 solver-context projection.
//
// Every solve unit receives its target neighborhood inline and a compact
// manifest for everything omitted. The complete, same-round core is available
// through a content-addressed snapshot path supplied by dispatch.ts when a unit
// discovers that its local job genuinely needs non-local context.
import { createHash } from "node:crypto";
import type {
  Core,
  CoreAssumption,
  CoreDefinition,
  CoreStatement,
  CoreSymbol,
} from "../core/schema.js";
import { stampDefinitionRevision, statementRevision } from "../core/revision.js";
import { extractNodeRefs } from "../core/node_ids.js";
import { normalizeSymbol } from "../core/preflight.js";

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
  mode: "projected";
  /** Transitive consumers of a target. Inspect them in the immutable snapshot
   * before changing a claim or dependency contract they consume. */
  affected_downstream_statement_ids: string[];
  omitted: {
    symbols: string[];
    assumptions: string[];
    definitions: string[];
    statements: string[];
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
    definitions: core.definitions.map((definition) => stampDefinitionRevision(definition, core)),
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
): FrozenCoreProjection {
  const statementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
  const assumptionById = new Map(core.assumptions.map((assumption) => [assumption.id, assumption] as const));
  const definitionById = new Map(core.definitions.map((definition) => [definition.id, definition] as const));
  const symbolByName = new Map(core.symbols.map((symbol) => [symbol.name, symbol] as const));
  // Preflight, apply, and G1 compare symbol names delimiter-normalized (`\(\eta\)` ≡
  // `\eta`); resolve declared/referenced names the same way so a spelling that
  // passes the gate cannot drop a declared symbol from the local view.
  const symbolByNormalizedName = new Map(core.symbols.map((symbol) => [normalizeSymbol(symbol.name), symbol] as const));
  const resolveSymbolName = (raw: string): string | undefined =>
    symbolByName.get(raw)?.name ?? symbolByNormalizedName.get(normalizeSymbol(raw))?.name;

  const statementIds = new Set(targetIds);
  const affectedDownstreamIds = new Set<string>();
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

  const assumptionIds = new Set<string>();
  const definitionIds = new Set<string>();
  const symbolNames = new Set<string>();
  const collectDeclaredSymbols = (freeSymbols: string[] | undefined): void => {
    if (freeSymbols !== undefined) {
      for (const name of freeSymbols) {
        const declared = resolveSymbolName(name);
        if (declared !== undefined) symbolNames.add(declared);
      }
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
  // `free_symbols` is warn-tier and legacy nodes may omit it. Conservatively
  // recover visibly used declarations from the authored text instead of paying
  // to inline the whole paper-wide symbol table in every local solve unit.
  // A one- or two-letter alphanumeric name (`n`, `p`, `X1`) occurs inside almost
  // any TeX string, which would silently re-inline the whole symbol table; match
  // those only as a standalone token (a following `_` subscript still counts).
  const occurs = (text: string, needle: string): boolean => {
    if (needle.length === 0) return false;
    if (needle.length > 2 || !/^[A-Za-z0-9]+$/.test(needle)) return text.includes(needle);
    return new RegExp(`(?<![A-Za-z0-9\\\\])${needle}(?![A-Za-z0-9])`).test(text);
  };
  const collectTextSymbols = (text: string): void => {
    for (const name of symbolByName.keys()) {
      if (occurs(text, name) || occurs(text, normalizeSymbol(name))) symbolNames.add(name);
    }
  };

  for (const statement of core.statements) {
    if (!statementIds.has(statement.id)) continue;
    for (const dependency of statement.depends_on) collectNodeId(dependency);
    collectDeclaredSymbols(statement.free_symbols);
    collectTextRefs(statement.statement);
    collectTextSymbols(statement.statement);
  }
  collectTextSymbols(core.target_estimand);
  if (core.estimand_functional !== undefined) collectTextSymbols(core.estimand_functional);

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
        const declaredInput = resolveSymbolName(input);
        if (declaredInput !== undefined) symbolNames.add(declaredInput);
      }
      collectDeclaredSymbols(definition.free_symbols);
      collectTextRefs(definition.construction);
      collectTextSymbols(definition.construction);
    }
    for (const id of [...assumptionIds]) {
      const assumption = assumptionById.get(id)!;
      collectDeclaredSymbols(assumption.free_symbols);
      collectTextRefs(assumption.condition);
      collectTextSymbols(assumption.condition);
    }
    // A declaration whose semantic `ref` points into this local closure is local
    // notation even when a legacy node forgot to declare it in `free_symbols`.
    for (const symbol of core.symbols) {
      if (symbol.ref !== undefined &&
        (statementIds.has(symbol.ref) || assumptionIds.has(symbol.ref) || definitionIds.has(symbol.ref))) {
        symbolNames.add(symbol.name);
      }
    }
    for (const name of [...symbolNames]) {
      const symbol = symbolByName.get(name)!;
      if (symbol.ref) collectNodeId(symbol.ref);
      for (const referencedName of symbol.refs ?? []) {
        const declaredRef = resolveSymbolName(referencedName);
        if (declaredRef !== undefined) symbolNames.add(declaredRef);
      }
    }
    const after = assumptionIds.size + definitionIds.size + symbolNames.size;
    catalogChanged = after !== before;
  }

  const symbols = core.symbols.filter((symbol) => symbolNames.has(symbol.name));
  const assumptions = core.assumptions.filter((assumption) => assumptionIds.has(assumption.id));
  const definitions = core.definitions
    .filter((definition) => definitionIds.has(definition.id))
    .map((definition) => stampDefinitionRevision(definition, core));
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
      mode: "projected",
      affected_downstream_statement_ids: core.statements
        .filter((statement) => affectedDownstreamIds.has(statement.id))
        .map((statement) => statement.id),
      omitted: {
        symbols: core.symbols.filter((symbol) => !symbolNames.has(symbol.name)).map((symbol) => symbol.name),
        assumptions: core.assumptions
          .filter((assumption) => !assumptionIds.has(assumption.id))
          .map((assumption) => assumption.id),
        definitions: core.definitions
          .filter((definition) => !definitionIds.has(definition.id))
          .map((definition) => definition.id),
        statements: core.statements
          .filter((statement) => !statementIds.has(statement.id))
          .map((statement) => statement.id),
      },
    },
  };
}
