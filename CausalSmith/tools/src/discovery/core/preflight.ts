// Deterministic preflight checks — structural rules that were being enforced by an
// expensive model AFTER a full solve round, instead of by a set operation before one.
//
// This check is transcribed from a real failure on the 2026-07-18
// stat_cot_observational_efficiency run:
//
//   round 36  FAIL at the post-solve G1 gate: `ass:holder-propensity` declared free
//             symbols `t_π` and `L_π` that are absent from `proto_core.symbols`. Found
//             after a complete solve round had already been paid for.
//
// It needed no model: it is a membership test.

export interface PreflightViolation {
  check: string;
  detail: string;
  ids: string[];
}

/** Every free symbol named by an assumption/definition must be a declared symbol.
 *
 *  This is the G1 gate's rule, hoisted to run BEFORE dispatch. Running it only after
 *  the solve means a round's entire cost is spent and then discarded over a missing
 *  symbol-table row. Matching is on the declared symbol's own name AND its rendered
 *  form, because cores declare symbols in both plain (`t_\pi`) and delimited
 *  (`\(t_\pi\)`) styles. */
export function checkSymbolDeclarations(core: {
  symbols?: Array<{ name?: string; symbol?: string }>;
  assumptions?: Array<{ id?: string; free_symbols?: string[] }>;
  definitions?: Array<{ id?: string; free_symbols?: string[] }>;
  statements?: Array<{ id?: string; free_symbols?: string[] }>;
}): PreflightViolation[] {
  const declared = new Set<string>();
  for (const s of core.symbols ?? []) {
    for (const raw of [s.name, s.symbol]) {
      if (typeof raw !== "string") continue;
      declared.add(normalizeSymbol(raw));
    }
  }
  const violations: PreflightViolation[] = [];
  // Statements joined this check when they gained `free_symbols`: an UNRESOLVABLE
  // declaration is worse on a statement than on an assumption, because the invalidation
  // scope reads it as the complete list of symbols the claim rests on — a name that
  // matches no symbol contributes nothing and the real symbol goes unwatched.
  for (const node of [...(core.assumptions ?? []), ...(core.definitions ?? []), ...(core.statements ?? [])]) {
    const missing = (node.free_symbols ?? [])
      .filter((sym) => typeof sym === "string")
      .filter((sym) => !declared.has(normalizeSymbol(sym)));
    if (missing.length > 0) {
      violations.push({
        check: "symbol-declaration",
        detail:
          `${node.id ?? "<unnamed>"} names free symbol(s) absent from the symbol table: ${missing.join(", ")}. ` +
          `Declare them in symbols[] before dispatching a solve round.`,
        ids: [node.id ?? "<unnamed>"],
      });
    }
  }
  return violations;
}

/** Strip the `\( \)` / `$ $` delimiters and surrounding space so `\(t_\pi\)` and
 *  `t_\pi` compare equal. Exported because symbol invalidation
 *  (`d0_working.declaredSymbolScope`) must compare a node's declared `free_symbols`
 *  against `symbols[].name` under exactly this equality — cores really do declare the
 *  same symbol in both styles, and a delimiter-only mismatch there would silently
 *  UNDER-invalidate. */
export function normalizeSymbol(raw: string): string {
  return raw
    .trim()
    .replace(/^\\\(|\\\)$/g, "")
    .replace(/^\$+|\$+$/g, "")
    .trim();
}

/** ADVISORY (warn-tier) counterpart to `checkSymbolDeclarations`: a symbol whose name
 *  occurs in a node's own TEXT but is missing from that node's `free_symbols`.
 *
 *  Why this exists: `free_symbols` is now the edge that scopes symbol invalidation
 *  (`d0_working.declaredSymbolScope`). An under-declared node keeps a proof of a claim
 *  whose symbol was re-defined underneath it, and nothing else in the pipeline looks at
 *  the declaration, so it can rot unobserved.
 *
 *  Why WARN and not HARD. Text matching is the very thing the invalidation path refuses
 *  to rely on, and it was measured against ground truth before this check was written:
 *  over all 1186 declaring assumptions in the 112 real cores under
 *  doc/research/{active,_bank}, a boundary-anchored scan disagrees with the author's own
 *  declaration on 1062 symbol/node pairs (43.6% of assumptions flag at least once) — and
 *  in the other direction 809 genuinely-declared symbols never appear literally in the
 *  condition text (`N`, `T` bound an index range that is written only as `\sum_i`). The
 *  filters below (drop 1-character names, drop a hit that is a sub- or super-string of
 *  something already declared, e.g. `Y_it` under a declared `Y_it(d)`) cut that to 277
 *  pairs / 10.1% of assumptions. A gate that rejects one in ten CORRECT nodes is not a
 *  gate; it would spend the D0 round budget the scoping is meant to save. So: report it,
 *  never block on it. Only nodes that DO declare are scanned — an undeclared node is
 *  already handled fail-safe by the invalidation path, and warning on all of them would
 *  bury the signal under every legacy core. */
export function checkSymbolDeclarationDrift(core: {
  symbols?: Array<{ name?: string; symbol?: string }>;
  assumptions?: Array<{ id?: string; condition?: string; free_symbols?: string[] }>;
  definitions?: Array<{ id?: string; construction?: string; free_symbols?: string[] }>;
  statements?: Array<{ id?: string; statement?: string; free_symbols?: string[] }>;
}): PreflightViolation[] {
  const names = new Set<string>();
  for (const s of core.symbols ?? []) {
    for (const raw of [s.name, s.symbol]) {
      if (typeof raw !== "string") continue;
      const n = normalizeSymbol(raw);
      // Single characters match ordinary English prose ("bounded" contains `d`), which
      // is exactly the unsoundness that disqualified mention-based invalidation.
      if (n.length >= 2) names.add(n);
    }
  }
  const nodes: Array<{ id?: string; text?: string; free_symbols?: string[] }> = [
    ...(core.assumptions ?? []).map((a) => ({ id: a.id, text: a.condition, free_symbols: a.free_symbols })),
    ...(core.definitions ?? []).map((d) => ({ id: d.id, text: d.construction, free_symbols: d.free_symbols })),
    ...(core.statements ?? []).map((s) => ({ id: s.id, text: s.statement, free_symbols: s.free_symbols })),
  ];
  const violations: PreflightViolation[] = [];
  for (const node of nodes) {
    if (!Array.isArray(node.free_symbols)) continue; // never declared — fail-safe already
    if (typeof node.text !== "string" || node.text.length === 0) continue;
    const declared = new Set(node.free_symbols.filter((s) => typeof s === "string").map(normalizeSymbol));
    const undeclared = [...names].filter((n) => {
      if (declared.has(n)) return false;
      // `Y_it` inside a declared `Y_it(d)` (or vice versa) is the same object written at
      // a different arity, not a missing declaration.
      if ([...declared].some((d) => d.includes(n) || n.includes(d))) return false;
      return mentionsSymbol(node.text as string, n);
    });
    if (undeclared.length > 0) {
      violations.push({
        check: "symbol-declaration-drift",
        detail:
          `${node.id ?? "<unnamed>"} mentions symbol(s) it does not declare in free_symbols: ${undeclared.join(", ")}. ` +
          `free_symbols scopes symbol invalidation — an undeclared symbol can be re-defined under this node ` +
          `without reopening its proof. ADVISORY: text matching is approximate, so verify before editing.`,
        ids: [node.id ?? "<unnamed>"],
      });
    }
  }
  return violations;
}

/** Boundary-anchored literal occurrence of `name` in `text`. `\\` is excluded from the
 *  left boundary class so `\eta` does not match inside `\theta`'s tail. */
function mentionsSymbol(text: string, name: string): boolean {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(`(^|[^A-Za-z0-9_\\\\])${escaped}(?![A-Za-z0-9_])`).test(text);
}

/** Accepts the registry's GateViolation rows (whose `detail` is already
 *  `[check] detail`), producing the same text as the original struct-based
 *  formatter did. */
export function formatPreflightViolations(violations: Array<{ detail: string }>): string {
  return [
    `D0 preflight failed with ${violations.length} deterministic violation(s). These are structural rules, ` +
      `not mathematical judgments — no solve round or adjudication is needed to resolve them.`,
    ...violations.map((v) => `  ${v.detail}`),
  ].join("\n");
}
