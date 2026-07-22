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
}): PreflightViolation[] {
  const declared = new Set<string>();
  for (const s of core.symbols ?? []) {
    for (const raw of [s.name, s.symbol]) {
      if (typeof raw !== "string") continue;
      declared.add(normalizeSymbol(raw));
    }
  }
  const violations: PreflightViolation[] = [];
  for (const node of [...(core.assumptions ?? []), ...(core.definitions ?? [])]) {
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
 *  `t_\pi` compare equal. */
function normalizeSymbol(raw: string): string {
  return raw
    .trim()
    .replace(/^\\\(|\\\)$/g, "")
    .replace(/^\$+|\$+$/g, "")
    .trim();
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
