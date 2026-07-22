/**
 * Deterministic post-Stage-3 lint: flag named hypotheses in a Lean theorem
 * signature that never appear in the corresponding proof body.
 *
 * Intent (see Stage 1.5 prompt §U): catch speculative assumptions the math
 * never needed. This module operates by textual scan of a Lean source file —
 * it does NOT invoke Lean. It is a fast first-pass triage; a hypothesis flagged
 * here should either be dropped (and the .tex / .md U-check re-run) or, if the
 * proof relies on it implicitly via a wildcard tactic, the wildcard tactic
 * itself should be replaced with an explicit `exact …` so the dependency is
 * auditable.
 *
 * Caveats:
 *  - The scan is name-based; tactics like `assumption`, `tauto`, `omega`,
 *    `linarith`, `aesop`, `simp [*]`, `simp_all` can close a goal using any
 *    in-scope hypothesis without naming it. When such tactics appear in the
 *    proof body, the finding is downgraded to `advisory` so the reviewer
 *    knows to confirm by trying to remove the hypothesis.
 *  - Proof bodies that are `sorry` / `admit` cannot meaningfully be linted;
 *    those theorems are skipped with `reason: "sorry-stub"`.
 */

export type LintSeverity = "definite" | "advisory" | "skip";

export interface UnusedHypothesisFinding {
  /** Theorem / lemma name. */
  theoremName: string;
  /** Hypothesis identifier as it appears in the binder. */
  hypothesisName: string;
  /** Severity: `definite` if no wildcard tactic could be using it implicitly. */
  severity: LintSeverity;
  /** 1-indexed source line of the declaration header. */
  declLine: number;
  /** Optional explanatory note (e.g. which wildcard tactic triggered advisory). */
  note?: string;
  /** True when the hypothesis is only forwarded to a bridge whose same parameter is unused. */
  transitive?: boolean;
  /** Bridge declaration that exposed the transitive unused hypothesis. */
  viaTheorem?: string;
}

export interface SkippedTheorem {
  theoremName: string;
  reason: "sorry-stub" | "no-proof-body" | "no-named-hypotheses";
  declLine: number;
}

export interface LintResult {
  findings: UnusedHypothesisFinding[];
  skipped: SkippedTheorem[];
  /** Total number of theorem/lemma/example declarations the lint inspected. */
  theoremsInspected: number;
}

interface Declaration {
  kind: string;
  name: string;
  /** Character offset of declaration header start. */
  start: number;
  /** Character offset of next top-level declaration (or end of source). */
  end: number;
}

interface InspectedDeclaration {
  name: string;
  isPrivate: boolean;
  declLine: number;
  names: string[];
  resultType: string;
  typeTexts: string[];
  body: string;
}

/**
 * Tactics that may consume any in-scope hypothesis without naming it. When the
 * proof body contains one of these, unused-hypothesis findings are downgraded
 * to `advisory`. Lint is name-based, so it cannot tell which specific
 * hypothesis the wildcard tactic actually used.
 */
const WILDCARD_TACTIC_RES: Array<{ re: RegExp; label: string }> = [
  { re: /\bassumption\b/, label: "assumption" },
  { re: /\btauto\b/, label: "tauto" },
  { re: /\bdecide\b/, label: "decide" },
  { re: /\bomega\b/, label: "omega" },
  { re: /\blinarith\b/, label: "linarith" },
  { re: /\bnlinarith\b/, label: "nlinarith" },
  { re: /\bpolyrith\b/, label: "polyrith" },
  { re: /\baesop\b/, label: "aesop" },
  { re: /\bsimp_all\b/, label: "simp_all" },
  { re: /\bsimp[^\n]*\[[^\]]*\*[^\]]*\]/, label: "simp [*]" },
  { re: /\bsolve_by_elim\b/, label: "solve_by_elim" },
  { re: /\bexact\?\B/, label: "exact?" },
  // `subst x` consumes an equation hypothesis about `x` without naming the
  // hypothesis. `cases'`/`rcases`/`obtain` typically DO name the consumed
  // hypothesis (it appears in the tactic text), so they're not wildcards.
  { re: /\bsubst\b/, label: "subst" },
  { re: /\bsubst_vars\b/, label: "subst_vars" },
];

const SORRY_RE = /\b(sorry|admit)\b/;

const TOP_LEVEL_DECL_RE =
  /^(?:(?:private|protected|noncomputable|@\[[^\]]*\])\s+)*(theorem|lemma|example|def)\b/gm;

/**
 * Replace Lean comments with spaces (preserving newlines) so character offsets
 * and line numbers are identical to the original source. Avoids false positives
 * in usage / wildcard scans from text inside docstrings.
 */
function stripComments(src: string): string {
  const chars = Array.from(src);
  let i = 0;
  while (i < chars.length) {
    if (chars[i] === "-" && chars[i + 1] === "-") {
      while (i < chars.length && chars[i] !== "\n") {
        chars[i] = " ";
        i++;
      }
    } else if (chars[i] === "/" && chars[i + 1] === "-") {
      let depth = 1;
      chars[i] = " "; chars[i + 1] = " ";
      i += 2;
      while (i < chars.length && depth > 0) {
        if (chars[i] === "/" && chars[i + 1] === "-") {
          depth++;
          chars[i] = " "; chars[i + 1] = " ";
          i += 2;
        } else if (chars[i] === "-" && chars[i + 1] === "/") {
          depth--;
          chars[i] = " "; chars[i + 1] = " ";
          i += 2;
        } else {
          if (chars[i] !== "\n") chars[i] = " ";
          i++;
        }
      }
    } else {
      i++;
    }
  }
  return chars.join("");
}

function findDeclarations(src: string): Declaration[] {
  const decls: Declaration[] = [];
  TOP_LEVEL_DECL_RE.lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = TOP_LEVEL_DECL_RE.exec(src)) !== null) {
    const headerEnd = m.index + m[0].length;
    // The identifier follows whitespace after the kind keyword.
    const tail = src.slice(headerEnd);
    const nameMatch = /^\s+([A-Za-z_][A-Za-z0-9_'\.]*)/.exec(tail);
    const name = nameMatch?.[1] ?? "<anonymous>";
    decls.push({ kind: m[1], name, start: m.index, end: src.length });
  }
  for (let k = 0; k < decls.length - 1; k++) decls[k].end = decls[k + 1].start;
  return decls;
}

/**
 * Split a declaration slice into (signature, body) at the depth-0 `:=` that
 * separates them, and further split the signature into (binders, resultType)
 * at the depth-0 `:` that ends the binder list. Returns null if no body is
 * present (e.g. axiom-like decls).
 */
function splitSignatureAndBody(
  slice: string,
): { binders: string; resultType: string; body: string } | null {
  let depth = 0;
  let sigEnd = -1;
  for (let i = 0; i < slice.length - 1; i++) {
    const c = slice[i];
    if (c === "(" || c === "[" || c === "{" || c === "⦃") depth++;
    else if (c === ")" || c === "]" || c === "}" || c === "⦄") depth--;
    else if (depth === 0 && c === ":" && slice[i + 1] === "=") {
      sigEnd = i;
      break;
    }
  }
  if (sigEnd < 0) return null;
  const signature = slice.slice(0, sigEnd);
  const body = slice.slice(sigEnd + 2);
  // Find the depth-0 `:` separating binders from the result type. This is
  // the FIRST top-level colon that is not part of `::` and not `:=`.
  depth = 0;
  let resultColon = -1;
  for (let i = 0; i < signature.length - 1; i++) {
    const c = signature[i];
    if (c === "(" || c === "[" || c === "{" || c === "⦃") depth++;
    else if (c === ")" || c === "]" || c === "}" || c === "⦄") depth--;
    else if (
      depth === 0 &&
      c === ":" &&
      signature[i + 1] !== "=" &&
      signature[i - 1] !== ":"
    ) {
      resultColon = i;
      break;
    }
  }
  const binders = resultColon >= 0 ? signature.slice(0, resultColon) : signature;
  const resultType = resultColon >= 0 ? signature.slice(resultColon + 1) : "";
  return { binders, resultType, body };
}

interface Binder {
  open: "(" | "{" | "[" | "⦃";
  inner: string;
}

/** Collect balanced binder groups between the theorem name and the result-type `:`. */
function parseBinders(signature: string): Binder[] {
  const nameRe =
    /^\s*(?:(?:private|protected|noncomputable|@\[[^\]]*\])\s+)*(?:theorem|lemma|example|def)\s+[A-Za-z_][A-Za-z0-9_'\.]*\b/;
  const nm = nameRe.exec(signature);
  if (!nm) return [];
  let i = nm[0].length;
  // Skip optional universe-parameter block `.{u v}`.
  while (i < signature.length && signature[i] === "." && signature[i + 1] === "{") {
    let d = 1;
    i += 2;
    while (i < signature.length && d > 0) {
      if (signature[i] === "{") d++;
      else if (signature[i] === "}") d--;
      i++;
    }
  }
  const binders: Binder[] = [];
  while (i < signature.length) {
    while (i < signature.length && /\s/.test(signature[i])) i++;
    if (i >= signature.length) break;
    const c = signature[i];
    let open: Binder["open"];
    let close: string;
    if (c === "(") { open = "("; close = ")"; }
    else if (c === "{") { open = "{"; close = "}"; }
    else if (c === "[") { open = "["; close = "]"; }
    else if (c === "⦃") { open = "⦃"; close = "⦄"; }
    else break; // hit the result-type `:` or some other token
    let d = 1;
    let j = i + 1;
    while (j < signature.length && d > 0) {
      if (signature[j] === open && open !== close) d++;
      else if (signature[j] === close) d--;
      j++;
    }
    binders.push({ open, inner: signature.slice(i + 1, j - 1) });
    i = j;
  }
  return binders;
}

/**
 * Extract named identifiers + the type-text portion of a binder. Skips `_`
 * and unnamed binders. The type text is everything after the depth-0 `:` that
 * separates names from type.
 */
function parseBinderContent(b: Binder): { names: string[]; typeText: string } {
  let depth = 0;
  let colonIdx = -1;
  for (let i = 0; i < b.inner.length; i++) {
    const c = b.inner[i];
    if (c === "(" || c === "{" || c === "[" || c === "⦃") depth++;
    else if (c === ")" || c === "}" || c === "]" || c === "⦄") depth--;
    else if (depth === 0 && c === ":" && b.inner[i + 1] !== "=" && b.inner[i - 1] !== ":") {
      colonIdx = i;
      break;
    }
  }
  if (colonIdx < 0) return { names: [], typeText: b.inner }; // positional/anonymous instance
  const namesStr = b.inner.slice(0, colonIdx).trim();
  const typeText = b.inner.slice(colonIdx + 1);
  if (!namesStr) return { names: [], typeText };
  const names = namesStr
    .split(/\s+/)
    .filter((n) => n && n !== "_" && /^[A-Za-z_][A-Za-z0-9_']*$/.test(n));
  return { names, typeText };
}

function lineOfOffset(src: string, offset: number): number {
  let line = 1;
  for (let i = 0; i < offset && i < src.length; i++) {
    if (src[i] === "\n") line++;
  }
  return line;
}

function escapeForRegex(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function isPrivateDeclaration(slice: string): boolean {
  return /^\s*private\b/.test(slice);
}

function isBridgeOnlyProof(body: string, bridgeName: string): boolean {
  const normalized = body.replace(/\s+/g, " ").trim();
  const re = new RegExp(`^by\\s+(?:exact|apply)\\s+${escapeForRegex(bridgeName)}\\b`);
  return re.test(normalized);
}

export function lintUnusedHypotheses(source: string): LintResult {
  const stripped = stripComments(source);
  const decls = findDeclarations(stripped);
  const findings: UnusedHypothesisFinding[] = [];
  const skipped: SkippedTheorem[] = [];
  const inspected: InspectedDeclaration[] = [];
  let theoremsInspected = 0;

  for (const decl of decls) {
    if (decl.kind !== "theorem" && decl.kind !== "lemma" && decl.kind !== "example") {
      continue; // skip `def` and other non-proof declarations
    }
    theoremsInspected++;
    const slice = stripped.slice(decl.start, decl.end);
    const split = splitSignatureAndBody(slice);
    const declLine = lineOfOffset(source, decl.start);
    if (!split) {
      skipped.push({ theoremName: decl.name, reason: "no-proof-body", declLine });
      continue;
    }
    const binders = parseBinders(split.binders);
    const names: string[] = [];
    const typeTexts: string[] = [];
    for (const b of binders) {
      const { names: ns, typeText } = parseBinderContent(b);
      typeTexts.push(typeText);
      for (const n of ns) {
        // Instance binders `[…]` whose only identifier is the conventional
        // `inst…` placeholder are rarely cited by name; skip them. Identifiers
        // the user *did* name (e.g. `[hMeas : Measurable f]`) are kept.
        if (b.open === "[" && /^_?inst/i.test(n)) continue;
        names.push(n);
      }
    }
    if (names.length === 0) {
      skipped.push({ theoremName: decl.name, reason: "no-named-hypotheses", declLine });
      continue;
    }
    if (SORRY_RE.test(split.body)) {
      skipped.push({ theoremName: decl.name, reason: "sorry-stub", declLine });
      continue;
    }
    inspected.push({
      name: decl.name,
      isPrivate: isPrivateDeclaration(slice),
      declLine,
      names,
      resultType: split.resultType,
      typeTexts,
      body: split.body,
    });
    const wildcardHit = WILDCARD_TACTIC_RES.find((w) => w.re.test(split.body));
    // A binder name is "used" if it appears in (a) the result type
    // [load-bearing for the statement], (b) any OTHER binder's type text
    // [load-bearing for a sibling hypothesis], or (c) the proof body. Only
    // flag if absent from all three. Note: a name trivially appears in its
    // own binder name list — we only check binder *types*, not the names.
    const usageScope =
      typeTexts.join("\n") + "\n" + split.resultType + "\n" + split.body;
    for (const name of names) {
      const re = new RegExp(`(?<![A-Za-z0-9_'])${escapeForRegex(name)}(?![A-Za-z0-9_'])`);
      if (re.test(usageScope)) continue;
      findings.push({
        theoremName: decl.name,
        hypothesisName: name,
        severity: wildcardHit ? "advisory" : "definite",
        declLine,
        note: wildcardHit
          ? `proof contains \`${wildcardHit.label}\`; hypothesis may be used implicitly`
          : undefined,
      });
    }
  }

  const directUnused = new Map<string, Map<string, UnusedHypothesisFinding>>();
  const alreadyFlagged = new Set<string>();
  for (const f of findings) {
    const byHyp = directUnused.get(f.theoremName) ?? new Map<string, UnusedHypothesisFinding>();
    byHyp.set(f.hypothesisName, f);
    directUnused.set(f.theoremName, byHyp);
    alreadyFlagged.add(`${f.theoremName}:${f.hypothesisName}`);
  }
  for (const caller of inspected) {
    if (caller.isPrivate) continue;
    for (const [bridgeName, bridgeFindings] of directUnused) {
      if (caller.name === bridgeName) continue;
      if (!isBridgeOnlyProof(caller.body, bridgeName)) continue;
      for (const [hypName, bridgeFinding] of bridgeFindings) {
        if (!caller.names.includes(hypName)) continue;
        if (alreadyFlagged.has(`${caller.name}:${hypName}`)) continue;
        const re = new RegExp(`(?<![A-Za-z0-9_'])${escapeForRegex(hypName)}(?![A-Za-z0-9_'])`);
        const nonBodyScope = caller.typeTexts.join("\n") + "\n" + caller.resultType;
        if (re.test(nonBodyScope)) continue;
        if (!re.test(caller.body)) continue;
        findings.push({
          theoremName: caller.name,
          hypothesisName: hypName,
          severity: bridgeFinding.severity,
          declLine: caller.declLine,
          transitive: true,
          viaTheorem: bridgeName,
          note: `only forwarded to \`${bridgeName}\`, where the same parameter is unused`,
        });
        alreadyFlagged.add(`${caller.name}:${hypName}`);
      }
    }
  }

  return { findings, skipped, theoremsInspected };
}

export function formatLintReport(result: LintResult): string {
  const lines: string[] = [];
  if (result.theoremsInspected === 0) return "no theorems found";
  if (result.findings.length === 0 && result.skipped.length === 0) {
    return `${result.theoremsInspected} theorem(s) inspected — no unused-hypothesis findings`;
  }
  const byTheorem = new Map<string, UnusedHypothesisFinding[]>();
  for (const f of result.findings) {
    const arr = byTheorem.get(f.theoremName) ?? [];
    arr.push(f);
    byTheorem.set(f.theoremName, arr);
  }
  for (const [thm, arr] of byTheorem) {
    lines.push(`theorem ${thm} (line ${arr[0].declLine}):`);
    for (const f of arr) {
      const sev = f.severity === "advisory" ? " [advisory]" : "";
      const transitive = f.transitive && f.viaTheorem ? ` [via ${f.viaTheorem}]` : "";
      const note = f.note ? `  — ${f.note}` : "";
      lines.push(`  - ${f.hypothesisName}${sev}${transitive}${note}`);
    }
  }
  if (result.skipped.length > 0) {
    lines.push("");
    lines.push("skipped:");
    for (const s of result.skipped) {
      lines.push(`  - ${s.theoremName} (line ${s.declLine}): ${s.reason}`);
    }
  }
  return lines.join("\n");
}
