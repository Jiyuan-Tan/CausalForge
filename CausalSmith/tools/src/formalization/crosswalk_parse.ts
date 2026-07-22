// F2.5 tex↔Lean crosswalk — parse layer: deterministic .md block parsing and
// Lean declaration scanning/primitives, consumed by crosswalk_semantics.ts and
// crosswalk.ts. See crosswalk.ts for the module-level design note.

import { existsSync } from "node:fs";
import { readFile, readdir } from "node:fs/promises";
import path from "node:path";
import { isPaperTmpPath } from "../paths.js";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";
import type { CrosswalkEntry } from "../types.js";

// ---------------------------------------------------------------------------
// .md parsing
// ---------------------------------------------------------------------------

/** Options shared by the parsers / builder. `includeLemmas` switches on the
 *  full-mode F5 behavior (L-blocks + Lean `lemma` decls). */
export interface CrosswalkOpts {
  includeLemmas?: boolean;
}

interface MdBlock {
  objId: string; // normalized: "P-10", "P-1b", "T-1", "L-7"
  kind: CrosswalkEntry["kind"];
  title: string;
  texLineRange: string;
  texLabel: string;
}

/**
 * Parse the F1 .md for P-/T-/L- block headers (`### P-10. <title>`, `### T-1. …`,
 * `### L-7. …`). `kind`: T-* → theorem; L-* → lemma (or proposition when the
 * title says so); P-* → assumption when the title marks it a "(P-form of A_n)" /
 * assumption encoding, else definition. `texLabel` is the quoted ".tex line range"
 * string if present (durable anchor), else the title; `texLineRange` is the raw
 * field text (convenience). L-blocks are emitted unconditionally and filtered by
 * the builder when `includeLemmas` is off.
 */
export async function parseMdBlocks(mdPath: string): Promise<MdBlock[]> {
  if (!existsSync(mdPath)) return [];
  const lines = (await readFile(mdPath, "utf8")).split(/\r?\n/);
  const headerRe = /^#{2,4}\s+(P-\d+[a-z]?|T-\d+|L-\d+[a-z]?)\.\s*(.*)$/;
  const blocks: MdBlock[] = [];
  type Region = { objId: string; title: string; body: string[] };
  let cur: Region | null = null;
  const flush = () => {
    if (!cur) return;
    const bodyText = cur.body.join("\n");
    const title = cur.title.trim().replace(/\.$/, "");
    const isThm = cur.objId.startsWith("T-");
    const isLem = cur.objId.startsWith("L-");
    const isProp = /\bproposition\b/i.test(title);
    const isAssumption = /\(P-form of\s+A\d|\bassumption\b/i.test(title);
    const kind: CrosswalkEntry["kind"] = isThm
      ? "theorem"
      : isLem
        ? isProp
          ? "proposition"
          : "lemma"
        : isAssumption
          ? "assumption"
          : "definition";
    const texFieldMatch = bodyText.match(/\*\*\.tex line range\.\*\*\s*([^\n]*)/i);
    const texLineRange = (texFieldMatch?.[1] ?? "").trim();
    const quoted = texLineRange.match(/"([^"]+)"/);
    blocks.push({ objId: cur.objId, kind, title, texLineRange, texLabel: quoted?.[1] ?? title });
    cur = null;
  };
  for (const ln of lines) {
    const m = ln.match(headerRe);
    if (m) {
      flush();
      cur = { objId: m[1], title: m[2], body: [] };
      continue;
    }
    // A non-P/T header (any `#`-level) ends the current block region.
    if (/^#{1,6}\s/.test(ln)) {
      flush();
      continue;
    }
    if (cur) cur.body.push(ln);
  }
  flush();
  return blocks;
}

// ---------------------------------------------------------------------------
// Lean parsing
// ---------------------------------------------------------------------------

export interface LeanDecl {
  objId: string | null; // derived obj_id ("P-10"/"T-1") or null if none recognizable
  declKind: string; // def | abbrev | structure | theorem
  name: string;
  file: string; // path relative to leanDir
  line: number; // 1-indexed
}

/** Whole-file declaration scan for omission guards. Lean permits the name on the next line and
 * quoted identifiers (`«name»`); a line-only header regex silently misses both. Comments are
 * masked before this runs, while newlines/offsets are preserved for source locations. */
export const DECL_HEADER_SCAN_RE =
  /^[ \t]*(?:@\[[^\]]*\][ \t\r\n]*)*(?:(?:noncomputable|private|protected|scoped|local|partial|unsafe)\s+)*(def|abbrev|structure|theorem|lemma|class|instance|inductive|opaque|axiom|constant)\b[ \t\r\n]+(?:«([^»]+)»|([A-Za-z_][A-Za-z0-9_'.]*))/gm;

/** A standalone `variable`/`universe` binder command. It is NOT a `DECL_HEADER_SCAN_RE`
 *  anchor, but the scaffolder legitimately tags a shared section binder inline
 *  (`variable (D : FiniteDesign Ω) -- @realizes Z(sample space Ω)`): the binder's
 *  TYPE realizes the symbol. Such a tag must anchor to the `variable` itself, not
 *  fall through to the preceding — already closed — `def` (which realizes something
 *  else and would poison the cluster's conjunction with a false drift). Captures the
 *  first bound identifier as a readable member label. */
export const VARIABLE_HEADER_RE = /^\s*variable\s*[({][^)}]*?([A-Za-z_][A-Za-z0-9_'.]*)/;

/** A line is comment-or-blank if blank, inside a block comment, or opens a
 *  `/-`/`--` comment. Sufficient for walking the docstring block above a decl. */
export function classifyComment(source: string): boolean[] {
  const raw = source.split(/\r?\n/);
  const masked = maskLeanCommentsAndStrings(source).split(/\r?\n/);
  return raw.map((line, i) => line.trim() === "" || (line.trim() !== "" && (masked[i] ?? "").trim() === ""));
}

/**
 * Derive an obj_id for a Lean decl, KIND-AWARE so a `def` whose docstring merely
 * *mentions* a theorem id (e.g. "drives T-2's L-14") cannot hijack that T-slot:
 *  - `theorem`: a `t<n>_…` name ⇒ `T-<n>` (the scaffold convention); else a
 *    `T-<n>` token in the comment above as fallback. A theorem never maps to P-*.
 *  - `lemma`: a `l<n>_…` name ⇒ `L-<n>`; else an `L-<n>` token in the comment.
 *    A lemma never maps to a P- or T- id (those are owned by defs / theorems).
 *  - `def`/`abbrev`/`structure`: a `P-<n>` token in the comment above only;
 *    T- and L- tokens are IGNORED (a definition is never a theorem/lemma).
 */
export function deriveObjId(declKind: string, name: string, commentAbove: string): string | null {
  // Archived / deprecated SHADOW decls (kept in-tree for provenance after a
  // theorem is superseded — convention `<name>_deterministic_shadow` /
  // `<name>_shadow`) are NOT paper objects and must NOT claim an obj_id:
  // `t1_thm_deterministic_shadow` derives the same `T-1` from its `^t1_` name
  // prefix as the live `t1_thm`, and being earlier in the file it would shadow
  // the real headline in the crosswalk (the paper would then verify the
  // archived statement). Skip them so the live decl is the sole obj_id holder.
  if (/(^|_)(shadow|deprecated|archived)(_|$)/i.test(name)) return null;
  // Plan-driven scaffolds use semantic typed-core ids (`thm:...`, `def:...`,
  // `ass:...`, `lem:...`) on an explicit `-- @node:` line rather than the
  // legacy T-/P-/A-/L- naming convention.  Treat that tag as authoritative.
  // Without this, typed-core headline theorems are invisible to the hidden-def
  // reachability scan below, so changing a meaning-bearing inline structure in
  // F2 does not invalidate the theorem's cached F2.5 verdict.
  const typed = commentAbove.match(/@node:\s*((?:thm|def|ass|lem|gate):[A-Za-z0-9_.:-]+)/)?.[1];
  if (typed) {
    if (declKind === "theorem" && typed.startsWith("thm:")) return typed;
    if (declKind === "lemma" && typed.startsWith("lem:")) return typed;
    if (
      (declKind === "def" || declKind === "abbrev" || declKind === "structure" ||
        declKind === "class" || declKind === "instance" || declKind === "inductive" ||
        declKind === "opaque" || declKind === "axiom" || declKind === "constant") &&
      /^(?:def|ass|gate):/.test(typed)
    ) return typed;
  }
  if (declKind === "theorem") {
    const tm = name.match(/^t(\d+)_/i);
    if (tm) return `T-${tm[1]}`;
    return commentAbove.match(/\bT-\d+\b/)?.[0] ?? null;
  }
  if (declKind === "lemma") {
    const lm = name.match(/^l(\d+)/i);
    if (lm) return `L-${lm[1]}`;
    return commentAbove.match(/\bL-\d+[a-z]?\b/)?.[0] ?? null;
  }
  // Assumption bundle (`structure a3Bundle …`) → A-3; setup (`def s1Setup …`) → S-1.
  // Name-prefix only (`^a\d` / `^s\d`), so `aipwScore` / `score` do NOT match.
  const am = name.match(/^a(\d+)/i);
  if (am) return `A-${am[1]}`;
  const sm = name.match(/^s(\d+)/i);
  if (sm) return `S-${sm[1]}`;
  return commentAbove.match(/\bP-\d+[a-z]?\b/)?.[0] ?? null;
}

/**
 * The canonical headline decl for a T-obj_id is exactly `t<n>_thm`. A
 * same-prefixed helper / bridge / aggregate (`t1_thm_bridge`, `t5_geometry`)
 * also derives the same `T-n` from its `t<n>_` name but is NOT the paper's
 * theorem — used by the skeleton dedup to pick the real headline when several
 * decls claim one T-obj_id. Returns false for non-theorem obj_ids (so P-/L-
 * keep first-wins).
 */
export function isCanonicalHeadline(objId: string, name: string): boolean {
  const t = objId.match(/^T-(\d+)$/);
  return t ? name.toLowerCase() === `t${t[1]}_thm` : false;
}

/**
 * Collect every named declaration form in `DECL_HEADER_SCAN_RE` (with `lemma` optional in
 * `includeLemmas`) in `leanDir` that carries a recognizable obj_id (P-/T-/L-).
 * Helper decls without an obj_id token are skipped — implementation detail, not
 * paper objects.
 */
export async function parseLeanDecls(
  leanDir: string,
  opts: CrosswalkOpts = {},
): Promise<LeanDecl[]> {
  const out: LeanDecl[] = [];
  if (!existsSync(leanDir)) return out;
  const files = (await readdir(leanDir, { recursive: true }))
    .map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .sort();
  for (const rel of files) {
    const source = await readFile(path.join(leanDir, rel), "utf8");
    const lines = source.split(/\r?\n/);
    const comment = classifyComment(source);
    const masked = maskLeanCommentsAndStrings(source);
    DECL_HEADER_SCAN_RE.lastIndex = 0;
    let m: RegExpExecArray | null;
    while ((m = DECL_HEADER_SCAN_RE.exec(masked))) {
      const kind = m[1];
      const name = m[2] ?? m[3];
      if (!opts.includeLemmas && kind === "lemma") continue;
      const startLine = source.slice(0, m.index).split(/\r?\n/).length - 1;
      const kindOffset = m[0].indexOf(kind);
      const line = source.slice(0, m.index + Math.max(0, kindOffset)).split(/\r?\n/).length;
      // Walk up over the contiguous comment/blank block to grab the docstring.
      let j = startLine - 1;
      const above: string[] = [];
      while (j >= 0 && comment[j]) {
        above.push(lines[j]);
        j--;
      }
      const objId = deriveObjId(kind, name, above.join("\n"));
      out.push({ objId, declKind: kind, name, file: rel, line });
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Membership-predicate augmentation (the uniform-constant-laundering surface)
// ---------------------------------------------------------------------------

/**
 * A def/abbrev whose body existentially quantifies REAL constants — the
 * "membership predicate" shape `∃ C : ℝ, P satisfies-bound-with-C`. As a CLASS
 * definition this per-law `∃` is correct, but on a converse / lower bound it is
 * the safe-for-the-prover direction: the witness need only satisfy the bare `∃`,
 * so it may join the class with n-dependent / blowing-up constants and the
 * .tex's "uniform over a fixed class" claim is silently weakened (Lean then
 * certifies a strictly weaker statement than the paper asserts). Matches an
 * existential binder annotated with `ℝ` (incl. `ℝ≥0`, `ℝ≥0∞`); function-typed
 * existentials (`∃ f : … → ℝ`) and integer thresholds (`∃ N : ℕ`) are deliberately
 * NOT this trap and do not match.
 */
export const CONSTANT_EXISTENTIAL_RE = /∃[^,\n]*:\s*ℝ/;

export interface FullDecl {
  kind: string;
  name: string;
  file: string;
  line: number; // 1-indexed header line
  text: string; // full decl source (header through line before next decl)
  commentAbove: string;
}

/** Parse EVERY top-level decl in `leanDir` with its full body span + docstring.
 *  Unlike `parseLeanDecls` (obj_id-bearing only) this keeps obj-id-less helper
 *  defs and their bodies — needed to walk the def-reference graph and to resolve
 *  banked crosswalk anchors against live source (see bank_crosswalk_lint.ts). */
export async function parseAllDecls(leanDir: string): Promise<FullDecl[]> {
  const out: FullDecl[] = [];
  if (!existsSync(leanDir)) return out;
  const files = (await readdir(leanDir, { recursive: true }))
    .map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .sort();
  for (const rel of files) {
    const source = await readFile(path.join(leanDir, rel), "utf8");
    const lines = source.split(/\r?\n/);
    const comment = classifyComment(source);
    const masked = maskLeanCommentsAndStrings(source);
    const headers: { i: number; kind: string; name: string }[] = [];
    DECL_HEADER_SCAN_RE.lastIndex = 0;
    let m: RegExpExecArray | null;
    while ((m = DECL_HEADER_SCAN_RE.exec(masked))) {
      headers.push({
        i: source.slice(0, m.index).split(/\r?\n/).length - 1,
        kind: m[1],
        name: m[2] ?? m[3] ?? "",
      });
    }
    for (let h = 0; h < headers.length; h++) {
      const { i, kind, name } = headers[h];
      const end = h + 1 < headers.length ? headers[h + 1].i : lines.length;
      let j = i - 1;
      const above: string[] = [];
      while (j >= 0 && comment[j]) {
        above.push(lines[j]);
        j--;
      }
      out.push({
        kind,
        name,
        file: rel,
        line: i + 1,
        text: lines.slice(i, end).join("\n"),
        commentAbove: above.join("\n"),
      });
    }
  }
  return out;
}

/** A theorem's STATEMENT (signature + hypotheses + conclusion), i.e. everything
 *  before the proof `:=`. A raw `indexOf(":=")` is wrong because two other kinds
 *  of `:=` appear earlier:
 *   - a named argument `(x := y)` inside a binder — always at BRACKET-DEPTH > 0,
 *     so the depth check skips it;
 *   - a `let v := …` / `have v := …` binder, which at depth 0 introduces the
 *     conclusion itself (`… : let beta := e; P beta`). Its `:=` is NOT the proof
 *     delimiter, so each depth-0 `let`/`have` consumes the next depth-0 `:=`.
 *  Cutting at either truncates the statement, dropping the class/conclusion and
 *  everything the BFS reaches through them.
 *
 *  Equation-compiler decls (`def f : T\n  | 0 => …`) have no proof `:=`, so the
 *  binder skip runs to the end and returns the whole decl. That is the safe
 *  direction (this feeds a BFS that is deliberately over-inclusive — "surfaces
 *  more, hides nothing") and it does not move `isPropValued`, which only asks
 *  whether the text ends in `Prop`. Don't try to terminate such decls at their
 *  first `|`: a line-initial `|` is far more often an absolute value
 *  (`|a - b| ≤ …`) than a match arm, and cutting there truncates real
 *  statements. */
export function statementText(declText: string): string {
  const masked = maskLeanCommentsAndStrings(declText);
  let depth = 0;
  // Depth-0 `let`/`have` binders still awaiting their `:=`.
  let pendingBinders = 0;
  for (let i = 0; i < declText.length - 1; i++) {
    const ch = masked[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth--;
    else if (depth !== 0) continue;
    else if (ch === ":" && masked[i + 1] === "=") {
      if (pendingBinders > 0) pendingBinders--;
      else return declText.slice(0, i);
    } else if (isBinderKeywordAt(masked, i)) pendingBinders++;
  }
  return declText;
}

/** `declText` has a whole-word `let` or `have` starting at `i` — the keyword
 *  form, not an identifier that merely starts with it (`letFun`, `haveI`). */
function isBinderKeywordAt(text: string, i: number): boolean {
  const isWordChar = (c: string | undefined) => c != null && /[A-Za-z0-9_'.]/.test(c);
  if (isWordChar(text[i - 1])) return false;
  for (const kw of ["let", "have"]) {
    if (text.startsWith(kw, i) && !isWordChar(text[i + kw.length])) return true;
  }
  return false;
}

export function leanIdentifiers(text: string): string[] {
  return text.match(/[A-Za-z_][A-Za-z0-9_']*/g) ?? [];
}

/** Split a theorem STATEMENT into its hypothesis (binder) region and its
 *  conclusion region at the conclusion `:` (the first colon at bracket-depth 0).
 *  No depth-0 colon (autobound / unusual layout) → treat the whole thing as the
 *  conclusion (conservative: surfaces more, hides nothing). */
export function splitStatement(stmt: string): { hyp: string; concl: string } {
  const masked = maskLeanCommentsAndStrings(stmt);
  let depth = 0;
  for (let i = 0; i < stmt.length; i++) {
    const ch = masked[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth--;
    else if (ch === ":" && depth === 0) return { hyp: stmt.slice(0, i), concl: stmt.slice(i + 1) };
  }
  return { hyp: "", concl: stmt };
}

/** A def's result type is `Prop` (or `… → Prop`) — i.e. it is a predicate /
 *  condition / membership class, the form an inline ASSUMPTION takes. Tested on
 *  the signature (everything before `:=`): its last type token is `Prop`. */
export function isPropValued(declText: string): boolean {
  return /\bProp\s*$/.test(statementText(declText).trim());
}
