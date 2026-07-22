/**
 * Structures a theorem's authored Lean source (name-preserving surface syntax,
 * as written in the file — NOT the elaborated, name-erased `statement` pretty-print)
 * into one row per top-level binder plus a conclusion, so the library page can
 * render "one hypothesis, one line" instead of a single shared-scroll block.
 *
 * Deliberately conservative: every step that can't confidently recognise the
 * shape it's looking at returns `null`/falls back, so the caller can keep the
 * existing scrollable rendering for anything this doesn't handle.
 */

import { linkifyStatement, type Library } from "./library.js";

export interface StmtLine {
  indent: number;
  text: string;
  html?: string;
}

export interface ChainBlock {
  kind: "chain";
  /** The leading `∀ …,`/`∃ …,` header(s), already dedented — null if there was none. */
  header: StmtLine[] | null;
  /** Each `→`-separated premise, itself possibly multi-line. */
  premises: StmtLine[][];
  conclusion: StmtLine[];
}

export type StmtBody = StmtLine[] | ChainBlock;

export function isChain(body: StmtBody): body is ChainBlock {
  return !Array.isArray(body);
}

export interface BinderRow {
  kind: "binder";
  names: string;
  chip: "hyp" | "decl";
  body: StmtBody;
  /** `(...)` vs `{...}`/`[...]` — used to decide whether a trailing anonymous
   * typeclass row (`[NormedAddCommGroup Θ]`) constrains THIS row and should
   * merge into it rather than stand alone. */
  bracketKind: "explicit" | "implicit";
}

/** A `-- section comment` / `/- … -/` the author placed between binder
 * groups to label a cluster of hypotheses — preserved as its own divider
 * row rather than dropped, since it's how the source communicates grouping. */
export interface CommentRow {
  kind: "comment";
  text: string;
}

export type StatementItem = BinderRow | CommentRow;

export function isBinderRow(item: StatementItem): item is BinderRow {
  return item.kind === "binder";
}

export interface StructuredStatement {
  /** A theorem's hypotheses, or a structure/class's own parameter telescope. */
  rows: StatementItem[];
  /** Non-null only for a structure/class: the fields bundled in its `where` block. */
  fields: StatementItem[] | null;
  /** A theorem's goal; always `[]` for a structure/class (nothing to conclude). */
  conclusion: StmtBody;
}

// ---------------------------------------------------------------------------
// bracket-depth utilities
// ---------------------------------------------------------------------------

function bracketDelta(c: string): number {
  if (c === "(" || c === "{" || c === "[" || c === "⦃") return 1; // ⦃
  if (c === ")" || c === "}" || c === "]" || c === "⦄") return -1; // ⦄
  return 0;
}

function topLevelIndexOf(text: string, ch: string): number {
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    depth += bracketDelta(text[i]);
    if (depth === 0 && text[i] === ch) return i;
  }
  return -1;
}

/**
 * Index of the whitespace before the signature-ending `:=` (proof/definition
 * start) — same semantics as `text.search(/\s:=/)`, but aware of the two other
 * kinds of `:=` that appear first:
 *
 *  - a named-argument application inside the signature
 *    (`BackdoorEstimationSystem.H_ε (γ := γ) ε`) — always at bracket depth > 0,
 *    so the depth check skips it;
 *  - a `let`/`have` binder introducing a let-bound CONCLUSION
 *    (`… : let beta := e; P beta`), which sits at depth 0. Its `:=` is not the
 *    proof marker, so each depth-0 `let`/`have` consumes the next depth-0 `:=`.
 *    Without this the conclusion renders as the bare head `let beta`.
 *
 * -1 if none found.
 */
export function findProofStart(text: string): number {
  // Comments are blanked position-preservingly, so a `-- …` note's prose
  // ("variables have zero excess kurtosis") can't be read as a binder keyword.
  // Indices into `clean` remain valid for `text`.
  const clean = stripLeanComments(text);
  let depth = 0;
  // Depth-0 `let`/`have` binders still awaiting their `:=`.
  let pendingBinders = 0;
  // First depth-0 `:=` regardless of binders — the pre-binder-skip answer.
  let firstMarker = -1;
  // A depth-0 `=>` seen before any `:=` means this decl's body is given by
  // match alternatives (`| 0 => rfl`), not by a proof `:=`.
  let sawTopLevelArrow = false;
  for (let i = 0; i < clean.length; i++) {
    depth += bracketDelta(clean[i]);
    if (depth !== 0) continue;
    if (clean[i] === ":" && /\s/.test(clean[i - 1] ?? "") && clean[i + 1] === "=") {
      if (firstMarker < 0) {
        firstMarker = i - 1;
        // Equation-compiler decl: the `let`/`have`s below are its ARMS', not
        // conclusion binders', so the skip would eat proof markers and run on
        // into the body. Keep the naive answer.
        if (sawTopLevelArrow) return firstMarker;
      }
      if (pendingBinders > 0) pendingBinders--;
      else return i - 1;
    } else if (clean[i] === "=" && clean[i + 1] === ">") sawTopLevelArrow = true;
    else if (isBinderKeywordAt(clean, i)) pendingBinders++;
  }
  // Every `:=` was eaten by a pending binder and none was left over: this text
  // has no proof marker at all. That is the normal case for an already-stripped
  // signature (`declSignature` cuts the proof, then re-parses to structure the
  // conclusion), whose trailing `let`s are conclusion binders. Report "none" —
  // returning `firstMarker` here would cut at the conclusion's own `let`.
  // Equation-compiler decls never reach this point: `sawTopLevelArrow` returns
  // their naive marker above.
  return -1;
}

/** `text` has a whole-word `let`/`have` at `i` — the keyword, not an identifier
 * that merely starts with it (`letFun`, `haveI`, `S.let`). */
function isBinderKeywordAt(text: string, i: number): boolean {
  const isWordChar = (c: string | undefined) => c != null && /[A-Za-z0-9_'.]/.test(c);
  if (isWordChar(text[i - 1])) return false;
  for (const kw of ["let", "have"]) {
    if (text.startsWith(kw, i) && !isWordChar(text[i + kw.length])) return true;
  }
  return false;
}

/** Depth-aware whole-word search for a keyword (`where`, `extends`, …), so a
 * parent type's own application args can't hide an accidental substring hit. */
function topLevelKeywordIndex(text: string, keyword: string): number {
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    depth += bracketDelta(text[i]);
    if (depth === 0 && text.startsWith(keyword, i)) {
      const before = text[i - 1];
      const after = text[i + keyword.length];
      const wordBefore = before === undefined || !/[A-Za-z0-9_]/.test(before);
      const wordAfter = after === undefined || !/[A-Za-z0-9_]/.test(after);
      if (wordBefore && wordAfter) return i;
    }
  }
  return -1;
}

function topLevelSplit(text: string, sep: string): string[] {
  const parts: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < text.length; i++) {
    depth += bracketDelta(text[i]);
    if (depth === 0 && text.startsWith(sep, i)) {
      parts.push(text.slice(start, i));
      start = i + sep.length;
    }
  }
  parts.push(text.slice(start));
  return parts.map((p) => p.trim());
}

// ---------------------------------------------------------------------------
// derive line breaks from a width budget, not from the source's own breaks
// ---------------------------------------------------------------------------

// The Lean source already breaks long expressions at sensible points — but at
// its OWN column width, which for a deeply nested conclusion (∃/∀/∧ nesting
// several levels deep, each level narrowing what's left of the line) means
// almost every operator lands on its own line. Reproducing those breaks
// verbatim reads as fragmented once re-indented into a narrower card. Instead
// this derives breaks from scratch against a width budget: split at ∧
// conjuncts, then a leading ∀/∃ header, then the clause's main relation, then
// a top-level +/- sum — recursing into each piece only while it's still over
// budget, so short pieces stay on one line and only genuinely long ones grow
// a second line (with per-line horizontal scroll as the final fallback for
// anything left irreducibly long, e.g. deep inside an if/then/else).
const WRAP_WIDTH = 90;

function collapseWs(text: string): string {
  return text.replace(/\s+/g, " ").trim();
}

// Depth that also toggles +1 while inside a `‖ … ‖` norm span — otherwise a
// bare `-` inside `‖x - y‖` reads as a top-level subtraction and gets treated
// as a sum-split point.
function normAwareDepths(text: string): number[] {
  const depths: number[] = new Array(text.length);
  let depth = 0;
  let inNorm = false;
  for (let i = 0; i < text.length; i++) {
    depths[i] = depth;
    if (text[i] === "‖") {
      inNorm = !inNorm;
      depth += inNorm ? 1 : -1;
    } else {
      depth += bracketDelta(text[i]);
    }
  }
  return depths;
}

// ∀/∃ extend as far right as Lean's grammar allows (to the end of the
// enclosing clause), so a `∧` occurring AFTER one is inside its body, not a
// sibling conjunct of whatever came before the quantifier. Scanning stops the
// instant it sees a top-level ∀/∃, so only ∧'s that occur before any
// quantifier are treated as splitting the current clause into conjuncts.
function topLevelConjuncts(text: string): string[] {
  const depths = normAwareDepths(text);
  const parts: string[] = [];
  let start = 0;
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    if (text[i] === "∀" || text[i] === "∃") break;
    if (text[i] === "∧") {
      parts.push(text.slice(start, i).trim());
      start = i + 1;
    }
  }
  parts.push(text.slice(start).trim());
  return parts;
}

const RELATIONS = ["≤", "≥", "≠", "↔", "="];

function topLevelRelationIndex(text: string): number {
  const depths = normAwareDepths(text);
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    for (const r of RELATIONS) {
      if (!text.startsWith(r, i)) continue;
      if (r === "=" && (text[i - 1] === ":" || text[i + 1] === "=")) continue; // `:=` / `==`
      return i;
    }
  }
  return -1;
}

// One summand per element; `sign` is null for the first (no leading +/-).
function topLevelSumSplit(text: string): { sign: string | null; text: string }[] {
  const depths = normAwareDepths(text);
  const parts: { sign: string | null; text: string }[] = [];
  let start = 0;
  let sign: string | null = null;
  for (let i = 1; i < text.length - 1; i++) {
    if (depths[i] !== 0) continue;
    if ((text[i] === "+" || text[i] === "-") && /\s/.test(text[i - 1]) && /\s/.test(text[i + 1])) {
      parts.push({ sign, text: text.slice(start, i).trim() });
      sign = text[i];
      start = i + 1;
    }
  }
  parts.push({ sign, text: text.slice(start).trim() });
  return parts;
}

function breakLines(raw: string, depth: number): StmtLine[] {
  const t = collapseWs(raw);
  if (!t) return [];
  if (t.length <= WRAP_WIDTH) return [{ indent: depth, text: t }];

  const conjuncts = topLevelConjuncts(t);
  if (conjuncts.length > 1) {
    const out: StmtLine[] = [];
    conjuncts.forEach((c, i) => {
      out.push(...breakLines(c, depth));
      if (i < conjuncts.length - 1 && out.length > 0) out[out.length - 1].text += " ∧";
    });
    return out;
  }

  const q = stripLeadingQuantifier(t);
  if (q) return [{ indent: depth, text: `${q.header},` }, ...breakLines(q.rest, depth + 1)];

  const relIdx = topLevelRelationIndex(t);
  if (relIdx > 0) {
    return [...breakLines(t.slice(0, relIdx), depth), ...breakLines(t.slice(relIdx), depth + 1)];
  }

  const sum = topLevelSumSplit(t);
  if (sum.length > 1) {
    const out: StmtLine[] = [];
    for (const s of sum) out.push(...breakLines(s.sign ? `${s.sign} ${s.text}` : s.text, depth));
    return out;
  }

  return [{ indent: depth, text: t }]; // irreducibly long — per-line horizontal scroll handles it
}

// ---------------------------------------------------------------------------
// chain (`∀ …, P → Q → … → R`) detection
// ---------------------------------------------------------------------------

function stripLeadingQuantifier(text: string): { header: string; rest: string } | null {
  const t = text.trim();
  if (!/^[∀∃]/.test(t)) return null;
  const commaIdx = topLevelIndexOf(t, ",");
  if (commaIdx < 0) return null;
  return { header: t.slice(0, commaIdx).trim(), rest: t.slice(commaIdx + 1).trim() };
}

/**
 * Only fires when the text opens with an explicit `∀`/`∃` — a plain data
 * arrow type (`Θ → γ → ℝ`) never does, in this codebase's surface syntax, so
 * that single check keeps this from ever mis-firing on a non-Prop binder.
 */
function detectChain(text: string): ChainBlock | null {
  const stripped = stripLeadingQuantifier(text);
  if (!stripped) return null;
  const { header, rest } = stripped;
  const parts = topLevelSplit(rest, "→");
  if (parts.length < 2) return null;
  const premiseParts = parts.slice(0, -1);
  const finalPart = parts[parts.length - 1];
  if (!finalPart.trim()) return null;
  if (premiseParts.some((p) => !p.trim() || /^[∀∃]/.test(p.trim()))) return null;
  return {
    kind: "chain",
    header: breakLines(header, 0),
    premises: premiseParts.map((p) => breakLines(p, 0)),
    conclusion: breakLines(finalPart, 0),
  };
}

function formatBody(text: string): StmtBody {
  return detectChain(text) ?? breakLines(text, 0);
}

// ---------------------------------------------------------------------------
// binder-telescope + conclusion scan
// ---------------------------------------------------------------------------

interface ScannedGroup {
  raw: string;
  start: number;
  end: number;
}

// Operates on the FULL (comment-stripped) text starting at `start`, reporting
// each group's ABSOLUTE position — so the caller can look up the
// corresponding span of the ORIGINAL (comment-intact) source and recover any
// `-- …`/`/- … -/` comment that sat in the gap before it.
function scanSignature(
  text: string,
  start: number,
): { groups: ScannedGroup[]; conclusionText: string; telescopeStart: number } | null {
  const n = text.length;
  let i = start;
  const skipWs = () => {
    while (i < n && /\s/.test(text[i])) i++;
  };
  const groups: ScannedGroup[] = [];
  skipWs();
  while (i < n && bracketDelta(text[i]) === 1) {
    const gStart = i;
    let depth = 0;
    do {
      depth += bracketDelta(text[i]);
      i++;
    } while (i < n && depth > 0);
    if (depth !== 0) return null; // unbalanced — abort, let caller fall back
    groups.push({ raw: text.slice(gStart, i), start: gStart, end: i });
    skipWs();
  }
  if (text[i] !== ":") return null;
  i++;
  const conclusionStart = i;
  const proofStart = findProofStart(text.slice(conclusionStart));
  const conclusionEnd = proofStart >= 0 ? conclusionStart + proofStart : -1;
  const conclusionText = (
    conclusionEnd >= 0 ? text.slice(conclusionStart, conclusionEnd) : text.slice(conclusionStart)
  ).trim();
  if (!conclusionText) return null;
  return { groups, conclusionText, telescopeStart: start };
}

// The gap between two consecutive groups (or between the telescope's start
// and its first group) is, BY CONSTRUCTION, pure whitespace once comments are
// accounted for — `scanSignature`'s own `skipWs` already walked past it
// without hitting a non-whitespace character in the comment-stripped text. So
// extracting comment markers from the corresponding ORIGINAL-source span is
// safe: there is no code in there to misparse, only whitespace and comments.
function extractComment(gap: string): string | null {
  const parts: string[] = [];
  // `\/-{1,2}` — a docstring opens `/--` (one extra dash over a plain `/-`
  // block comment); without the `{1,2}` the second dash falls INSIDE the
  // captured group as a stray leading `-` in the displayed text.
  const re = /--([^\n]*)|\/-{1,2}([\s\S]*?)-\//g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(gap))) {
    const text = (m[1] ?? m[2] ?? "").trim();
    if (text) parts.push(text);
  }
  return parts.length ? parts.join(" ") : null;
}

// Deliberately excludes `→`: Lean uses the same arrow for a plain function
// type (`Θ → γ → ℝ`, not a hypothesis) and for implication, so its presence
// alone says nothing about Prop-vs-Type. The remaining symbols are relations
// that only meaningfully appear inside a proposition.
const PROP_HINT = /[≤≥≠↔∈⊆∀∃]|(?:^|[^:<>])=(?:[^=]|$)|\s<\s/;

function classifyChip(names: string, bracketKind: "explicit" | "implicit", typeText: string): "hyp" | "decl" {
  if (bracketKind === "implicit") return "decl";
  const toks = names.split(/\s+/).filter(Boolean);
  if (toks.length > 0 && toks.every((t) => /^h/i.test(t) && t.length > 1)) return "hyp";
  return PROP_HINT.test(typeText) ? "hyp" : "decl";
}

function parseBinderGroup(raw: string): Omit<BinderRow, "kind"> | null {
  const open = raw[0];
  const inner = raw.slice(1, -1).trim();
  if (!inner) return null;
  const bracketKind: "explicit" | "implicit" = open === "(" ? "explicit" : "implicit";
  const colonIdx = topLevelIndexOf(inner, ":");
  if (colonIdx < 0) {
    // Anonymous instance binder — `[StandardBorelSpace P.Ω]`, sugar for
    // `[inst : StandardBorelSpace P.Ω]`. Only `[...]` instance binders may
    // omit the name; `(...)`/`{...}` always carry an explicit `name : type`.
    if (open !== "[") return null;
    return { names: "", chip: "decl", body: formatBody(inner), bracketKind };
  }
  const names = inner.slice(0, colonIdx).trim();
  const typeText = inner.slice(colonIdx + 1).trim();
  if (!names || !typeText) return null;
  return {
    names,
    chip: classifyChip(names, bracketKind, typeText),
    body: formatBody(typeText),
    bracketKind,
  };
}

/**
 * Blanks out `--…`/`/- … -/` Lean comments (nesting-aware for block
 * comments), preserving every other character's position — including
 * newlines — so every downstream index-based scan (bracket depth, colon-
 * finding, arrow-finding, indentation) can stay comment-oblivious instead of
 * needing to special-case them at every call site. A comment's own prose can
 * contain unbalanced-looking punctuation ("the bridging hypothesis (see
 * below)"), which would otherwise corrupt bracket-depth tracking; this
 * codebase also interleaves `-- section comment` lines between binder groups
 * inside a long telescope.
 */
function stripLeanComments(text: string): string {
  let out = "";
  let i = 0;
  const n = text.length;
  while (i < n) {
    if (text[i] === "-" && text[i + 1] === "-") {
      while (i < n && text[i] !== "\n") {
        out += " ";
        i++;
      }
      continue;
    }
    if (text[i] === "/" && text[i + 1] === "-") {
      let depth = 1;
      out += "  ";
      i += 2;
      while (i < n && depth > 0) {
        if (text[i] === "/" && text[i + 1] === "-") {
          depth++;
          out += "  ";
          i += 2;
        } else if (text[i] === "-" && text[i + 1] === "/") {
          depth--;
          out += "  ";
          i += 2;
        } else {
          out += text[i] === "\n" ? "\n" : " ";
          i++;
        }
      }
      continue;
    }
    out += text[i];
    i++;
  }
  return out;
}

// Same identifier tokenizer linkifyStatement uses — reused here (rather than
// a unicode-fragile `\bname\b` regex) to test whether a trailing typeclass
// row's type mentions an earlier row's own name as a whole token.
const IDENT_RE = /[A-Za-z_¡-￿][A-Za-z0-9_.'¡-￿]*/g;

function bodyPlainText(body: StmtBody): string {
  const lines = isChain(body)
    ? [...(body.header ?? []), ...body.premises.flat(), ...body.conclusion]
    : body;
  return lines.map((l) => l.text).join(" ");
}

function referencesAnyName(body: StmtBody, names: string): boolean {
  const targets = new Set(names.split(/\s+/).filter(Boolean));
  if (targets.size === 0) return false;
  for (const m of bodyPlainText(body).matchAll(IDENT_RE)) {
    if (targets.has(m[0])) return true;
  }
  return false;
}

/**
 * A trailing anonymous/named typeclass constraint immediately following the
 * field/binder it constrains — `V : Type*` then `[decEqV : DecidableEq V]`
 * then `[fintypeV : Fintype V]`, or a theorem's `(Θ : Type*)
 * [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]` — reads as ONE logical
 * unit ("V, together with the fact it's decidable-eq and finite"), not three
 * unrelated rows. Folds each such `[...]`/`{...}` row into the row it
 * constrains as extra (indented) lines, so long instance chains on the same
 * variable stay visually attached to it instead of scattering across the
 * card. Only ever looks at the IMMEDIATELY preceding row (no comment or
 * unrelated binder in between) and only merges into a NAMED row — two
 * anonymous instances back to back (nothing in common to anchor them to)
 * stay separate.
 */
function mergeAttachedInstances(rows: StatementItem[]): StatementItem[] {
  const out: StatementItem[] = [];
  for (const r of rows) {
    if (r.kind === "binder" && r.bracketKind === "implicit" && out.length > 0) {
      const prev = out[out.length - 1];
      if (
        prev.kind === "binder" &&
        prev.names &&
        !isChain(prev.body) &&
        !isChain(r.body) &&
        referencesAnyName(r.body, prev.names)
      ) {
        const extra = (r.body as StmtLine[]).map((l) => ({ ...l, indent: Math.max(1, l.indent) }));
        prev.body = [...(prev.body as StmtLine[]), ...extra];
        continue;
      }
    }
    out.push(r);
  }
  return out;
}

/**
 * `rawSource` is the declaration's authored Lean text (docstring already
 * stripped) starting at (or before) the `theorem`/`lemma` keyword. Returns
 * `null` for anything that doesn't confidently parse as a binder telescope
 * followed by `: conclusion := …` — the caller should fall back to the plain
 * scrollable rendering in that case.
 */
export function structureTheoremSource(rawSource: string): StructuredStatement | null {
  const cleaned = stripLeanComments(rawSource);
  const m = cleaned.match(/\b(theorem|lemma)\s+([^\s({[⦃:]+)/);
  if (!m || m.index === undefined) return null;
  let telescopeStart = m.index + m[0].length;
  // optional explicit universe params `.{u, v}` — advance past without
  // slicing, so every downstream index stays absolute into `cleaned`/`rawSource`.
  const uniMatch = cleaned.slice(telescopeStart).match(/^\s*\.\{[^}]*\}/);
  if (uniMatch) telescopeStart += uniMatch[0].length;
  const scan = scanSignature(cleaned, telescopeStart);
  if (!scan) return null;

  const rows: StatementItem[] = [];
  let prevEnd = scan.telescopeStart;
  for (const g of scan.groups) {
    const comment = extractComment(rawSource.slice(prevEnd, g.start));
    if (comment) rows.push({ kind: "comment", text: comment });
    const row = parseBinderGroup(g.raw);
    if (!row) return null; // one unparseable binder aborts the whole structuring
    rows.push({ kind: "binder", ...row });
    prevEnd = g.end;
  }
  // A theorem/lemma may have no explicit binders at all (`lemma σ_X_le : …`).
  // Its conclusion still benefits from the structured card: LeanStatement
  // simply omits the hypotheses section and renders the conclusion directly.
  return { rows: mergeAttachedInstances(rows), fields: null, conclusion: formatBody(scan.conclusionText) };
}

// ---------------------------------------------------------------------------
// structure/class fields — a field list isn't bracket-delimited like a
// binder telescope; each field is its own `name(s) : type` INDENTED at the
// same column, so fields are found by indentation, not brackets.
// ---------------------------------------------------------------------------

interface FieldBlock {
  start: number;
  end: number;
}

// `cleaned`/`rawSource` share length and line structure (stripLeanComments
// blanks comment characters in place, never removing a byte), so line-based
// offsets computed from one apply directly to the other.
function scanStructureFields(cleaned: string, start: number): FieldBlock[] | null {
  const body = cleaned.slice(start);
  const lines = body.split("\n");
  const firstIdx = lines.findIndex((l) => l.trim().length > 0);
  if (firstIdx < 0) return null;
  const fieldIndent = lines[firstIdx].match(/^ */)![0].length;

  const lineOffsets: number[] = [];
  {
    let pos = start;
    for (const l of lines) {
      lineOffsets.push(pos);
      pos += l.length + 1;
    }
  }

  const blocks: FieldBlock[] = [];
  let idx = firstIdx;
  while (idx < lines.length) {
    if (lines[idx].trim().length === 0) {
      idx++;
      continue;
    }
    const indent = lines[idx].match(/^ */)![0].length;
    if (indent < fieldIndent) break; // dedented out of the structure body
    if (indent > fieldIndent) {
      idx++; // stray continuation with no owning field — skip defensively
      continue;
    }
    const blockLineStart = idx;
    idx++;
    while (idx < lines.length) {
      if (lines[idx].trim().length === 0) {
        idx++;
        continue;
      }
      if (lines[idx].match(/^ */)![0].length <= fieldIndent) break;
      idx++;
    }
    let blockLineEnd = idx;
    while (blockLineEnd > blockLineStart && lines[blockLineEnd - 1].trim().length === 0) blockLineEnd--;
    if (blockLineEnd === blockLineStart) continue; // shouldn't happen; defensive
    blocks.push({
      start: lineOffsets[blockLineStart],
      end: lineOffsets[blockLineEnd - 1] + lines[blockLineEnd - 1].length,
    });
  }
  return blocks.length ? blocks : null;
}

function parseFieldBlock(raw: string): Omit<BinderRow, "kind"> | null {
  const trimmed = raw.trim();
  // Bracket-wrapped instance/implicit field — `[decEqV : DecidableEq V]` or
  // an anonymous `[Fintype V]` — same shape as a theorem's binder group, so
  // it gets the exact same treatment (including the anonymous-instance case).
  if (/^[({[⦃]/.test(trimmed)) return parseBinderGroup(trimmed);
  const colonIdx = topLevelIndexOf(trimmed, ":");
  if (colonIdx < 0) return null;
  const names = trimmed.slice(0, colonIdx).trim();
  const typeText = trimmed.slice(colonIdx + 1).trim();
  if (!names || !typeText) return null;
  return { names, chip: classifyChip(names, "explicit", typeText), body: formatBody(typeText), bracketKind: "explicit" };
}

/**
 * `rawSource` is the declaration's authored Lean text (docstring already
 * stripped) starting at (or before) the `structure`/`class` keyword. Handles
 * the modern `where`-style field list (with an optional `extends Parent …`
 * clause); returns `null` — same fallback contract as
 * `structureTheoremSource` — for the old `structure Foo := ⟨…⟩` syntax, a
 * structure with no fields, or anything else it isn't confident about.
 */
export function structureRecordSource(rawSource: string): StructuredStatement | null {
  const cleaned = stripLeanComments(rawSource);
  const m = cleaned.match(/\b(structure|class)\s+([^\s({[⦃:]+)/);
  if (!m || m.index === undefined) return null;
  const telescopeStart = m.index + m[0].length;
  let i = telescopeStart;
  const skipWs = () => {
    while (i < cleaned.length && /\s/.test(cleaned[i])) i++;
  };
  const groups: ScannedGroup[] = [];
  skipWs();
  while (i < cleaned.length && bracketDelta(cleaned[i]) === 1) {
    const gStart = i;
    let depth = 0;
    do {
      depth += bracketDelta(cleaned[i]);
      i++;
    } while (i < cleaned.length && depth > 0);
    if (depth !== 0) return null;
    groups.push({ raw: cleaned.slice(gStart, i), start: gStart, end: i });
    skipWs();
  }

  // Optional `extends Parent1 Parent2 …`, ending at whichever of `:` (an
  // explicit return-type annotation) or `where` comes first at depth 0.
  // Occasionally there's neither — a pure wrapper structure that introduces
  // NO new fields at all (`structure Foo (params) extends Bar`, full stop) —
  // in which case the extends clause simply runs to the end of the source.
  let extendsText: string | null = null;
  let noFieldsAtAll = false;
  if (/^extends\b/.test(cleaned.slice(i))) {
    const afterExtends = i + "extends".length;
    const whereIdx = topLevelKeywordIndex(cleaned.slice(afterExtends), "where");
    const colonIdx = topLevelIndexOf(cleaned.slice(afterExtends), ":");
    const candidates = [whereIdx, colonIdx].filter((n) => n >= 0);
    if (candidates.length === 0) {
      extendsText = cleaned.slice(afterExtends).trim();
      i = cleaned.length;
      noFieldsAtAll = true;
    } else {
      const relEnd = Math.min(...candidates);
      extendsText = cleaned.slice(afterExtends, afterExtends + relEnd).trim();
      i = afterExtends + relEnd;
    }
  }
  if (!noFieldsAtAll) {
    // Optional explicit return type, e.g. `: Prop` on a predicate-bundle
    // structure (`structure Foo (params) : Prop where …`) — skipped, not
    // shown; it's almost always just `Prop` and adds no information over
    // "these fields are the predicate's conditions".
    if (cleaned[i] === ":") {
      i++;
      const whereIdx = topLevelKeywordIndex(cleaned.slice(i), "where");
      if (whereIdx < 0) return null;
      i += whereIdx;
    }
    if (!/^where\b/.test(cleaned.slice(i))) return null; // old-style `structure Foo := ⟨…⟩` or unrecognised
    i += "where".length;
  }

  const fieldBlocks = noFieldsAtAll ? [] : scanStructureFields(cleaned, i);
  if (!fieldBlocks) return null;

  // Parameters (what you supply to construct one) and fields (what it
  // actually bundles) are DIFFERENT roles — `Regime (V : Type*) (X : V →
  // Type*) where target : Finset V; assign : …` reads very differently once
  // `target`/`assign` aren't sitting in the same list as `V`/`X` — so they
  // render as two separate labelled sections, not one flat list.
  const paramRows: StatementItem[] = [];
  let prevEnd = telescopeStart;
  for (const g of groups) {
    const comment = extractComment(rawSource.slice(prevEnd, g.start));
    if (comment) paramRows.push({ kind: "comment", text: comment });
    const row = parseBinderGroup(g.raw);
    if (!row) return null;
    paramRows.push({ kind: "binder", ...row });
    prevEnd = g.end;
  }
  if (extendsText) {
    paramRows.push({ kind: "binder", names: "extends", chip: "decl", body: formatBody(extendsText), bracketKind: "explicit" });
  }

  const fieldRows: StatementItem[] = [];
  for (const b of fieldBlocks) {
    const comment = extractComment(rawSource.slice(prevEnd, b.start));
    if (comment) fieldRows.push({ kind: "comment", text: comment });
    const row = parseFieldBlock(cleaned.slice(b.start, b.end));
    if (!row) return null;
    fieldRows.push({ kind: "binder", ...row });
    prevEnd = b.end;
  }
  // A structure with no fields at all gains nothing from structuring UNLESS
  // it's the legitimate zero-new-fields wrapper case (`extends Bar`, full
  // stop) — there, the params + extends row IS the whole useful content.
  if (fieldRows.length === 0 && !noFieldsAtAll) return null;
  return {
    rows: mergeAttachedInstances(paramRows),
    fields: mergeAttachedInstances(fieldRows),
    conclusion: [],
  };
}

/** Dispatches to the theorem/lemma or structure/class parser by decl kind. */
export function structureDeclSource(rawSource: string, kind: string): StructuredStatement | null {
  if (kind === "theorem" || kind === "lemma") return structureTheoremSource(rawSource);
  if (kind === "structure" || kind === "class") return structureRecordSource(rawSource);
  return null;
}

// ---------------------------------------------------------------------------
// linkification (identifier → decl-page links), applied once over the whole
// statement so bound-variable detection sees full context, then redistributed
// to each display line.
// ---------------------------------------------------------------------------

function collectLines(s: StructuredStatement): StmtLine[] {
  const out: StmtLine[] = [];
  const visit = (b: StmtBody) => {
    if (Array.isArray(b)) {
      out.push(...b);
      return;
    }
    if (b.header) out.push(...b.header);
    for (const p of b.premises) out.push(...p);
    out.push(...b.conclusion);
  };
  for (const r of s.rows) if (isBinderRow(r)) visit(r.body);
  for (const r of s.fields ?? []) if (isBinderRow(r)) visit(r.body);
  visit(s.conclusion);
  return out;
}

// A NUL never occurs in real Lean source and falls outside linkifyStatement's
// identifier regex, so it survives escaping/linking untouched and can't
// collide with any cell's own content the way a space or newline would.
const CELL_DELIM = "\u0000";

export function linkifyStructured(
  s: StructuredStatement,
  lib: Library,
  base: string,
  selfNames?: Set<string>,
): void {
  const lines = collectLines(s);
  if (lines.length === 0) return;
  // A row's binder NAME is never linkified itself (it renders straight from
  // `row.names`, escaped by Astro) — but linkifyStatement's own bound-name
  // detection needs to SEE `name :` to know that name is a local variable,
  // not a reference. Without this, a name reused bare in a later row's type
  // (`eval` inside `eval_meas`'s `∀ θ, Measurable (eval θ)`, when `eval` was
  // bound several rows earlier as `(eval : Θ → γ → ℝ)`) can collide with an
  // unrelated same-named library declaration (`Polynomial.eval`). This
  // preamble cell is fed through linkifyStatement purely to seed that
  // detection; its own rendered output is discarded (see `parts[i + 1]`).
  const preamble = [...s.rows, ...(s.fields ?? [])]
    .filter(isBinderRow)
    .map((r) => (r.names ? `${r.names} : ` : ""))
    .filter(Boolean)
    .join(" ");
  const combined = [preamble, ...lines.map((l) => l.text)].join(CELL_DELIM);
  const html = linkifyStatement(combined, lib, base, selfNames);
  const parts = html.split(CELL_DELIM);
  lines.forEach((l, i) => {
    l.html = parts[i + 1] ?? l.text;
  });
}

/** Structures + linkifies in one call; returns `null` when structuring isn't confident.
 * `selfNames` (a page rendering its own decls, e.g. a paper's formalization page)
 * anchors those names within the page instead of linking out to /library. */
export function structureAndLinkify(
  rawSource: string,
  lib: Library,
  base: string,
  kind: string,
  selfNames?: Set<string>,
): StructuredStatement | null {
  const structured = structureDeclSource(rawSource, kind);
  if (!structured) return null;
  linkifyStructured(structured, lib, base, selfNames);
  return structured;
}
