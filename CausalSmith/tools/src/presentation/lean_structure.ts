// PORTED from `site/src/lib/paperLean.ts` (the "structured (hypotheses /
// conclusions) view" section and its three public types). P4 emits the tree the
// site renders, so this copy is the authority for row identity; drift with the
// site is harmless by construction because the site draws rows FROM the artifact.
// Re-sync by re-copying that section and the HypRow/ConclusionCard/StructuredView
// types.
//
// Added here and NOT in the site copy: `assignRowIds`, which stamps a stable
// `id` on every hypothesis row and every conclusion card in reading order. Those
// ids are what the author call assigns paper segments to.

import {
  classifyChip,
  identifierTokens,
  isBinderRow,
  isChain,
  normAwareDepths,
  parseBinderGroup,
  scanPropositionSignature,
  structureRecordSource,
  stripLeadingQuantifier,
  stripLeanComments,
  topLevelConjuncts,
  type StmtBody,
} from "./lean_statement.js";

export interface HypRow {
  /** Stable row id within this block's structured view ("r1", "r2", … in
   *  reading order) — the handle the artifact's assignments refer to. */
  id?: string;
  /** `cited` marks a hypothesis whose type is an ASSUMED external result — an
   *  input to the theorem, not something this development proves. */
  chip: "hyp" | "decl" | "cited";
  code: string;
  /** Space-separated NL↔Lean crosslink ids (HTML-class style; word-match
   *  with `[data-xl~="…"]`). A row can be covered by several links. */
  xl?: string;
}

/**
 * One clause of a theorem's goal, recursively fine-grained: the telescope
 * lifted at THIS level, an optional non-liftable prefix, and then EITHER a leaf
 * statement or a further split. Exactly one of `code` / `sub` is present.
 */
export interface ConclusionCard {
  /** Stable row id for this card's own content row (see HypRow.id). */
  id?: string;
  /** `∀` binders and `premise →` prefixes lifted at this level. */
  hyps: HypRow[];
  /** A leading run of `∃` binder groups, verbatim through its trailing comma —
   *  it scopes everything below, but is not a hypothesis. Only ever set
   *  alongside `sub`: an `∃` whose body doesn't split stays inside `code`. */
  intro?: string;
  /** Leaf statement. */
  code?: string;
  /** Nested split of a conjunction at this level. */
  sub?: ConclusionCard[];
  /** Space-separated NL↔Lean crosslink ids for the card's own content row:
   *  its `intro` when it nests, its `code` when it is a leaf. */
  xl?: string;
}

export interface StructuredView {
  sharedHyps: HypRow[];
  conclusions: ConclusionCard[];
}

/** Whether this is an explicitly Prop-valued `structure`/`class`. The final
 * `: Prop` check is made on the declaration header (before `where`), so a
 * parameter whose own type is `Prop` cannot trigger it. */
export function isPropRecord(statement: string): boolean {
  const cleaned = stripLeanComments(statement);
  const where = cleaned.search(/\bwhere\b/);
  if (where < 0) return false;
  const header = cleaned.slice(0, where).trimEnd();
  return /\b(structure|class)\b/.test(header) && /:\s*Prop\s*$/.test(header);
}

const stmtLinesText = (lines: Array<{ indent: number; text: string }>): string =>
  lines.map((line) => `${"  ".repeat(Math.max(0, line.indent))}${line.text}`).join("\n");

/** Reconstructs the readable type of a record parameter/field. This is only a
 * display tree—the conservative record parser has already proved that every
 * field was consumed. */
function stmtBodyText(body: StmtBody): string {
  if (!isChain(body)) return stmtLinesText(body);
  const parts: string[] = [];
  if (body.header?.length) parts.push(stmtLinesText(body.header));
  parts.push(...body.premises.map((premise) => `${stmtLinesText(premise)} →`));
  parts.push(stmtLinesText(body.conclusion));
  return parts.join("\n");
}

/** A Prop-valued record is a conjunction-like assumption/definition: its
 * telescope supplies parameters and each `where` field is one defining clause.
 * Convert the existing conservative record parse into the same view P4 emits
 * for a `def … : Prop := A ∧ B`, without changing the site's artifact schema. */
export function structurePropRecordView(rawSource: string): StructuredView | null {
  if (!isPropRecord(rawSource)) return null;
  const record = structureRecordSource(rawSource);
  if (!record?.fields) return null;

  const sharedHyps: HypRow[] = [];
  const conclusions: ConclusionCard[] = [];
  for (const item of record.rows) {
    if (!isBinderRow(item)) continue;
    const body = stmtBodyText(item.body);
    if (!body) return null;
    if (item.names === "extends") {
      conclusions.push({ hyps: [], code: `extends ${body}` });
      continue;
    }
    const [open, close] = item.bracketKind === "explicit" ? ["(", ")"] : ["{", "}"];
    sharedHyps.push({ chip: item.chip, code: `${open}${item.names} : ${body}${close}` });
  }
  for (const item of record.fields) {
    if (!isBinderRow(item)) continue;
    const body = stmtBodyText(item.body);
    if (!body) return null;
    conclusions.push({ hyps: [], code: `${item.names} : ${body}` });
  }
  return conclusions.length > 0 ? { sharedHyps, conclusions } : null;
}

/**
 * One declaration's source, held ONCE per paper in `Bundle.declSources` rather
 * than inlined into every drawer that reaches it. The same helper is pulled in
 * by dozens of statements — inlining it multiplied the payload roughly threefold.
 */
// ---------------------------------------------------------------------------
// structured (hypotheses / conclusions) view
// ---------------------------------------------------------------------------

/** All whitespace removed — the comparison used to prove a structured view
 *  reproduces its source exactly, modulo layout. */
function squash(text: string): string {
  return text.replace(/\s+/g, "");
}

/** Removes the common indentation of continuation lines, so a binder or
 *  conclusion lifted out of a deeply indented signature reads at the left
 *  margin without losing its internal line structure. */
function dedent(text: string): string {
  const lines = text.replace(/\s+$/, "").split("\n");
  if (lines.length < 2) return text.trim();
  let min = Infinity;
  for (const l of lines.slice(1)) {
    if (!l.trim()) continue;
    min = Math.min(min, l.match(/^ */)![0].length);
  }
  if (!Number.isFinite(min) || min === 0) return lines.join("\n").trimStart();
  return [lines[0].trimStart(), ...lines.slice(1).map((l) => l.slice(min))].join("\n");
}

const OPENERS = "({[⦃";
const CLOSERS = ")}]⦄";

/** Index of the closer matching the opener at position 0, or -1. */
function matchedCloseIndex(text: string): number {
  if (!OPENERS.includes(text[0] ?? "")) return -1;
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (OPENERS.includes(text[i])) depth++;
    else if (CLOSERS.includes(text[i])) {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

function topLevelColonIndex(text: string): number {
  const depths = normAwareDepths(text);
  for (let i = 0; i < text.length; i++) {
    if (depths[i] === 0 && text[i] === ":" && text[i + 1] !== "=") return i;
  }
  return -1;
}

/** Whole-word keyword at `i` — `let`, not `letFun`/`S.let`. */
function keywordAt(text: string, i: number, kw: string): boolean {
  const word = (c: string | undefined) => c != null && /[A-Za-z0-9_'.]/.test(c);
  return text.startsWith(kw, i) && !word(text[i - 1]) && !word(text[i + kw.length]);
}

const SCOPE_KEYWORDS = ["let", "have", "fun", "match", "if", "do"];

/**
 * Index of the leading implication arrow — the `→` that separates a premise
 * from the rest — or -1 when there is none, or when reading one would be
 * unsound. It is unsound as soon as a binder opens first: in `∃ f : α → β, P f`
 * the depth-0 `→` belongs to `f`'s TYPE, not to an implication, and splitting
 * there would invent the hypothesis `∃ f : α`.
 */
function leadingImplicationIndex(text: string): number {
  const depths = normAwareDepths(text);
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    const c = text[i];
    if (c === "→") return i;
    if (c === "∀" || c === "∃" || c === "," || c === ";" || c === "↦") return -1;
    if (c === "=" && text[i + 1] === ">") return -1;
    if (SCOPE_KEYWORDS.some((kw) => keywordAt(text, i, kw))) return -1;
  }
  return -1;
}

/**
 * True when splitting `text` at its depth-0 `∧`s is faithful to Lean's
 * precedence. `∧` binds tighter than `→`, `∨` and `↔`, so a depth-0 occurrence
 * of any of those means the `∧`s are nested INSIDE a larger connective and
 * splitting on them would rewrite the statement (`A ∧ B → C` is
 * `(A ∧ B) → C`, not `A ∧ (B → C)`).
 *
 * The scan stops at the first depth-0 `∀`/`∃`, because those extend as far
 * right as the grammar allows: everything after one is its body, so `A ∧ B ∧
 * ∀ n, P n → Q n` really is three conjuncts and its `→` is not this level's.
 * `topLevelConjuncts` stops in the same place, so the two agree.
 */
function conjunctionSplitLimit(text: string): number {
  const depths = normAwareDepths(text);
  let sawConjunction = false;
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    const c = text[i];
    if (c === "∀" || c === "∃") return text.length;
    if (c === "∧") {
      sawConjunction = true;
      continue;
    }
    // A depth-zero comma is also the binder separator in `∑ x in s, f x` and
    // `sup x, f x`; it does not change the connective level. Quantifiers were
    // handled above, while `fun`/`match`/etc. are rejected by SCOPE_KEYWORDS.
    if (c === "→" || c === "∨" || c === "↔" || c === ";" || c === "↦") return -1;
    if (c === "=" && text[i + 1] === ">") return -1;
    if (SCOPE_KEYWORDS.some((kw) => keywordAt(text, i, kw))) {
      // `A ∧ let x := v; B ∧ C` may be split immediately before `let`, but
      // not at the later conjunction: that one is inside the let's body. The
      // resulting suffix card peels the let first and can then split B/C.
      return sawConjunction ? i : -1;
    }
  }
  return text.length;
}

/** The depth-0 conjuncts of `text`, or `null` when it is not a conjunction at
 *  this level (or splitting it would misread Lean's precedence). */
function conjunctsOf(text: string): string[] | null {
  const limit = conjunctionSplitLimit(text);
  if (limit < 0) return null;
  let parts: string[];
  if (limit === text.length) {
    parts = topLevelConjuncts(text);
  } else {
    parts = [];
    const depths = normAwareDepths(text);
    let start = 0;
    for (let i = 0; i < limit; i++) {
      if (depths[i] === 0 && text[i] === "∧") {
        parts.push(text.slice(start, i).trim());
        start = i + 1;
      }
    }
    parts.push(text.slice(start).trim());
  }
  return parts.length > 1 && parts.every((p) => p.trim()) ? parts : null;
}

/**
 * A leading run of `∃` binder groups, taken verbatim through each trailing
 * comma. `∃ C rho : ℝ, ∃ N : ℕ, <body>` is not a hypothesis — nothing is
 * assumed — but it scopes everything under it, so it is hoisted out of the way
 * rather than left to bury the clauses the reader wants to compare.
 */
function stripExistsRun(text: string): { intro: string; rest: string } | null {
  let t = text.trim();
  const headers: string[] = [];
  while (t.startsWith("∃")) {
    const q = stripLeadingQuantifier(t);
    if (!q || !q.rest.trim()) break;
    headers.push(dedent(q.header));
    t = q.rest;
  }
  if (headers.length === 0) return null;
  return { intro: headers.map((h) => `${h},`).join(" "), rest: t };
}

function forallChip(header: string): "hyp" | "decl" {
  const body = header.replace(/^∀/, "").trim();
  if (OPENERS.includes(body[0] ?? "")) {
    const close = matchedCloseIndex(body);
    if (close > 0) {
      const parsed = parseBinderGroup(body.slice(0, close + 1));
      if (parsed) return parsed.chip;
    }
  }
  const colon = topLevelColonIndex(body);
  const names = colon >= 0 ? body.slice(0, colon).trim() : body;
  const type = colon >= 0 ? body.slice(colon + 1).trim() : "";
  return classifyChip(names, "explicit", type);
}

interface Lift {
  hyps: HypRow[];
  /** Everything peeled off the FRONT, concatenated verbatim (modulo layout). */
  prefix: string;
  inner: string;
  /** Everything peeled off the BACK (closing parens of an unwrapped clause). */
  suffix: string;
}

interface LetRun {
  rows: HypRow[];
  /** The let declarations, used only by the losslessness reconstruction. */
  prefix: string;
  rest: string;
}

/**
 * Peels a layout-delimited run of conclusion-local `let` declarations.
 *
 * Lean's common theorem shape
 *
 *     : let W := ...
 *       let denominator := ...
 *       P W denominator ∧ Q W
 *
 * has no punctuation between the declarations and the proposition: layout is
 * the delimiter. After `dedent`, each declaration and the body starts in
 * column zero while continuation lines remain indented. We only act on that
 * unambiguous shape; unusual inline/layout forms remain a single leaf.
 */
function stripLetRun(text: string): LetRun | null {
  let rest = dedent(text).trimStart();
  let prefix = "";
  const rows: HypRow[] = [];
  for (let guard = 0; guard < 64 && keywordAt(rest, 0, "let"); guard++) {
    const depths = normAwareDepths(rest);
    let semicolon = -1;
    for (let i = 0; i < rest.length; i++) {
      if (depths[i] === 0 && rest[i] === ";") {
        semicolon = i;
        break;
      }
    }

    let layout = -1;
    let offset = 0;
    const lines = rest.split("\n");
    for (let i = 0; i < lines.length; i++) {
      if (i > 0 && lines[i].trim() && (lines[i].match(/^ */)?.[0].length ?? 0) === 0) {
        layout = offset;
        break;
      }
      offset += lines[i].length + (i < lines.length - 1 ? 1 : 0);
    }

    const useSemicolon = semicolon >= 0 && (layout < 0 || semicolon < layout);
    const boundary = useSemicolon ? semicolon : layout;
    if (boundary <= 0) return null;
    const code = rest.slice(0, boundary).trim();
    if (!/^let\b[\s\S]*:=/.test(code)) return null;
    rows.push({ chip: "decl", code: dedent(code) });
    const consumed = useSemicolon ? boundary + 1 : boundary;
    prefix += rest.slice(0, consumed);
    rest = rest.slice(consumed).trimStart();
  }
  return rows.length > 0 && rest ? { rows, prefix, rest } : null;
}

/**
 * A clause prefix may alternate scopes: `let B := ...; ∀ L, premise → let C :=
 * ...; body`. Peel the whole run in source order so every local declaration and
 * governed hypothesis becomes a row before the body is recursively split.
 */
function liftCardPrefix(raw: string): Lift {
  let inner = raw.trim();
  const hyps: HypRow[] = [];
  let prefix = "";
  let suffix = "";
  for (let guard = 0; guard < 64; guard++) {
    const lift = liftTelescope(inner);
    hyps.push(...lift.hyps);
    prefix += lift.prefix;
    suffix = lift.suffix + suffix;
    inner = lift.inner;

    const lets = stripLetRun(inner);
    if (!lets) break;
    hyps.push(...lets.rows);
    prefix += lets.prefix;
    inner = lets.rest;
  }
  return { hyps, prefix, inner, suffix };
}

/**
 * Peels a clause's own leading telescope — `∀` binders and `premise →`
 * prefixes, through any parentheses wrapping the whole clause — into
 * hypothesis rows, leaving the proposition they govern as `inner`.
 * `prefix + inner + suffix` reproduces the input modulo whitespace, which the
 * caller checks.
 */
function liftTelescope(raw: string): Lift {
  let t = raw.trim();
  const prefix: string[] = [];
  const suffix: string[] = [];
  const hyps: HypRow[] = [];
  for (let guard = 0; guard < 64; guard++) {
    if (t.startsWith("(") && matchedCloseIndex(t) === t.length - 1) {
      prefix.push("(");
      suffix.unshift(")");
      t = t.slice(1, -1).trim();
      continue;
    }
    if (t.startsWith("∀")) {
      const q = stripLeadingQuantifier(t);
      if (!q) break;
      hyps.push({ chip: forallChip(q.header), code: dedent(q.header) });
      prefix.push(q.header, ",");
      t = q.rest;
      continue;
    }
    const arrow = leadingImplicationIndex(t);
    if (arrow > 0) {
      const premise = t.slice(0, arrow).trim();
      hyps.push({ chip: "hyp", code: dedent(premise) });
      prefix.push(premise, "→");
      t = t.slice(arrow + 1).trim();
      continue;
    }
    break;
  }
  return { hyps, prefix: prefix.join(""), inner: t, suffix: suffix.join("") };
}

/** How many levels of conclusion nesting are split. Six covers the deepest
 * accepted-paper statements while the renderer's inset rules still make the
 * scope visible; the losslessness check remains the final guard. */
const MAX_CARD_DEPTH = 6;

interface BuiltCard {
  card: ConclusionCard;
  /** Reproduces the card's source text modulo whitespace. */
  recon: string;
}

/**
 * One clause of a goal, fine-grained recursively: lift this level's
 * `∀`/`premise →` telescope, hoist any leading `∃` run, then split a
 * conjunction into nested cards — or stop at a leaf.
 */
function buildCard(raw: string, depth: number): BuiltCard | null {
  const lift = liftCardPrefix(raw);
  if (!lift.inner.trim()) return null;
  const localHyps = lift.hyps;
  const inner = lift.inner;
  const localPrefix = lift.prefix;
  const leaf = (): BuiltCard => ({
    card: { hyps: localHyps, code: dedent(inner) },
    recon: localPrefix + inner + lift.suffix,
  });
  if (depth >= MAX_CARD_DEPTH) return leaf();

  const ex = stripExistsRun(inner);
  // An `∃` prefix earns its own row only if hoisting it actually reveals a
  // split; otherwise the clause reads better whole, `∃` and all.
  const parts = conjunctsOf(ex ? ex.rest : inner);
  if (!parts) return leaf();

  const subs: BuiltCard[] = [];
  for (const p of parts) {
    const built = buildCard(p, depth + 1);
    if (!built) return null;
    subs.push(built);
  }
  const card: ConclusionCard = { hyps: localHyps };
  if (ex) card.intro = ex.intro;
  card.sub = subs.map((s) => s.card);
  return {
    card,
    recon: localPrefix + (ex?.intro ?? "") + subs.map((s) => s.recon).join("∧") + lift.suffix,
  };
}

/**
 * The type half of a binder row: `(hZeng : ZengOneArmMinimaxLower epsilon)` →
 * `ZengOneArmMinimaxLower epsilon`. A lifted `∀` header or `premise →` row has
 * no name half, so it is its own type.
 */
function binderTypeText(code: string): string {
  if (!OPENERS.includes(code[0] ?? "")) return code;
  const close = matchedCloseIndex(code);
  const inner = close > 0 ? code.slice(1, close) : code.slice(1);
  const colon = topLevelColonIndex(inner);
  return colon >= 0 ? inner.slice(colon + 1) : inner;
}

/**
 * Re-chips hypothesis rows whose type names an assumed external result.
 *
 * `(hZeng : ZengOneArmMinimaxLower epsilon)` is not a condition the paper
 * establishes — it is an input it takes on faith from the cited literature.
 * Showing it in the Hypotheses block chipped exactly like a proved side
 * condition hides the one thing a reader most needs to see. Only rows already
 * read as hypotheses are re-chipped; a type-class or type parameter is not an
 * assumption however its type reads.
 */
function markCitedHyps(rows: readonly HypRow[], citedNames: ReadonlySet<string>): void {
  if (citedNames.size === 0) return;
  for (const row of rows) {
    if (row.chip !== "hyp") continue;
    for (const tok of identifierTokens(binderTypeText(row.code))) {
      if (citedNames.has(tok)) {
        row.chip = "cited";
        break;
      }
    }
  }
}

/** Every hypothesis row of a structured view, at any nesting depth. */
function allHypRows(view: StructuredView): HypRow[] {
  const out: HypRow[] = [...view.sharedHyps];
  const walk = (c: ConclusionCard) => {
    out.push(...c.hyps);
    for (const sub of c.sub ?? []) walk(sub);
  };
  for (const c of view.conclusions) walk(c);
  return out;
}

/**
 * A theorem/lemma or Prop-valued definition as shared parameters plus one card
 * per top-level conjunct of its proposition, each card recursively fine-grained. Returns `null` —
 * the caller then shows the raw statement — for anything it cannot reproduce
 * exactly.
 *
 * `citedNames` (short and fully-qualified names of the paper's cited external
 * results) re-chips the hypotheses that assume one.
 */
export function structureStatementView(
  rawSource: string,
  citedNames: ReadonlySet<string> = new Set(),
): StructuredView | null {
  const scan = scanPropositionSignature(rawSource);
  if (!scan) return null;

  const sharedHyps: HypRow[] = [];
  for (const g of scan.groups) {
    const parsed = parseBinderGroup(g.raw);
    if (!parsed) return null; // one unparseable binder aborts the whole view
    sharedHyps.push({ chip: parsed.chip, code: dedent(g.raw) });
  }

  const goal = scan.cleaned.slice(
    scan.conclusionStart,
    scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd,
  );
  if (!goal.trim()) return null;

  // A goal's own leading `∀`/`premise →` prefix is as much a hypothesis of the
  // theorem as a binder group is, so it joins the shared rows; what remains is
  // the proposition that may split into conjuncts.
  const outer = liftTelescope(goal);
  sharedHyps.push(...outer.hyps);

  const conclusions: ConclusionCard[] = [];
  const recons: string[] = [];
  for (const c of conjunctsOf(outer.inner) ?? [outer.inner]) {
    const built = buildCard(c, 0);
    if (!built) return null;
    conclusions.push(built.card);
    recons.push(built.recon);
  }
  if (conclusions.length === 0) return null;

  // Nothing may be dropped. Rebuild the signature from exactly the pieces the
  // view will render — recursively, through every nested card — and require it
  // to match the source token for token; a structured view that silently loses
  // a conjunct or a binder is worse than no structured view at all.
  const rebuilt = scan.groups.map((g) => g.raw).join("") + scan.goalPrefix + outer.prefix + recons.join("∧") + outer.suffix;
  const original = scan.cleaned.slice(
    scan.telescopeStart,
    scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd,
  );
  if (squash(rebuilt) !== squash(original)) return null;
  const view = { sharedHyps, conclusions };
  markCitedHyps(allHypRows(view), citedNames);
  return view;
}

/**
 * What the shared table stores for a declaration.
 *
 * The drawer's job is a CHECKABLE STATEMENT, so a theorem/lemma keeps its
 * docstring and signature through the goal and drops the proof: the proofs of
 * helpers a reader was pulled into are noise, the verification badges already
 * say they went through, and each row carries file+line to the real source. A
 * `def`/`abbrev`/`structure`/`instance`/`inductive` keeps its whole source,
 * because there the body IS the statement.
 */

// ---------------------------------------------------------------------------
// row identity (added for the P4 artifact; not part of the ported code)

/** Every addressable row of a structured view, in READING order: shared
 *  hypotheses first, then each conclusion card's own hypotheses and its content
 *  row (its `intro` when it nests, its `code` when it is a leaf), depth-first.
 *  Stamps `id` in place and returns the rows in the same order. */
export function assignRowIds(view: StructuredView): Array<{ id: string; kind: "hyp" | "conclusion"; code: string }> {
  const out: Array<{ id: string; kind: "hyp" | "conclusion"; code: string }> = [];
  let n = 0;
  const next = () => `r${++n}`;
  const hyp = (row: HypRow) => {
    row.id = next();
    out.push({ id: row.id, kind: "hyp", code: row.code });
  };
  for (const h of view.sharedHyps) hyp(h);
  const walk = (card: ConclusionCard) => {
    for (const h of card.hyps) hyp(h);
    // A purely BRANCHING card — one that only splits into `sub`, with neither an
    // `intro` nor a `code` of its own — has no content row for the renderer to
    // draw, so giving it an id would invent a row nothing can highlight.
    const content = card.intro ?? card.code;
    if (content !== undefined && content.length > 0) {
      card.id = next();
      out.push({ id: card.id, kind: "conclusion", code: content });
    }
    for (const c of card.sub ?? []) walk(c);
  };
  for (const c of view.conclusions) walk(c);
  return out;
}
