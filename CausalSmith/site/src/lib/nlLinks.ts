/**
 * NL↔Lean crosslinks for a paper's formal blocks — the closed-world (`v3`)
 * artifact.
 *
 * Earlier versions handed the site a phrase of prose and a fragment of Lean and
 * left it to find both again: verbatim substring search, whitespace-normalised
 * run matching, shortest-covering-run selection, and snap policies to keep a
 * wrap from splitting a tag or a formula. Every one of those was a guess about
 * text the pipeline had already parsed, and each guess needed its own guard.
 *
 * `v3` inverts that. The pipeline emits, per block, the structured statement it
 * already built (rows carrying stable ids), the exact byte ranges of the prose
 * segments, and the assignment of rows to segments. The site's job shrinks to:
 * check the offsets are sane, then wrap them. Nothing is searched for, so
 * nothing can be found in the wrong place.
 *
 * What remains here is that validation — offsets in bounds, non-overlapping,
 * and landing neither inside a tag nor inside a formula (a `data-xl` boundary
 * inside a `<span class="math …">` is eaten when KaTeX re-renders it at build
 * time). A block whose offsets fail is dropped whole, with a warning: the paper
 * renders exactly as it would without crosslinks, never with broken HTML.
 */

import { createHash } from "node:crypto";

import type { ConclusionCard, HypRow, StructuredView } from "./paperLean.js";

/**
 * The only artifact format this understands. `v3` is the closed-world contract:
 * the pipeline supplies structure and offsets, the site does not search.
 */
export const NL_LINKS_POLICY = "nl-links-v3";

/** A byte range of a block's inner HTML that can be highlighted. */
export interface NlSegment {
  id: string;
  /** `display` marks a whole display formula, wrapped as one atom. */
  kind: "text" | "display";
  start: number;
  end: number;
  /** Element names open at `start`, outermost first. Pandoc wraps every
   *  sentence in a `<p>`, so a segment almost always begins inside something;
   *  this records what, and is checked against the real markup on read. */
  openPath: string[];
}

/** Which prose segments state a given row of the structured statement. */
export interface NlAssignment {
  /** Id of a `HypRow` or `ConclusionCard` in the block's `structured` tree. */
  row: string;
  segments: string[];
  /** The row has no counterpart in the prose — the paper does not state it. */
  unstated?: boolean;
}

/** What a display formula corresponds to in Lean. */
export interface NlDisplayLink {
  segment: string;
  /** The declaration the formula defines; absent when presentation-only. */
  decl?: string;
  /** The formula is exposition, with no Lean counterpart. */
  presentationOnly?: boolean;
}

/** Everything the artifact says about one crosswalk block. */
export interface NlBlock {
  /** The pipeline's own structured view; `null` leaves the site to parse. */
  structured: StructuredView | null;
  segments: NlSegment[];
  assignments: NlAssignment[];
  displayLinks: NlDisplayLink[];
  /** Raw sha256 of the block inner HTML the offsets were measured against. */
  digest: string;
  /** Exact `.length` of that same inner HTML — a cheap pre-check that fails
   *  before the hash is computed, and names the discrepancy when it does. */
  byteLength: number;
  /** The block deliberately assigns no rows (a definition with only display
   *  links). Without it, every row must be accounted for. */
  rowless?: boolean;
}

export interface NlLinkTable {
  commit: string;
  policy: string;
  /** Which paper this artifact was written for. Bundles share repo commits, so
   *  the commit alone does not identify one. */
  qid: string;
  spec: string;
  /** obj_id → its block. */
  blocks: Record<string, NlBlock>;
  /** Blocks that failed the closed-world contract on read, with the reason. */
  dropped: NlLinkProblem[];
}

/** What the artifact must be bound to for its blocks to be applied. */
export interface NlLinkBinding {
  commit?: string;
  qid?: string;
  spec?: string;
}

/** A block the site declined to apply, and why. */
export interface NlLinkProblem {
  objId: string;
  reason: string;
}

/**
 * The digest the pipeline stamps on a block: a raw sha256 of the block's inner
 * HTML, byte for byte.
 *
 * Deliberately NOT the pipeline's `hashEnvBody`, which collapses whitespace to
 * ignore prose reflow. That is right where it guards drift and wrong here: this
 * guards byte OFFSETS, and a pure reflow moves every one of them while leaving
 * a whitespace-insensitive hash equal.
 */
export function blockDigest(inner: string): string {
  return createHash("sha256").update(inner).digest("hex");
}

// ---------------------------------------------------------------------------
// parsing — every field is external data, so every field is checked
// ---------------------------------------------------------------------------

const CHIPS = new Set(["hyp", "decl", "cited"]);
/** Guards against a pathologically nested (or cyclic-by-construction) tree. */
const MAX_CARD_NESTING = 8;

function str(v: unknown): string | undefined {
  return typeof v === "string" && v.length > 0 ? v : undefined;
}

/** A field that is present but of the wrong type is a malformed artifact, not
 *  an absent field: silently reading it as absent turns a producer bug into a
 *  quietly wrong page. */
function presentNonString(v: unknown): boolean {
  // `null` counts as present-and-wrong: the producer never emits null, so a
  // null here is a malformed artifact, not an omitted optional.
  return v !== undefined && typeof v !== "string";
}

/** The discriminators are permitted only as literal `true`. `false`, `0`, `"no"`
 *  — anything else — is a schema violation rather than a soft "no". */
function badFlag(v: unknown): boolean {
  return v !== undefined && v !== true;
}

/** An id becomes half of a `<obj_id>#<id>` token in a space-separated list, so
 *  it can be neither empty nor whitespace-bearing. */
function id(v: unknown): string | undefined {
  const t = str(v);
  return t !== undefined && !/\s/.test(t) ? t : undefined;
}

function coerceHypRow(raw: unknown): HypRow | null {
  if (!raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  if (typeof r.code !== "string") return null;
  if (typeof r.chip !== "string" || !CHIPS.has(r.chip)) return null;
  if (presentNonString(r.id)) return null;
  const row: HypRow = { chip: r.chip as HypRow["chip"], code: r.code };
  const rid = id(r.id);
  if (rid) row.id = rid;
  return row;
}

function coerceCard(raw: unknown, depth: number): ConclusionCard | null {
  if (depth > MAX_CARD_NESTING || !raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  const hyps: HypRow[] = [];
  for (const h of Array.isArray(r.hyps) ? r.hyps : []) {
    const row = coerceHypRow(h);
    if (!row) return null;
    hyps.push(row);
  }
  if (presentNonString(r.id) || presentNonString(r.intro) || presentNonString(r.code)) return null;
  const card: ConclusionCard = { hyps };
  const cid = id(r.id);
  if (cid) card.id = cid;
  const intro = str(r.intro);
  if (intro) card.intro = intro;
  if (r.id !== undefined && !cid) return null; // present but empty or whitespace-bearing

  const hasCode = typeof r.code === "string";
  const hasSub = Array.isArray(r.sub) && r.sub.length > 0;
  // Exactly one of `code`/`sub` — the invariant the renderer relies on.
  if (hasCode === hasSub) return null;
  if (hasCode) {
    card.code = r.code as string;
  } else {
    const sub: ConclusionCard[] = [];
    for (const c of r.sub as unknown[]) {
      const child = coerceCard(c, depth + 1);
      if (!child) return null;
      sub.push(child);
    }
    card.sub = sub;
  }
  return card;
}

function coerceStructured(raw: unknown): StructuredView | null {
  if (!raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  if (!Array.isArray(r.sharedHyps) || !Array.isArray(r.conclusions)) return null;
  const sharedHyps: HypRow[] = [];
  for (const h of r.sharedHyps) {
    const row = coerceHypRow(h);
    if (!row) return null;
    sharedHyps.push(row);
  }
  const conclusions: ConclusionCard[] = [];
  for (const c of r.conclusions) {
    const card = coerceCard(c, 0);
    if (!card) return null;
    conclusions.push(card);
  }
  return conclusions.length > 0 ? { sharedHyps, conclusions } : null;
}

/**
 * Every CONTENT-BEARING row id in a structured view, in order, so duplicates
 * are visible.
 *
 * A card that only branches — `sub` with no `intro` and no `code` — renders
 * nothing of its own: it is a bracket around its children. It therefore has no
 * id, is not assignable, and must not be counted as an unaccounted-for row.
 */
function rowIds(view: StructuredView): (string | undefined)[] {
  const out: (string | undefined)[] = [];
  const walk = (card: ConclusionCard) => {
    for (const h of card.hyps) out.push(h.id);
    if (cardHasContent(card)) out.push(card.id);
    for (const sub of card.sub ?? []) walk(sub);
  };
  for (const h of view.sharedHyps) out.push(h.id);
  for (const c of view.conclusions) walk(c);
  return out;
}

/** A card renders a row of its own — its `intro` when it nests, its `code` when
 *  it is a leaf. A purely branching card renders neither. */
function cardHasContent(card: ConclusionCard): boolean {
  return card.intro !== undefined || card.code !== undefined;
}

/**
 * Reads one block, or says why it cannot be trusted.
 *
 * This is a CLOSED world: the artifact claims to account for the whole block,
 * so the contract is checked in full rather than salvaged in part. Every row is
 * assigned exactly once, every display formula is linked exactly once, every id
 * referenced exists, and no id is used twice. Half-consuming a malformed block
 * would leave rows silently untokened and formulas silently unlinked — the
 * reader could not tell that from a paper which genuinely says nothing about
 * them, which is precisely the confusion this artifact exists to remove.
 */
function coerceBlock(raw: unknown): { block: NlBlock } | { reason: string } {
  if (!raw || typeof raw !== "object" || Array.isArray(raw)) return { reason: "block is not an object" };
  const r = raw as Record<string, unknown>;

  if (presentNonString(r.digest)) return { reason: "`digest` is present but not a string" };
  const digest = str(r.digest);
  if (!digest) return { reason: "block carries no digest" };
  if (!Number.isInteger(r.byteLength) || (r.byteLength as number) < 0) {
    return { reason: "block carries no byteLength" };
  }
  const byteLength = r.byteLength as number;
  // Like the leaf discriminators, `rowless` is permitted only as literal true:
  // the producer never writes `rowless: false`, so its presence is malformed.
  if (r.rowless !== undefined && r.rowless !== true) return { reason: "`rowless` is present but not literal true" };
  const rowless = r.rowless === true;

  // Absent lists are NOT defaulted: an artifact that omits one is not making
  // the empty claim, it is malformed.
  for (const field of ["segments", "assignments", "displayLinks"]) {
    if (!Array.isArray(r[field])) return { reason: `\`${field}\` is missing or not an array` };
  }

  const segments: NlSegment[] = [];
  const segById = new Map<string, NlSegment>();
  for (const s of r.segments as unknown[]) {
    if (!s || typeof s !== "object") return { reason: "a segment is not an object" };
    const seg = s as Record<string, unknown>;
    if (presentNonString(seg.id)) return { reason: "a segment's id is present but not a string" };
    if (presentNonString(seg.kind)) return { reason: "a segment's kind is present but not a string" };
    const sid = id(seg.id);
    if (!sid) return { reason: "a segment has no id, or its id contains whitespace" };
    if (segById.has(sid)) return { reason: `duplicate segment id "${sid}"` };
    if (seg.kind !== "text" && seg.kind !== "display") return { reason: `segment "${sid}" has an unknown kind` };
    if (!Number.isInteger(seg.start) || !Number.isInteger(seg.end)) {
      return { reason: `segment "${sid}" has non-integer offsets` };
    }
    if (!Array.isArray(seg.openPath) || seg.openPath.some((n) => typeof n !== "string")) {
      return { reason: `segment "${sid}" has no openPath` };
    }
    const parsed: NlSegment = {
      id: sid,
      kind: seg.kind,
      start: seg.start as number,
      end: seg.end as number,
      openPath: (seg.openPath as string[]).map((n) => n.toLowerCase()),
    };
    segments.push(parsed);
    segById.set(sid, parsed);
  }

  // The producer TILES the block: the segments partition its inner HTML end to
  // end. Checking that here turns a dropped or misaligned segment into a loud
  // failure instead of a silent hole in the middle of a paragraph.
  if (segments.length === 0) {
    // An empty list tiles an empty block and nothing else. Letting it through
    // for a real block would mean claiming total coverage of prose while
    // addressing none of it.
    if (byteLength > 0) return { reason: `block has ${byteLength} bytes but no segments` };
  } else {
    const sorted = [...segments].sort((a, b) => a.start - b.start);
    if (sorted[0].start !== 0) return { reason: `segments start at ${sorted[0].start}, not 0` };
    for (let i = 1; i < sorted.length; i++) {
      if (sorted[i].start !== sorted[i - 1].end) {
        return {
          reason: `segments do not tile: "${sorted[i - 1].id}" ends at ${sorted[i - 1].end} but "${sorted[i].id}" starts at ${sorted[i].start}`,
        };
      }
    }
    const last = sorted[sorted.length - 1];
    if (last.end !== byteLength) {
      return { reason: `segments end at ${last.end}, not the block's ${byteLength} bytes` };
    }
  }


  let structured: StructuredView | null = null;
  if (r.structured !== undefined && r.structured !== null) {
    structured = coerceStructured(r.structured);
    if (!structured) return { reason: "`structured` is not a readable statement tree" };
    const ids = rowIds(structured);
    if (ids.some((x) => x === undefined)) {
      return { reason: "a content-bearing row in `structured` has no id" };
    }
    const seen = new Set<string>();
    for (const id of ids as string[]) {
      if (seen.has(id)) return { reason: `duplicate row id "${id}"` };
      seen.add(id);
    }
  }
  const known = structured ? new Set(rowIds(structured) as string[]) : new Set<string>();

  // `rowless` and a statement tree are exclusive: the flag says "this block has
  // no rows to assign", so a tree alongside it is a contradiction, and its
  // absence without the flag is an omission rather than a claim. Checked before
  // the assignments so the structural complaint wins over a downstream symptom.
  if (rowless && structured) return { reason: "block is `rowless` but carries a structured tree" };
  if (!rowless && !structured) return { reason: "block has no `structured` tree and is not marked rowless" };
  if (rowless && (r.assignments as unknown[]).length > 0) {
    return { reason: "block is `rowless` but carries assignments" };
  }

  const assignments: NlAssignment[] = [];
  const assigned = new Set<string>();
  for (const a of r.assignments as unknown[]) {
    if (!a || typeof a !== "object") return { reason: "an assignment is not an object" };
    const asg = a as Record<string, unknown>;
    if (presentNonString(asg.row)) return { reason: "an assignment's row is present but not a string" };
    if (badFlag(asg.unstated)) return { reason: "`unstated` is present but not literal true" };
    const row = id(asg.row);
    if (!row) return { reason: "an assignment names no row, or the row id contains whitespace" };
    if (!known.has(row)) return { reason: `assignment names unknown row "${row}"` };
    if (assigned.has(row)) return { reason: `row "${row}" is assigned more than once` };
    assigned.add(row);
    if (asg.unstated === true) {
      // `unstated` means the paper says nothing about this row; a segment list
      // says where it does. Both at once is a contradiction, not a preference.
      if (asg.segments !== undefined) {
        return { reason: `row "${row}" is marked unstated but also carries segments` };
      }
      assignments.push({ row, segments: [], unstated: true });
      continue;
    }
    if (!Array.isArray(asg.segments)) return { reason: `assignment for "${row}" has no segment list` };
    const segs = asg.segments.filter((x): x is string => typeof x === "string");
    if (segs.length !== asg.segments.length) return { reason: `assignment for "${row}" has a non-string segment` };
    // A stated row with no segments says nothing; `unstated` is how "the paper
    // does not state this" is expressed, and the difference matters to a reader.
    if (segs.length === 0) return { reason: `row "${row}" is stated but has no segments (use unstated)` };
    for (const id of segs) {
      if (!segById.has(id)) return { reason: `assignment for "${row}" names unknown segment "${id}"` };
    }
    assignments.push({ row, segments: segs });
  }
  if (!rowless) {
    for (const id of known) {
      if (!assigned.has(id)) return { reason: `row "${id}" is not accounted for (assign it or mark the block rowless)` };
    }
  }

  const displayLinks: NlDisplayLink[] = [];
  /** segment id → how it is linked, so the decl/presentation XOR can be seen. */
  const linked = new Map<string, { decls: number; quiet: number }>();
  for (const d of r.displayLinks as unknown[]) {
    if (!d || typeof d !== "object") return { reason: "a displayLink is not an object" };
    const dl = d as Record<string, unknown>;
    if (presentNonString(dl.segment)) return { reason: "a displayLink's segment is present but not a string" };
    if (presentNonString(dl.decl)) return { reason: "a displayLink's decl is present but not a string" };
    if (badFlag(dl.presentationOnly)) return { reason: "`presentationOnly` is present but not literal true" };
    const segment = id(dl.segment);
    if (!segment) return { reason: "a displayLink names no segment, or the id contains whitespace" };
    const seg = segById.get(segment);
    if (!seg) return { reason: `displayLink names unknown segment "${segment}"` };
    if (seg.kind !== "display") return { reason: `displayLink targets non-display segment "${segment}"` };
    const tally = linked.get(segment) ?? { decls: 0, quiet: 0 };
    linked.set(segment, tally);
    const decl = str(dl.decl);
    // A formula either has a Lean counterpart or is exposition; claiming both
    // leaves the reader's hover with two incompatible meanings.
    if (decl && dl.presentationOnly === true) {
      return { reason: `displayLink for "${segment}" is both a decl and presentationOnly` };
    }
    if (decl) {
      // A display may show several constants at once, so more than one decl
      // entry per segment is expected; they share the segment's single token.
      tally.decls++;
      displayLinks.push({ segment, decl });
    } else if (dl.presentationOnly === true) {
      tally.quiet++;
      displayLinks.push({ segment, presentationOnly: true });
    } else {
      return { reason: `displayLink for "${segment}" has neither a decl nor presentationOnly` };
    }
  }
  for (const [segment, tally] of linked) {
    // Exposition or Lean, never both, and "exposition" is said exactly once.
    if (tally.decls > 0 && tally.quiet > 0) {
      return { reason: `display segment "${segment}" is both linked to decls and marked presentationOnly` };
    }
    if (tally.quiet > 1) return { reason: `display segment "${segment}" is marked presentationOnly twice` };
  }
  for (const seg of segments) {
    if (seg.kind === "display" && !linked.has(seg.id)) {
      return { reason: `display segment "${seg.id}" is not accounted for in displayLinks` };
    }
  }

  const block: NlBlock = { structured, segments, assignments, displayLinks, digest, byteLength };
  if (rowless) block.rowless = true;
  return { block };
}

/**
 * Parses the artifact, returning `null` for anything unrecognisable.
 *
 * `expect`, when given, BINDS the artifact to one bundle: its offsets index one
 * particular rendering of one particular paper body, so an artifact written for
 * another paper — or another revision of this one — would land its spans at
 * meaningless positions. The commit alone is not enough, since bundles share
 * repo commits, hence qid and spec too.
 */
export function parseNlLinks(raw: unknown, expect?: NlLinkBinding): NlLinkTable | null {
  if (!raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  if (r.policy !== NL_LINKS_POLICY) return null;
  if (expect?.commit !== undefined && r.commit !== expect.commit) return null;
  if (expect?.qid !== undefined && r.qid !== expect.qid) return null;
  if (expect?.spec !== undefined && r.spec !== expect.spec) return null;

  const container = r.blocks;
  if (!container || typeof container !== "object" || Array.isArray(container)) return null;

  const blocks: Record<string, NlBlock> = {};
  const dropped: NlLinkProblem[] = [];
  for (const [objId, value] of Object.entries(container as Record<string, unknown>)) {
    const read = coerceBlock(value);
    if ("block" in read) blocks[objId] = read.block;
    else dropped.push({ objId, reason: read.reason });
  }
  return {
    commit: typeof r.commit === "string" ? r.commit : "",
    policy: typeof r.policy === "string" ? r.policy : "",
    qid: typeof r.qid === "string" ? r.qid : "",
    spec: typeof r.spec === "string" ? r.spec : "",
    blocks,
    dropped,
  };
}

// ---------------------------------------------------------------------------
// minimal HTML scanning — enough to tell text from markup, not a parser
// ---------------------------------------------------------------------------

interface TagToken {
  start: number;
  /** Index just past the `>`. */
  end: number;
  name: string;
  closing: boolean;
  selfClosing: boolean;
}

/** Index just past the `>` ending the tag opening at `lt`, skipping quoted
 *  attribute values (a `>` inside `title="a > b"` does not end the tag). */
function endOfTag(html: string, lt: number): number {
  let quote = "";
  for (let i = lt + 1; i < html.length; i++) {
    const c = html[i];
    if (quote) {
      if (c === quote) quote = "";
    } else if (c === '"' || c === "'") {
      quote = c;
    } else if (c === ">") {
      return i + 1;
    }
  }
  return -1;
}

/** Every tag in `html`, in order. Comments are skipped; a bare `<` in text is
 *  passed over rather than guessed at. */
function scanTags(html: string): TagToken[] {
  const out: TagToken[] = [];
  let i = 0;
  while (i < html.length) {
    const lt = html.indexOf("<", i);
    if (lt < 0) break;
    if (html.startsWith("<!--", lt)) {
      const close = html.indexOf("-->", lt);
      i = close < 0 ? html.length : close + 3;
      continue;
    }
    const m = /^<(\/?)([A-Za-z][A-Za-z0-9-]*)/.exec(html.slice(lt, lt + 64));
    if (!m) {
      i = lt + 1;
      continue;
    }
    const end = endOfTag(html, lt);
    if (end < 0) break;
    out.push({
      start: lt,
      end,
      name: m[2].toLowerCase(),
      closing: m[1] === "/",
      selfClosing: html[end - 2] === "/",
    });
    i = end;
  }
  return out;
}

/**
 * The inner-HTML range of the paper BLOCK for `objId`.
 *
 * `data-objid` is not unique in the body: an inline `<span class="leanref"
 * data-objid="…">` cross-reference to a result normally appears in the prose
 * BEFORE the block it points at. Only `<div class="formal-block …">` counts —
 * the same element the pipeline's own `extractBlockHtml` keys on, and the one
 * its segment offsets are measured against.
 */
export function findBlockInner(html: string, objId: string): { start: number; end: number } | null {
  const marker = `data-objid="${objId}"`;
  for (let at = html.indexOf(marker); at >= 0; at = html.indexOf(marker, at + 1)) {
    const lt = html.lastIndexOf("<", at);
    if (lt < 0) continue;
    const openEnd = endOfTag(html, lt);
    if (openEnd < 0 || openEnd <= at || html[openEnd - 2] === "/") continue; // unterminated or empty
    const tag = html.slice(lt, openEnd);
    const m = /^<([A-Za-z][A-Za-z0-9-]*)/.exec(tag);
    if (!m || m[1].toLowerCase() !== "div") continue;
    if (!/\sclass="[^"]*\bformal-block\b/.test(tag)) continue;
    let depth = 1;
    for (const t of scanTags(html)) {
      if (t.start < openEnd || t.name !== "div") continue;
      if (t.closing) {
        depth--;
        if (depth === 0) return { start: openEnd, end: t.start };
      } else if (!t.selfClosing) {
        depth++;
      }
    }
    return null; // never closed — leave the document alone
  }
  return null;
}

// ---------------------------------------------------------------------------
// formulas are atomic
// ---------------------------------------------------------------------------

/**
 * Pandoc emits formulas as `<span class="math inline">\(…\)</span>`, and the
 * page re-renders each one through KaTeX at build time (`paperMath.ts`) with a
 * non-greedy `…</span>` regex — so a `data-xl` boundary placed inside one
 * truncates the match and the span silently disappears from the rendered page.
 * The artifact's segments are math-atomic by construction; this is the check
 * that they really are.
 */
function isMathStart(html: string, t: TagToken): boolean {
  return !t.closing && t.name === "span" && /^<span\s+class="math[\s"]/.test(html.slice(t.start, t.end));
}

/** Elements with no closing tag, so they never enter the open-element path. */
const VOID_ELEMENTS = new Set([
  "area", "base", "br", "col", "embed", "hr", "img", "input",
  "link", "meta", "param", "source", "track", "wbr",
]);

interface MathRange {
  start: number;
  end: number;
  /** A `math display` block, as opposed to an inline `\(…\)` symbol. */
  display: boolean;
}

/** Full ranges (start tag through end tag) of every math element in `html`. */
function mathRanges(html: string, tags: readonly TagToken[]): MathRange[] {
  const out: MathRange[] = [];
  for (let i = 0; i < tags.length; i++) {
    if (!isMathStart(html, tags[i])) continue;
    const display = /\bdisplay\b/.test(html.slice(tags[i].start, tags[i].end));
    let depth = 1;
    for (let j = i + 1; j < tags.length; j++) {
      const u = tags[j];
      if (u.name !== "span" || u.selfClosing) continue;
      depth += u.closing ? -1 : 1;
      if (depth === 0) {
        out.push({ start: tags[i].start, end: u.end, display });
        break;
      }
    }
  }
  return out;
}

/**
 * Counts `data-xl` boundaries sitting inside a formula in FINISHED HTML — the
 * invariant `applyNlLinks` must leave behind, checkable directly on its output.
 * A math element's content is plain (entity-escaped) TeX, so any markup between
 * its tags is a boundary that KaTeX will eat.
 */
export function mathBoundaryViolations(html: string): number {
  const tags = scanTags(html);
  let bad = 0;
  for (let i = 0; i < tags.length; i++) {
    if (!isMathStart(html, tags[i])) continue;
    let depth = 1;
    for (let j = i + 1; j < tags.length; j++) {
      const u = tags[j];
      if (u.name !== "span" || u.selfClosing) continue;
      depth += u.closing ? -1 : 1;
      if (depth === 0) {
        if (html.slice(tags[i].end, u.start).includes("<")) bad++;
        break;
      }
    }
  }
  return bad;
}

// ---------------------------------------------------------------------------
// the transform
// ---------------------------------------------------------------------------

/** The element names open at `pos`, outermost first. Void and self-closing
 *  elements never enter it, since they never close. */
function openStackAt(tags: readonly TagToken[], pos: number): string[] {
  const stack: string[] = [];
  for (const t of tags) {
    if (t.start >= pos) break;
    if (t.selfClosing || VOID_ELEMENTS.has(t.name)) continue;
    if (t.closing) {
      const i = stack.lastIndexOf(t.name);
      if (i >= 0) stack.splice(i, 1);
    } else {
      stack.push(t.name);
    }
  }
  return stack;
}

/**
 * The text runs of `[start, end)`: the range chopped at every tag boundary it
 * contains, so each piece can be wrapped in its own span.
 *
 * This is what makes a segment safe to highlight without requiring it to
 * balance its own tags. A run never crosses a tag, so a span around one is
 * always well-formed. A math element is the exception: its tags are NOT split
 * points, because KaTeX re-renders the formula from its raw TeX and a span
 * boundary inside it would be eaten — the formula travels as one atom.
 */
function textRuns(
  tags: readonly TagToken[],
  math: readonly MathRange[],
  start: number,
  end: number,
): { s: number; e: number }[] {
  const runs: { s: number; e: number }[] = [];
  let cursor = start;
  for (const t of tags) {
    if (t.start < start || t.end > end) continue;
    if (math.some((m) => t.start >= m.start && t.end <= m.end)) continue;
    if (t.start > cursor) runs.push({ s: cursor, e: t.start });
    cursor = Math.max(cursor, t.end);
  }
  if (end > cursor) runs.push({ s: cursor, e: end });
  return runs.filter((r) => r.e > r.s);
}

/**
 * Why this block's offsets cannot be trusted, or `null` if they can.
 *
 * Offsets are computed by the pipeline against the same block HTML, so this is
 * a cheap consistency check, not a search: it catches a body rewritten since
 * the artifact was authored, which would otherwise scatter spans across
 * unrelated text or into the middle of a tag.
 */
function validateSegments(inner: string, block: NlBlock): string | null {
  // Checked before the digest because it is the sharper instrument: the digest
  // collapses whitespace, so a reflow that shifts every offset leaves it equal
  // while the length moves.
  if (inner.length !== block.byteLength) {
    return `block HTML is ${inner.length} bytes, not the ${block.byteLength} the offsets were measured against`;
  }
  const actual = blockDigest(inner);
  if (actual !== block.digest) {
    // The offsets index bytes that are no longer there. Nothing downstream can
    // recover from that, and applying them anyway would highlight arbitrary
    // text — so the block goes, whole.
    return `block HTML has changed since the artifact was written (digest ${block.digest.slice(0, 12)}… vs ${actual.slice(0, 12)}…)`;
  }
  const tags = scanTags(inner);
  const math = mathRanges(inner, tags);
  for (const s of block.segments) {
    if (s.start < 0 || s.end > inner.length || s.start >= s.end) {
      return `segment ${s.id} is out of bounds (${s.start}..${s.end} of ${inner.length})`;
    }
    for (const t of tags) {
      if ((s.start > t.start && s.start < t.end) || (s.end > t.start && s.end < t.end)) {
        return `segment ${s.id} starts or ends inside a tag`;
      }
    }
    for (const m of math) {
      if ((s.start > m.start && s.start < m.end) || (s.end > m.start && s.end < m.end)) {
        return `segment ${s.id} starts or ends inside a formula`;
      }
    }
    // Segments are NOT required to balance their own tags — pandoc wraps every
    // sentence and every display in a `<p>`, so demanding balance left almost
    // nothing addressable. Instead the artifact declares what was open where it
    // starts, and that claim is checked against the real markup; wrapping then
    // splits at tag boundaries so the output is well-formed regardless.
    const actualPath = openStackAt(tags, s.start);
    if (actualPath.join(">") !== s.openPath.join(">")) {
      return `segment ${s.id} claims openPath [${s.openPath.join(", ")}] but sits inside [${actualPath.join(", ")}]`;
    }
    // A `display` segment must BE a display formula, not merely contain or
    // abut one: the UI treats it as an atom and the decl link hangs off it.
    if (s.kind === "display") {
      const exact = math.find((m) => m.start === s.start && m.end === s.end);
      if (!exact) return `segment ${s.id} is marked display but is not a math element`;
      if (!exact.display) return `segment ${s.id} is marked display but the formula is inline`;
    }
  }
  const sorted = [...block.segments].sort((a, b) => a.start - b.start);
  for (let i = 1; i < sorted.length; i++) {
    if (sorted[i].start < sorted[i - 1].end) {
      return `segments ${sorted[i - 1].id} and ${sorted[i].id} overlap`;
    }
  }
  return null;
}

/**
 * Checks every block against the body it claims to index, returning only the
 * blocks that survive.
 *
 * Both halves of the crosslink — the prose spans and the Lean-side tokens —
 * must be built from the SAME set of blocks, or a dropped block would leave
 * tokens on rows with nothing in the paper to light up. So validation happens
 * once, here, and the caller feeds the survivors to both.
 */
export function validateBlocks(
  bodyHtml: string,
  blocks: Record<string, NlBlock>,
): { blocks: Record<string, NlBlock>; problems: NlLinkProblem[] } {
  const ok: Record<string, NlBlock> = {};
  const problems: NlLinkProblem[] = [];
  for (const objId of Object.keys(blocks).sort()) {
    // Tokens live in a space-separated list, so an id with whitespace in it
    // could never be word-matched back out. (`sym:` obj_ids do contain spaces.)
    if (/\s/.test(objId)) {
      problems.push({ objId, reason: "obj_id is not a single token" });
      continue;
    }
    const range = findBlockInner(bodyHtml, objId);
    if (!range) {
      problems.push({ objId, reason: "no such block in the body" });
      continue;
    }
    const invalid = validateSegments(bodyHtml.slice(range.start, range.end), blocks[objId]);
    if (invalid) problems.push({ objId, reason: invalid });
    else ok[objId] = blocks[objId];
  }
  return { blocks: ok, problems };
}

function escapeAttr(value: string): string {
  return value.replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;");
}

/** The crosslink token for one row of one block. */
export function rowToken(objId: string, rowId: string): string {
  return `${objId}#${rowId}`;
}

/** The crosslink token for one display formula — carried by the formula in the
 *  prose AND by the component it defines, so the pair lights both ways. */
export function segmentToken(objId: string, segmentId: string): string {
  return `${objId}#${segmentId}`;
}

/**
 * Wraps each assigned segment in a `<span>` carrying the rows it states.
 *
 * `data-xl` is a space-separated token list (HTML-class style, word-matched
 * with `[data-xl~="…"]`) because one segment can state several rows.
 * `data-xl-decl` names the declaration a display formula defines, and
 * `data-xl-presentation` marks a formula that is exposition with no Lean
 * counterpart. Pure: returns the new HTML plus the blocks it declined.
 */
export function applyNlLinks(
  bodyHtml: string,
  blocks: Record<string, NlBlock>,
): { html: string; skipped: NlLinkProblem[] } {
  const skipped: NlLinkProblem[] = [];
  const inserts: { at: number; open: boolean; text: string }[] = [];

  for (const objId of Object.keys(blocks).sort()) {
    const block = blocks[objId];
    const range = findBlockInner(bodyHtml, objId);
    if (!range) {
      skipped.push({ objId, reason: "no such block in the body" });
      continue;
    }

    const tokens = new Map<string, string[]>();
    const add = (segId: string, token: string) => {
      const list = tokens.get(segId) ?? [];
      if (!list.includes(token)) list.push(token);
      tokens.set(segId, list);
    };
    for (const a of block.assignments) {
      if (a.unstated) continue;
      for (const segId of a.segments) add(segId, rowToken(objId, a.row));
    }
    const decls = new Map<string, string[]>();
    const presentation = new Set<string>();
    for (const d of block.displayLinks) {
      if (d.decl) {
        // A formula can show several constants at once. They share the
        // segment's SINGLE token — minted once here, and put on each of their
        // component cards — so hovering the formula lights every one of them
        // and any one of them lights the formula.
        const list = decls.get(d.segment) ?? [];
        if (!list.includes(d.decl)) list.push(d.decl);
        decls.set(d.segment, list);
        add(d.segment, segmentToken(objId, d.segment));
      } else if (d.presentationOnly) {
        presentation.add(d.segment);
      }
    }

    const inner = bodyHtml.slice(range.start, range.end);
    const tags = scanTags(inner);
    const math = mathRanges(inner, tags);

    for (const seg of block.segments) {
      const rows = tokens.get(seg.id) ?? [];
      const decl = decls.get(seg.id);
      const quiet = presentation.has(seg.id);
      if (rows.length === 0 && !decl && !quiet) continue; // nothing to say about it
      const attrs = [
        rows.length > 0 ? ` data-xl="${escapeAttr(rows.join(" "))}"` : "",
        decl ? ` data-xl-decl="${escapeAttr(decl.join(" "))}"` : "",
        quiet ? " data-xl-presentation" : "",
      ].join("");
      // One span per text run, never one around the whole range: a segment may
      // begin inside a `<p>` and end outside it, and a single span there would
      // be malformed. Every run carries the SAME attributes — the shared token
      // is what makes them one highlight, so the reader can hover any part of a
      // phrase that straddles a paragraph break and light the whole pair.
      for (const run of textRuns(tags, math, seg.start, seg.end)) {
        inserts.push({ at: range.start + run.s, open: true, text: `<span${attrs}>` });
        inserts.push({ at: range.start + run.e, open: false, text: "</span>" });
      }
    }
  }

  // Applied right to left so earlier offsets stay valid. At one position the
  // OPEN tag is applied first, which leaves it to the right of the CLOSE — so
  // two adjacent spans render as `</span><span …>`, never interleaved.
  inserts.sort((a, b) => b.at - a.at || (a.open ? -1 : 1));
  let html = bodyHtml;
  for (const ins of inserts) html = html.slice(0, ins.at) + ins.text + html.slice(ins.at);
  return { html, skipped };
}
