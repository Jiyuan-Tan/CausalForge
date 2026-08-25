/**
 * Sentence segmenter for the rendered paper body — the DOM half of the
 * commenting system's anchoring layer.
 *
 * `segmentPaperBody` walks the prose blocks of a rendered paper and wraps each
 * sentence in a `<span class="cs-s" data-sid="b<i>-s<j>">`, returning the
 * ordered `SentenceRef[]` the pure engine (`lib/comments/anchor.ts`) re-anchors
 * stored quotes against. Nothing here decides where a sentence ends — that is
 * `segmentSentences`; this file only maps those string boundaries onto nodes.
 *
 * Three invariants keep the rendered page intact:
 *   • KaTeX subtrees are never re-parented in part. Only DIRECT children of a
 *     block are grouped, so any element child (a `.katex` span, an `<em>`, a
 *     `<code>`) is atomic; a sentence boundary that would fall inside one is
 *     pushed out to that element's edge.
 *   • A display-math block is one sentence, and is marked by putting the class
 *     on the block itself rather than wrapping its children — so
 *     `.katex-display > .katex` layout rules keep applying.
 *   • Every block is segmented inside its own try/catch and is skipped whole on
 *     any surprise. A paper that cannot be segmented still renders; its
 *     comments simply resolve as archived/page-level.
 */

import { normalize, segmentSentences, type SentenceRef } from "../lib/comments/anchor.js";

/** Class on every sentence wrapper. Highlights and hit-testing key on it. */
export const SENTENCE_CLASS = "cs-s";

/** Blocks whose text is offered for commenting. */
const BLOCK_SELECTOR = "p, li, blockquote, .katex-display, span.math.display";

/**
 * The structural half of BLOCK_SELECTOR — elements that CONTAIN prose.
 *
 * Only these make an enclosing candidate defer: a loose `<li>` wraps its text
 * in a `<p>`, so the `<p>` is the real block. Display math must NOT be on this
 * list. Pandoc emits `\[…\]` as a `.katex-display` span sitting INSIDE the
 * paragraph that discusses it, and treating that span as the block would skip
 * the surrounding prose entirely — which is exactly how a selection covering
 * prose and a formula ended up highlighting only the formula.
 */
const STRUCTURAL_SELECTOR = "p, li, blockquote";

/** Regions never segmented: chrome, navigation, code, headings, the comments UI. */
const EXCLUDE_SELECTOR = [
  ".paper-toc",
  ".paper-byline",
  ".formal-layer",
  ".drawer",
  ".cs-comments",
  "pre",
  "code",
  "h1",
  "h2",
  "h3",
  "h4",
  "h5",
  "h6",
].join(",");

/** Display math: one indivisible sentence. */
const DISPLAY_SELECTOR = ".katex-display, .math.display";

const TEXT_NODE = 3;
const ELEMENT_NODE = 1;

/**
 * Text a reader can actually see and select.
 *
 * KaTeX renders every formula TWICE: `.katex-mathml` holds an accessible MathML
 * mirror (which itself contains an `<annotation>` carrying the raw TeX source),
 * and `.katex-html` holds the glyphs on screen. `textContent` concatenates all
 * of it, so a one-character formula reports something like `nn\\,n` — invisible
 * characters that shift every offset and, worse, feed TeX punctuation to the
 * sentence splitter. Both passes below (the split and the node walk) must agree
 * on what the text IS, so both go through this.
 */
function visibleText(node: Node): string {
  if (node.nodeType === TEXT_NODE) return node.nodeValue ?? "";
  if (node.nodeType !== ELEMENT_NODE) return "";
  const el = node as Element;
  if (isInvisible(el)) return "";
  // Fast paths — a paper body is mostly KaTeX, and this runs over every node
  // several times, so avoid recursing where `textContent` already answers.
  if (el.querySelector(INVISIBLE_SELECTOR) === null) return el.textContent ?? "";
  if (el.classList !== undefined && el.classList.contains("katex")) {
    const html = el.querySelector(".katex-html");
    if (html) return html.textContent ?? "";
  }
  let out = "";
  for (const child of Array.from(el.childNodes)) out += visibleText(child);
  return out;
}

/** KaTeX's screen-reader mirror and the raw-TeX annotation inside it. */
const INVISIBLE_SELECTOR = ".katex-mathml, annotation";

function isInvisible(el: Element): boolean {
  return (
    (el.classList !== undefined && el.classList.contains("katex-mathml")) ||
    el.localName === "annotation"
  );
}

interface Unit {
  node: ChildNode;
  start: number;
  end: number;
  /** Element (or other non-text) child — never split. */
  atomic: boolean;
}

interface Range {
  start: number;
  end: number;
}

const isWs = (c: string): boolean => /\s/.test(c);

/**
 * Segment every prose block under `root`, wrapping sentences in place.
 *
 * Idempotent: a second call on an already-segmented root re-reads the existing
 * spans instead of wrapping again (the paper page can call it after a late
 * KaTeX fallback pass without doubling anything up).
 */
export function segmentPaperBody(root: HTMLElement): SentenceRef[] {
  if (root.dataset.csSegmented === "1") return collectExisting(root);
  root.dataset.csSegmented = "1";

  const refs: SentenceRef[] = [];
  const candidates = Array.from(root.querySelectorAll<HTMLElement>(BLOCK_SELECTOR)).filter(
    (b) => !b.closest(EXCLUDE_SELECTOR),
  );
  // Candidates that must stand aside because an inner prose container will do
  // the job better: segmenting a loose <li> would make its <p> a single atomic
  // unit and collapse the whole item into one sentence.
  const deferring = deferringBlocks(candidates);
  const claimed = new Set<Element>();
  let blockIndex = 0;

  for (const block of candidates) {
    if (deferring.has(block)) continue;
    // Already covered by an enclosing block — e.g. the `.katex-display` sitting
    // inside a paragraph that was just segmented, where the formula is one
    // atomic unit of that paragraph's prose.
    if (isInsideClaimed(block, claimed)) continue;
    if (block.querySelector(`.${SENTENCE_CLASS}`)) continue;
    claimed.add(block);
    try {
      const made = segmentBlock(block, blockIndex);
      if (made.length > 0) {
        refs.push(...made);
        blockIndex++;
      }
    } catch {
      /* unsegmentable block — leave its DOM untouched and move on */
    }
  }
  return refs;
}

/**
 * Candidates that contain another prose container.
 *
 * Computed by walking each structural candidate's ANCESTORS rather than each
 * candidate's descendants: a paper body is megabytes of KaTeX, and a descendant
 * scan per block is quadratic in exactly the pages that need it most.
 */
function deferringBlocks(candidates: Element[]): Set<Element> {
  const structural = candidates.filter((c) => c.matches(STRUCTURAL_SELECTOR));
  const structuralSet = new Set<Element>(structural);
  const deferring = new Set<Element>();
  for (const block of structural) {
    let parent = block.parentElement;
    while (parent) {
      if (structuralSet.has(parent)) deferring.add(parent);
      parent = parent.parentElement;
    }
  }
  return deferring;
}

function isInsideClaimed(block: Element, claimed: Set<Element>): boolean {
  let parent = block.parentElement;
  while (parent) {
    if (claimed.has(parent)) return true;
    parent = parent.parentElement;
  }
  return false;
}

/** Look up a sentence span by id. `sid` is validated, so it is never a selector. */
export function sidElement(sid: string, root: ParentNode = document): HTMLElement | null {
  if (!/^[A-Za-z0-9_-]{1,64}$/.test(sid)) return null;
  return root.querySelector<HTMLElement>(`.${SENTENCE_CLASS}[data-sid="${sid}"]`);
}

export type SidMap = Map<string, HTMLElement>;

/**
 * Build the sid → span map in ONE tree scan.
 *
 * The controller caches this once after segmentation, so highlight/hover/layout
 * never re-run `querySelectorAll('.cs-s')` (a full-tree scan that, over a paper
 * full of KaTeX, costs hundreds of ms — multiplied by every comment before this
 * cache existed).
 */
export function collectSidElements(root: ParentNode): SidMap {
  const map: SidMap = new Map();
  for (const el of Array.from(root.querySelectorAll<HTMLElement>(`.${SENTENCE_CLASS}[data-sid]`))) {
    const sid = el.dataset.sid;
    if (sid) map.set(sid, el);
  }
  return map;
}

function collectExisting(root: ParentNode): SentenceRef[] {
  return Array.from(root.querySelectorAll<HTMLElement>(`.${SENTENCE_CLASS}[data-sid]`)).map(
    (el) => ({ id: el.dataset.sid ?? "", text: normalize(visibleText(el)) }),
  );
}

/** A block that carries display math and nothing else stays one sentence. */
function isDisplayBlock(block: Element): boolean {
  if (block.matches(DISPLAY_SELECTOR)) return true;
  let sawDisplay = false;
  for (const node of Array.from(block.childNodes)) {
    if (node.nodeType === TEXT_NODE) {
      if ((node.nodeValue ?? "").trim()) return false;
      continue;
    }
    if (node.nodeType !== ELEMENT_NODE) continue;
    if ((node as Element).matches(DISPLAY_SELECTOR)) {
      sawDisplay = true;
      continue;
    }
    return false;
  }
  return sawDisplay;
}

function segmentBlock(block: HTMLElement, blockIndex: number): SentenceRef[] {
  const raw = visibleText(block);
  if (!normalize(raw)) return [];

  if (isDisplayBlock(block)) {
    const sid = `b${blockIndex}-s0`;
    block.classList.add(SENTENCE_CLASS);
    block.setAttribute("data-sid", sid);
    return [{ id: sid, text: normalize(raw) }];
  }

  const sentences = segmentSentences(raw);
  if (sentences.length === 0) return [];

  const units = topUnits(block);
  const ranges = buildRanges(raw, units, rawEnds(raw, sentences));
  if (ranges.length === 0) return [];
  return applyRanges(block, ranges, blockIndex);
}

/** Direct children with their offsets into the block's `textContent`. */
function topUnits(block: Element): Unit[] {
  const units: Unit[] = [];
  let off = 0;
  for (const node of Array.from(block.childNodes)) {
    // `visibleText` returns "" for comments/PIs, which contribute to
    // `node.textContent` but not to the parent's — so offsets stay aligned.
    const len = visibleText(node).length;
    units.push({ node, start: off, end: off + len, atomic: node.nodeType !== TEXT_NODE });
    off += len;
  }
  return units;
}

/**
 * Offsets into the RAW block text just past each sentence.
 *
 * `segmentSentences` works on whitespace-normalized text, so the sentence
 * strings cannot be matched by index; this replays them character by character
 * against the raw text, absorbing collapsed whitespace runs. A mismatch throws,
 * which skips the block.
 */
function rawEnds(raw: string, sentences: string[]): number[] {
  const ends: number[] = [];
  let i = 0;
  for (const sentence of sentences) {
    for (let k = 0; k < sentence.length; k++) {
      const ch = sentence[k];
      if (isWs(ch)) {
        const before = i;
        while (i < raw.length && isWs(raw[i])) i++;
        if (i === before) throw new Error("cs-segment: whitespace mismatch");
      } else {
        while (i < raw.length && isWs(raw[i])) i++;
        if (raw[i] !== ch) throw new Error("cs-segment: text mismatch");
        i++;
      }
    }
    ends.push(i);
  }
  return ends;
}

function unitCovering(units: Unit[], off: number): Unit | undefined {
  return units.find((u) => off >= u.start && off < u.end);
}

/**
 * Turn sentence end-offsets into wrappable ranges: boundaries inside an atomic
 * element move to that element's trailing edge (its leading character belongs
 * to the earlier sentence), and inter-sentence whitespace is left outside both
 * spans so a highlight does not carry a trailing blank.
 */
function buildRanges(raw: string, units: Unit[], ends: number[]): Range[] {
  const adjusted = ends.map((end) => {
    const u = unitCovering(units, end);
    return u && u.atomic && end > u.start ? u.end : end;
  });

  const insideAtomic = (off: number): boolean => {
    const u = unitCovering(units, off);
    return !!u && u.atomic;
  };

  const ranges: Range[] = [];
  let cursor = 0;
  for (const boundary of adjusted) {
    let start = cursor;
    while (start < raw.length && isWs(raw[start]) && !insideAtomic(start)) start++;
    let end = boundary;
    while (end > start && isWs(raw[end - 1]) && !insideAtomic(end - 1)) end--;
    cursor = Math.max(cursor, boundary);
    if (end <= start) {
      // Degenerate (two boundaries inside one atomic element): merge into the
      // previous sentence rather than emitting an empty span.
      const prev = ranges[ranges.length - 1];
      if (prev) prev.end = Math.max(prev.end, Math.min(boundary, raw.length));
      continue;
    }
    ranges.push({ start, end });
  }
  return ranges;
}

function applyRanges(block: HTMLElement, ranges: Range[], blockIndex: number): SentenceRef[] {
  const edges = new Set<number>();
  for (const r of ranges) {
    edges.add(r.start);
    edges.add(r.end);
  }
  splitTextNodes(block, edges);

  const units = topUnits(block);
  const doc = block.ownerDocument;
  const refs: SentenceRef[] = [];
  ranges.forEach((range, i) => {
    const inside = units.filter(
      (u) => u.end > u.start && u.start >= range.start && u.end <= range.end,
    );
    if (inside.length === 0) return;
    const sid = `b${blockIndex}-s${i}`;
    const span = doc.createElement("span");
    span.className = SENTENCE_CLASS;
    span.setAttribute("data-sid", sid);
    block.insertBefore(span, inside[0].node);
    for (const u of inside) span.appendChild(u.node);
    refs.push({ id: sid, text: normalize(visibleText(span)) });
  });
  return refs;
}

/** Split top-level text nodes at every range edge so each node lies in one range. */
function splitTextNodes(block: Element, edges: Set<number>): void {
  const sorted = [...edges].sort((a, b) => a - b);
  let off = 0;
  for (const node of Array.from(block.childNodes)) {
    const len = visibleText(node).length;
    if (node.nodeType === TEXT_NODE && len > 0) {
      let cur = node as Text;
      let base = off;
      for (const edge of sorted) {
        if (edge <= off || edge >= off + len) continue;
        cur = cur.splitText(edge - base);
        base = edge;
      }
    }
    off += len;
  }
}
