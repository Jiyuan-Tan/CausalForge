// Deterministic segmentation of a paper block's inner HTML.
//
// The v2 design let the model quote spans and then checked them character by
// character. That put the model in charge of where a highlight starts and ends,
// so most of the machinery existed to catch it choosing badly: spans that cut a
// tag in half, spans that overlapped each other, spans that were paraphrased
// rather than copied. Here the spans are computed FIRST and the model only
// chooses among them by id — the whole class of defect disappears rather than
// being policed.
//
// Two invariants hold by construction, and are what make that safe:
//   * PARTITION — every byte of the block belongs to exactly one segment, in
//     order, with no gaps and no overlap.
//   * ATOMICITY — no boundary falls inside a tag or inside a math element. A
//     display formula is one whole segment; the text between displays is split
//     only at sentence ends outside inline math.
//   * WELL-NESTED FRAGMENTS — a segment may begin inside an open element (it
//     must: pandoc wraps every sentence and display in `<p>`, so requiring each
//     segment to balance on its own leaves ONE segment per block and no
//     addressable display — measured, not guessed). What is guaranteed instead
//     is the property that actually makes wrapping safe: each segment carries
//     the `openPath` of elements open at its start, it never closes an element
//     it did not have open, and applying its tags to its own path yields the
//     next segment's path. A consumer wraps the text nodes inside the range —
//     which is what a DOM wrap does anyway — and can never emit interleaved
//     tags. `segmentationProblems` checks all of it.

/** A stretch of the block the site can highlight as a unit. */
export interface NlSegment {
  id: string;
  kind: "text" | "display";
  /** Byte offsets into the block's inner HTML: [start, end). */
  start: number;
  end: number;
  /** Tag names of the elements open at `start`, outermost first. Empty when the
   *  segment begins at the block's top level. A consumer that wraps text nodes
   *  inside the range needs nothing else; one that splices strings must reopen
   *  this path. */
  openPath: string[];
}

const DISPLAY_OPEN = '<span class="math display">';

/** Elements with no closing tag — they never change the open-element depth. */
const VOID_ELEMENTS: ReadonlySet<string> = new Set([
  "area", "base", "br", "col", "embed", "hr", "img", "input",
  "link", "meta", "param", "source", "track", "wbr",
]);

/**
 * Open-element depth at every offset: `depth[i]` counts elements opened before
 * `i` and not yet closed. Comments, doctypes, void and self-closing elements do
 * not nest. The depth an offset carries is the depth AFTER any tag ending at or
 * before it, so two offsets with equal depth delimit balanced markup.
 */
export function openStacks(html: string): string[][] {
  const stacks: string[][] = new Array(html.length + 1);
  const stack: string[] = [];
  let at = 0;
  const fill = (from: number, to: number) => {
    const snapshot = [...stack];
    for (let i = from; i <= to && i < stacks.length; i++) stacks[i] = snapshot;
  };
  for (const m of html.matchAll(/<!--[\s\S]*?-->|<[^>]*>/g)) {
    fill(at, m.index);
    const tag = m[0];
    if (!tag.startsWith("<!")) {
      const name = /^<\/?\s*([a-zA-Z][^\s/>]*)/.exec(tag)?.[1]?.toLowerCase();
      if (name && !VOID_ELEMENTS.has(name) && !tag.endsWith("/>")) {
        if (tag.startsWith("</")) {
          const at_ = stack.lastIndexOf(name);
          if (at_ >= 0) stack.length = at_;
        } else stack.push(name);
      }
    }
    at = m.index + tag.length;
    fill(m.index + 1, at - 1); // tag interior: unsplittable anyway
  }
  fill(at, html.length);
  return stacks;
}

/** Open-element depth at every offset. */
export function openDepths(html: string): number[] {
  return openStacks(html).map((s) => s.length);
}

/** Ranges of the block's display-math elements, depth-aware so a display whose
 *  payload contains nested spans is taken whole. */
export function displayRanges(html: string): Array<[number, number]> {
  const out: Array<[number, number]> = [];
  const open = new RegExp(DISPLAY_OPEN.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"), "g");
  for (let m = open.exec(html); m !== null; m = open.exec(html)) {
    const tagRe = /<span\b[^>]*>|<\/span\s*>/g;
    tagRe.lastIndex = m.index + m[0].length;
    let depth = 1;
    let closed = -1;
    for (let t = tagRe.exec(html); t !== null; t = tagRe.exec(html)) {
      depth += t[0].startsWith("</") ? -1 : 1;
      if (depth === 0) {
        closed = t.index + t[0].length;
        break;
      }
    }
    if (closed < 0) break; // unbalanced markup: stop rather than invent a range
    out.push([m.index, closed]);
    open.lastIndex = closed;
  }
  return out;
}

/**
 * Offsets inside `html` that are safe to cut at: outside every tag, and outside
 * every inline-math element (splitting `\(a<b\)` mid-formula would hand the site
 * half a KaTeX node). Returns a predicate over offsets.
 */
function safeCutter(html: string): (at: number) => boolean {
  const unsafe = new Uint8Array(html.length + 1);
  const mark = (from: number, to: number) => {
    for (let i = from + 1; i < to && i < unsafe.length; i++) unsafe[i] = 1;
  };
  // tags
  for (const m of html.matchAll(/<[^>]*>/g)) mark(m.index, m.index + m[0].length);
  // display interiors are never cut either — a display is atomic
  for (const [start, end] of displayRanges(html)) mark(start, end);
  // inline math elements, depth-aware like the displays
  const open = /<span class="math inline">/g;
  for (let m = open.exec(html); m !== null; m = open.exec(html)) {
    const tagRe = /<span\b[^>]*>|<\/span\s*>/g;
    tagRe.lastIndex = m.index + m[0].length;
    let depth = 1;
    for (let t = tagRe.exec(html); t !== null; t = tagRe.exec(html)) {
      depth += t[0].startsWith("</") ? -1 : 1;
      if (depth === 0) {
        mark(m.index, t.index + t[0].length);
        open.lastIndex = t.index + t[0].length;
        break;
      }
    }
  }
  return (at: number) => at === 0 || at === html.length || unsafe[at] === 0;
}

/** Sentence-ending offsets: after `.`, `?` or `!` followed by whitespace, and
 *  after a closing `</p>`. Only offsets the cutter allows survive. */
function sentenceBreaks(html: string, from: number, to: number, safe: (at: number) => boolean): number[] {
  const out: number[] = [];
  for (let i = from; i < to - 1; i++) {
    const c = html[i];
    let at = -1;
    if ((c === "." || c === "?" || c === "!") && /[\s<]/.test(html[i + 1] ?? "")) at = i + 1;
    else if (html.startsWith("</p>", i)) at = i + 4;
    if (at > from && at < to && safe(at)) out.push(at);
  }
  return [...new Set(out)];
}

/**
 * Split a block's inner HTML into display-math segments (whole) and the text
 * runs between them, each further split at sentence boundaries. Ids are `s1`,
 * `s2`, … in document order, so they are stable for identical input.
 */
export function segmentBlock(html: string): NlSegment[] {
  const displays = displayRanges(html);
  const safe = safeCutter(html);
  const stacks = openStacks(html);
  const segments: NlSegment[] = [];
  let n = 0;
  const push = (kind: NlSegment["kind"], start: number, end: number) => {
    if (end <= start) return;
    segments.push({ id: `s${++n}`, kind, start, end, openPath: stacks[start] ?? [] });
  };
  const pushText = (start: number, end: number) => {
    let at = start;
    for (const brk of sentenceBreaks(html, start, end, safe)) {
      if (brk <= at) continue;
      push("text", at, brk);
      at = brk;
    }
    push("text", at, end);
  };
  let cursor = 0;
  for (const [start, end] of displays) {
    pushText(cursor, start);
    push("display", start, end);
    cursor = end;
  }
  pushText(cursor, html.length);
  return segments;
}

/** The text of a segment, as the prompt shows it. */
export const segmentText = (html: string, seg: NlSegment): string => html.slice(seg.start, seg.end);

/**
 * Partition AND well-nesting check: the segments tile the block exactly, each
 * one's recorded `openPath` is the real element path at its start, none closes
 * an element it did not have open, and the block ends with nothing left open.
 * Exported so the invariants are asserted at run time and in the sweep, not
 * merely intended.
 */
export function segmentationProblems(html: string, segments: NlSegment[]): string[] {
  const problems: string[] = [];
  const stacks = openStacks(html);
  const ids = new Set<string>();
  let at = 0;
  for (const s of segments) {
    if (ids.has(s.id)) problems.push(`duplicate segment id ${s.id}`);
    ids.add(s.id);
    if (s.start !== at) problems.push(`segment ${s.id} starts at ${s.start}, expected ${at}`);
    if (s.end <= s.start) problems.push(`segment ${s.id} is empty`);
    const actual = stacks[s.start] ?? [];
    if (s.openPath.join(">") !== actual.join(">")) {
      problems.push(
        `segment ${s.id} records openPath [${s.openPath.join(">")}], actual [${actual.join(">")}]`,
      );
    }
    // Never closes more than it opened, relative to its own path: the property
    // that makes a DOM wrap of this range safe.
    const closes = [...html.slice(s.start, s.end).matchAll(/<\/\s*([a-zA-Z][^\s/>]*)/g)]
      .map((m) => m[1].toLowerCase())
      .filter((nm) => !VOID_ELEMENTS.has(nm));
    let available = actual.length;
    let opened = 0;
    for (const m of html.slice(s.start, s.end).matchAll(/<\/?\s*([a-zA-Z][^\s/>]*)[^>]*>/g)) {
      const nm = m[1].toLowerCase();
      if (VOID_ELEMENTS.has(nm) || m[0].endsWith("/>")) continue;
      if (m[0].startsWith("</")) {
        if (opened > 0) opened--;
        else if (available > 0) available--;
        else problems.push(`segment ${s.id} closes </${nm}> it never had open`);
      } else opened++;
    }
    void closes;
    at = s.end;
  }
  if (segments.length > 0 && at !== html.length) {
    problems.push(`segments end at ${at}, block is ${html.length} bytes`);
  }
  const tail = stacks[html.length] ?? [];
  if (tail.length > 0) problems.push(`block leaves [${tail.join(">")}] open`);
  return problems;
}
