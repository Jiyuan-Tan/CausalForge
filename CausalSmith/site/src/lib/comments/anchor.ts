/**
 * Content-anchoring engine for paper-page margin comments.
 *
 * Comments anchor to SENTENCES of the rendered paper, not to character offsets
 * or revisions: an anchor stores the quoted sentence text plus a little
 * context, and each page load (or rebuild) re-locates the quote in the current
 * text. Unchanged text re-anchors exactly; small rewordings re-anchor fuzzily
 * as "drifted"; passages rewritten beyond recognition become "archived".
 *
 * Everything here is pure and DOM-free: the DOM layer segments rendered blocks
 * into an ordered sentence list (via `segmentSentences`) and hands it in.
 */

export interface SentenceRef {
  /** Stable-ish id assigned by the page (block id + index). Display only —
   * re-anchoring never trusts ids, only text. */
  id: string;
  text: string;
}

export interface Anchor {
  /** The quoted sentence(s), whitespace-normalized, in document order. */
  exact: string;
  /** Tail of the sentence before the quote (normalized, ≤ PREFIX_LEN chars). */
  prefix: string;
  /** Head of the sentence after the quote (normalized, ≤ PREFIX_LEN chars). */
  suffix: string;
  /** How many sentences the quote spanned when created. */
  count: number;
}

export type AnchorState = "anchored" | "drifted" | "archived";

export interface AnchorMatch {
  state: AnchorState;
  /** Start index into the sentence list (inclusive); -1 when archived. */
  start: number;
  /** End index (exclusive); -1 when archived. */
  end: number;
  /** Similarity of the matched window to the stored quote, in [0, 1]. */
  score: number;
}

const PREFIX_LEN = 32;
/** ≥ this (after normalization) counts as unchanged. */
const EXACT_THRESHOLD = 0.985;
/** ≥ this counts as a small rewording (drifted); below is archived. */
const DRIFT_THRESHOLD = 0.55;

/** Collapse whitespace; matching is case-insensitive but quotes keep case. */
export function normalize(s: string): string {
  return s.replace(/\s+/g, " ").trim();
}

function matchKey(s: string): string {
  return normalize(s).toLowerCase();
}

/** Character-bigram multiset of a match-key. */
function grams(s: string): Map<string, number> {
  const m = new Map<string, number>();
  for (let i = 0; i < s.length - 1; i++) {
    const g = s.slice(i, i + 2);
    m.set(g, (m.get(g) ?? 0) + 1);
  }
  return m;
}

function gramTotal(m: Map<string, number>): number {
  let n = 0;
  for (const c of m.values()) n += c;
  return n;
}

/**
 * A reusable query side for the Dice coefficient.
 *
 * `reanchor` scores one stored quote against many candidate windows, so its
 * gram multiset is built ONCE here and reused, rather than rebuilt per window
 * (the single biggest cost in placing a page full of comments).
 */
export interface GramQuery {
  key: string;
  grams: Map<string, number>;
  size: number;
}

export function gramQuery(a: string): GramQuery {
  const key = matchKey(a);
  const g = grams(key);
  return { key, grams: g, size: gramTotal(g) };
}

/** Dice coefficient of a prebuilt query against an already-normalized key. */
function similarityToKey(q: GramQuery, kb: string): number {
  if (!q.key || !kb) return 0;
  if (q.key === kb) return 1;
  const B = grams(kb);
  let inter = 0;
  for (const [g, c] of B) {
    const ca = q.grams.get(g);
    if (ca !== undefined) inter += Math.min(c, ca);
  }
  const sizeB = gramTotal(B);
  return q.size + sizeB === 0 ? 0 : (2 * inter) / (q.size + sizeB);
}

/** Dice coefficient of a prebuilt query against a fresh candidate string. */
export function similarityTo(q: GramQuery, b: string): number {
  return similarityToKey(q, matchKey(b));
}

/** Character-bigram Dice coefficient — cheap, order-insensitive enough for
 * "was this sentence reworded or replaced?". */
export function similarity(a: string, b: string): number {
  return similarityTo(gramQuery(a), b);
}

/** Abbreviations whose trailing period must not end a sentence. Lowercased,
 * period-free. Covers the forms that actually appear in the papers. */
const ABBREVIATIONS = new Set([
  "i.i.d", "e.g", "i.e", "cf", "resp", "vs", "et al", "eq", "eqs",
  "sec", "thm", "prop", "lem", "cor", "def", "fig", "no", "vol", "pp",
]);

function endsWithAbbreviation(chunk: string): boolean {
  const m = chunk.match(/([A-Za-z][A-Za-z.]*)\.$/);
  if (!m) return false;
  const word = m[1].replace(/\.$/, "").toLowerCase();
  if (ABBREVIATIONS.has(word)) return true;
  // Single capital letter — an initial ("W. K. Newey") or a math symbol.
  if (/^[A-Z]$/.test(m[1])) return true;
  return false;
}

/**
 * Split a block's plain text into sentences. Heuristic, tuned for math-heavy
 * scholarly prose: breaks after . ! ? ∎ followed by whitespace and an
 * uppercase/digit/math opener, with an abbreviation guard. A block that never
 * matches stays one sentence — display equations and headings should be passed
 * as their own blocks and come back whole.
 */
export function segmentSentences(text: string): string[] {
  const t = normalize(text);
  if (!t) return [];
  const out: string[] = [];
  let start = 0;
  const re = /[.!?∎](?=\s)/g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(t)) !== null) {
    const end = m.index + 1;
    // Only the tail can carry the abbreviation whose period we're testing; a
    // fixed-width slice keeps this O(n) rather than regrowing the whole prefix.
    const tailStart = Math.max(start, end - 40);
    if (m[0] === "." && endsWithAbbreviation(t.slice(tailStart, end))) continue;
    // Only the first non-space char after the break matters, so a bounded slice
    // keeps this O(n) instead of copying the whole remaining string each match.
    const rest = t.slice(end, end + 8).trimStart();
    // A following tombstone belongs to THIS sentence — break after it instead.
    if (rest.startsWith("∎")) continue;
    // Don't break before a lowercase continuation ("... rate. of" is a typo,
    // but "...) . Then" style splits need an opener on the right).
    if (rest && !/^[A-Z0-9("'‘“∀-⋿\u{1D400}-\u{1D7FF}]/u.test(rest)) continue;
    out.push(t.slice(start, end).trim());
    start = end;
  }
  const tail = t.slice(start).trim();
  if (tail) out.push(tail);
  return out;
}

/** Build the anchor for a selection that snapped to sentences [start, end). */
export function makeAnchor(sentences: SentenceRef[], start: number, end: number): Anchor {
  if (start < 0 || end > sentences.length || start >= end) {
    throw new Error(`makeAnchor: bad range [${start}, ${end}) over ${sentences.length} sentences`);
  }
  const exact = normalize(sentences.slice(start, end).map((s) => s.text).join(" "));
  const before = start > 0 ? normalize(sentences[start - 1].text) : "";
  const after = end < sentences.length ? normalize(sentences[end].text) : "";
  return {
    exact,
    prefix: before.slice(-PREFIX_LEN),
    suffix: after.slice(0, PREFIX_LEN),
    count: end - start,
  };
}

function contextScore(anchor: Anchor, sentences: SentenceRef[], start: number, end: number): number {
  let score = 0;
  if (anchor.prefix) {
    const before = start > 0 ? normalize(sentences[start - 1].text) : "";
    score += similarity(anchor.prefix, before.slice(-PREFIX_LEN));
  }
  if (anchor.suffix) {
    const after = end < sentences.length ? normalize(sentences[end].text) : "";
    score += similarity(anchor.suffix, after.slice(0, PREFIX_LEN));
  }
  return score;
}

/**
 * Sentences, normalized ONCE for re-anchoring.
 *
 * A page re-anchors many stored quotes against the SAME sentence list, so the
 * per-sentence match-keys and a prefix sum of their lengths are computed a
 * single time here and shared. Without this every `reanchor` call re-normalized
 * every sentence — the dominant cost when a page carries many comments.
 */
export interface PreparedSentences {
  sentences: SentenceRef[];
  /** matchKey(sentence.text) for each sentence. */
  keys: string[];
  /** Prefix sum of key lengths, so a window's key length is O(1) to estimate. */
  cumLen: number[];
}

export function prepareSentences(sentences: SentenceRef[]): PreparedSentences {
  const keys = sentences.map((s) => matchKey(s.text));
  const cumLen = new Array<number>(keys.length + 1);
  cumLen[0] = 0;
  for (let i = 0; i < keys.length; i++) cumLen[i + 1] = cumLen[i] + keys[i].length;
  return { sentences, keys, cumLen };
}

/**
 * Re-locate an anchor in the current sentence list.
 *
 * Exact pass first (normalized equality on a window of the stored width;
 * context disambiguates repeated sentences), then a fuzzy pass over windows of
 * width count−1 … count+1. Best score ≥ DRIFT_THRESHOLD → drifted;
 * ≥ EXACT_THRESHOLD → anchored; below → archived.
 *
 * Pass `prepared` (from `prepareSentences`) when re-anchoring many quotes
 * against one page — it shares the per-sentence normalization across calls.
 */
export function reanchor(
  anchor: Anchor,
  sentences: SentenceRef[],
  prepared?: PreparedSentences,
): AnchorMatch {
  const prep = prepared && prepared.sentences === sentences ? prepared : prepareSentences(sentences);
  const { keys, cumLen } = prep;
  const n = sentences.length;
  if (n === 0) return { state: "archived", start: -1, end: -1, score: 0 };

  // Window key from the precomputed sentence keys — a single space between
  // sentences matches what matchKey(joined text) would produce.
  const windowKey = (s: number, e: number) => keys.slice(s, e).join(" ");
  // O(1) window key length: member key lengths plus the joining spaces.
  const windowKeyLen = (s: number, e: number) => cumLen[e] - cumLen[s] + (e - s - 1);

  const anchorKey = matchKey(anchor.exact);
  const anchorLen = anchorKey.length;

  // Exact pass.
  const exactHits: Array<{ start: number; end: number }> = [];
  const w = Math.min(anchor.count, n);
  for (let s = 0; s + w <= n; s++) {
    // Cheap length pre-check before building the window key at all.
    if (windowKeyLen(s, s + w) !== anchorLen) continue;
    if (windowKey(s, s + w) === anchorKey) exactHits.push({ start: s, end: s + w });
  }
  if (exactHits.length > 0) {
    let best = exactHits[0];
    if (exactHits.length > 1) {
      let bestCtx = -1;
      for (const h of exactHits) {
        const c = contextScore(anchor, sentences, h.start, h.end);
        if (c > bestCtx) {
          bestCtx = c;
          best = h;
        }
      }
    }
    return { state: "anchored", start: best.start, end: best.end, score: 1 };
  }

  // Truncated-quote pass. The wire clips a stored `exact` to a length cap
  // (historically 400 chars — a five-sentence quote spanning display equations
  // was cut MID-FORMULA), so the stored key is a strict PREFIX of the true
  // window's key and full equality can never fire: the comment reads as
  // "drifted" on the very text it was written against. Prefix equality on a
  // long key identifies the window as unambiguously as full equality; the
  // length floor keeps a short quote from prefix-matching spuriously.
  const TRUNCATED_MIN_KEY = 200;
  if (anchorLen >= TRUNCATED_MIN_KEY) {
    const prefixHits: Array<{ start: number; end: number }> = [];
    for (let s = 0; s + w <= n; s++) {
      if (windowKeyLen(s, s + w) <= anchorLen) continue; // equal was the exact pass
      if (windowKey(s, s + w).startsWith(anchorKey)) prefixHits.push({ start: s, end: s + w });
    }
    if (prefixHits.length > 0) {
      let best = prefixHits[0];
      if (prefixHits.length > 1) {
        let bestCtx = -1;
        for (const h of prefixHits) {
          const c = contextScore(anchor, sentences, h.start, h.end);
          if (c > bestCtx) {
            bestCtx = c;
            best = h;
          }
        }
      }
      return { state: "anchored", start: best.start, end: best.end, score: 1 };
    }
  }

  // Fuzzy pass. Build the query grams once, and skip any window whose length is
  // too far from the quote's to possibly clear DRIFT_THRESHOLD — a Dice
  // coefficient above 0.5 forces the lengths within ~[0.5, 2]× of each other.
  // The length gate uses the O(1) prefix sum, so most windows are skipped
  // without ever building their key.
  const query: GramQuery = { key: anchorKey, grams: grams(anchorKey), size: 0 };
  query.size = gramTotal(query.grams);
  const loLen = anchorLen * 0.5;
  const hiLen = anchorLen * 2;
  let best: AnchorMatch = { state: "archived", start: -1, end: -1, score: 0 };
  let bestCtx = -1;
  const widths = new Set([anchor.count, Math.max(1, anchor.count - 1), anchor.count + 1]);
  for (const width of widths) {
    for (let s = 0; s + width <= n; s++) {
      const len = windowKeyLen(s, s + width);
      if (len < loLen || len > hiLen) continue;
      const score = similarityToKey(query, windowKey(s, s + width));
      if (score < DRIFT_THRESHOLD) continue;
      const ctx = contextScore(anchor, sentences, s, s + width);
      if (score > best.score || (score === best.score && ctx > bestCtx)) {
        best = {
          state: score >= EXACT_THRESHOLD ? "anchored" : "drifted",
          start: s,
          end: s + width,
          score,
        };
        bestCtx = ctx;
      }
    }
  }
  return best;
}
