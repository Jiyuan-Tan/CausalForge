/**
 * Pure model layer for paper-page margin comments.
 *
 * Everything here is DOM-free and side-effect-free: it turns the worker's read
 * payload into placed, grouped, ordered comments, decides which highlight a
 * sentence gets, writes the label strings, and composes the body the browser
 * hands to the worker. The controller (`../comments.ts`) does the rest.
 *
 * The hostile-input boundary lives here too: comment metadata comes from a
 * store any signed-in visitor can write to, so treat every field as hostile.
 * `sanitizeAnchor` caps the fields whose size drives re-anchoring cost, so a
 * comment claiming a 10,000-sentence quote cannot make the page do quadratic
 * work, and every string reaches the DOM through `textContent`.
 */

import {
  prepareSentences,
  reanchor,
  type Anchor,
  type PreparedSentences,
  type SentenceRef,
} from "../../lib/comments/anchor.js";
import { type CommentTag } from "../../lib/comments/schema.js";

/** The three tags a comment may carry; anything else degrades to "none". */
function isCommentTag(t: unknown): t is CommentTag {
  return t === "none" || t === "verified" || t === "problem";
}

/** Anchors wider than this are refused (the composer never makes one). */
export const MAX_ANCHOR_COUNT = 8;
/** Quote length cap — bounds the bigram similarity work per window. A snapped
 *  quote is a handful of sentences; 400 chars covers that with headroom while
 *  keeping a hostile anchor's per-window cost small. */
export const MAX_EXACT_CHARS = 400;
/** Context fields are 32 chars by construction; cap hostile ones anyway. */
export const MAX_CONTEXT_CHARS = 200;
/** Most comments a single page will re-anchor. Beyond this, comments are shown
 *  unanchored (general) instead of running the O(sentences) reanchor each — so
 *  a flood of comments can never turn into an O(comments·sentences) freeze. */
export const MAX_ANCHORED_COMMENTS = 40;
/** Comments placed per event-loop turn during the async pass, so a heavy paper
 *  never blocks paint. */
export const PLACE_BATCH = 10;
/** Client-side cap on what a visitor may post. */
export const MAX_TEXT_CHARS = 10000;
/** Past this the composer shows a live counter. */
export const TEXT_WARN_CHARS = 9000;
/** Cap on rendered length of a fetched comment, to bound the DOM. */
const MAX_RENDER_CHARS = 20000;

const AVATAR_PREFIX = "https://avatars.githubusercontent.com/";

export interface GithubAuthor {
  login: string;
  avatarUrl: string;
}

/**
 * A reply as the worker hands it over. Threads are exactly one level deep — a
 * reply has no replies of its own, and none of the metadata a top-level comment
 * carries (no tag, no anchor: it inherits its parent's).
 */
export interface FetchedReply {
  id: string;
  text: string;
  createdAt: string;
  author: GithubAuthor | null;
}

export interface FetchedComment {
  id: string;
  text: string;
  createdAt: string;
  author: GithubAuthor | null;
  tag?: unknown;
  anchor?: unknown;
  revision?: unknown;
  replies?: FetchedReply[];
}

export interface WorkerPayload {
  comments: FetchedComment[];
  /** The worker served only part of the thread; the rail says so. */
  truncated?: boolean;
}

export interface PlacedReply {
  id: string;
  login: string;
  avatarUrl: string | null;
  createdAt: string;
  text: string;
}

export type PlacedKind = "anchored" | "drifted" | "archived" | "general";

export interface PlacedComment {
  id: string;
  login: string;
  /** Validated avatar URL, or null → initials fallback. */
  avatarUrl: string | null;
  createdAt: string;
  tag: CommentTag;
  text: string;
  kind: PlacedKind;
  /** Sentence ids the comment currently covers (empty unless placed). */
  sids: string[];
  /** The stored quote — shown in narrow mode and in the archive. */
  quote: string;
  revision: string | null;
  /** Index of the first covered sentence; large when unplaced (rail tail). */
  order: number;
  /** Discussion thread under this comment, oldest first. */
  replies: PlacedReply[];
}

/* ── Hostile-input guards ────────────────────────────────────────────────── */

/** Accept an anchor only if re-anchoring it is cheap and bounded. */
export function sanitizeAnchor(a: unknown): Anchor | null {
  if (typeof a !== "object" || a === null) return null;
  const x = a as Record<string, unknown>;
  const exact = typeof x.exact === "string" ? x.exact : "";
  const count = typeof x.count === "number" && Number.isInteger(x.count) ? x.count : 0;
  if (!exact || exact.length > MAX_EXACT_CHARS) return null;
  if (count < 1 || count > MAX_ANCHOR_COUNT) return null;
  return {
    exact,
    prefix: typeof x.prefix === "string" ? x.prefix.slice(0, MAX_CONTEXT_CHARS) : "",
    suffix: typeof x.suffix === "string" ? x.suffix.slice(0, MAX_CONTEXT_CHARS) : "",
    count,
  };
}

/** Avatars are shown only from GitHub's own avatar host. */
export function isSafeAvatarUrl(u: unknown): u is string {
  return typeof u === "string" && u.startsWith(AVATAR_PREFIX) && !/[\s"'<>\\]/.test(u);
}

/* ── Placement ───────────────────────────────────────────────────────────── */

/**
 * Turn one fetched comment into a placed comment.
 *
 * `allowAnchor` is the DoS budget: when it is false the comment is parsed and
 * rendered but NOT re-anchored (the expensive step), so it lands in the general
 * group. Unanchored bodies — including replies written straight on GitHub — are
 * general regardless. Returns whether the anchor budget was actually spent.
 */
function placeOne(
  item: FetchedComment,
  paper: string,
  sentences: SentenceRef[],
  allowAnchor: boolean,
  prepared: PreparedSentences,
): { comment: PlacedComment; usedBudget: boolean; overflow: boolean } {
  const anchor = sanitizeAnchor(item.anchor);
  const comment: PlacedComment = {
    id: item.id,
    login: item.author?.login ?? "ghost",
    avatarUrl: isSafeAvatarUrl(item.author?.avatarUrl) ? item.author!.avatarUrl : null,
    createdAt: typeof item.createdAt === "string" ? item.createdAt : "",
    tag: isCommentTag(item.tag) ? item.tag : "none",
    text: typeof item.text === "string" ? item.text.slice(0, MAX_RENDER_CHARS) : "",
    kind: "general",
    sids: [],
    quote: anchor ? anchor.exact : "",
    revision: typeof item.revision === "string" && item.revision ? item.revision : null,
    order: Number.MAX_SAFE_INTEGER,
    replies: placeReplies(item.replies),
  };
  if (anchor && !allowAnchor) {
    // Over the per-page cap: shown as a general comment, not re-anchored.
    return { comment, usedBudget: false, overflow: true };
  }
  if (anchor) {
    const match = reanchor(anchor, sentences, prepared);
    if (match.state === "archived" || match.start < 0) {
      comment.kind = "archived";
    } else {
      comment.kind = match.state;
      comment.sids = sentences.slice(match.start, match.end).map((s) => s.id);
      comment.order = match.start;
    }
    return { comment, usedBudget: true, overflow: false };
  }
  return { comment, usedBudget: false, overflow: false };
}

export interface Placement {
  placed: PlacedComment[];
  /** How many anchored comments were shown unanchored because of the cap. */
  overflow: number;
}

/**
 * Re-locate every fetched comment against the page's current sentences.
 *
 * Anchored bodies become anchored / drifted / archived per `reanchor`, up to
 * `maxAnchored` of them; any further anchored comment, and every unanchored
 * body, becomes "general". The cap is what keeps a flood of comments from
 * turning into an O(comments · sentences) freeze.
 */
export function placeComments(
  items: FetchedComment[],
  paper: string,
  sentences: SentenceRef[],
  maxAnchored: number = MAX_ANCHORED_COMMENTS,
): PlacedComment[] {
  return placeCommentsBudgeted(items, paper, sentences, maxAnchored).placed;
}

/** As `placeComments`, but also reports how many were pushed over the cap. */
export function placeCommentsBudgeted(
  items: FetchedComment[],
  paper: string,
  sentences: SentenceRef[],
  maxAnchored: number = MAX_ANCHORED_COMMENTS,
): Placement {
  const placed: PlacedComment[] = [];
  const prepared = prepareSentences(sentences);
  let budget = maxAnchored;
  let overflow = 0;
  // Newest first, because that is who the budget should be spent on: the worker
  // serves the newest 100 comments, so iterating in wire order would hand the
  // re-anchor budget to the oldest of them and push the most recent — the ones
  // a returning reader came back for — into the unanchored "general" group.
  for (const item of [...items].reverse()) {
    if (!item || typeof item.id !== "string") continue;
    const r = placeOne(item, paper, sentences, budget > 0, prepared);
    if (r.usedBudget) budget--;
    if (r.overflow) overflow++;
    placed.push(r.comment);
  }
  placed.reverse();
  return { placed, overflow };
}

/**
 * Placement, off the synchronous critical path.
 *
 * Processes comments in small batches and yields to the event loop between
 * them, so even a paper with hundreds of comments never blocks paint. Calls
 * `onBatch` after each batch with everything placed so far, so the rail can
 * render incrementally. The re-anchor cap applies exactly as in the sync path.
 */
export async function placeCommentsAsync(
  items: FetchedComment[],
  paper: string,
  sentences: SentenceRef[],
  onBatch: (soFar: PlacedComment[], done: boolean) => void,
  maxAnchored: number = MAX_ANCHORED_COMMENTS,
  batchSize: number = PLACE_BATCH,
): Promise<Placement> {
  const placed: PlacedComment[] = [];
  const prepared = prepareSentences(sentences);
  let budget = maxAnchored;
  let overflow = 0;
  let sinceYield = 0;
  // Newest first, for the budget reason in `placeCommentsBudgeted`. Callers are
  // handed wire order at every step; the rail re-sorts anyway, but a batch that
  // arrives reversed would still be a surprising thing to expose.
  for (const item of [...items].reverse()) {
    if (!item || typeof item.id !== "string") continue;
    const r = placeOne(item, paper, sentences, budget > 0, prepared);
    if (r.usedBudget) budget--;
    if (r.overflow) overflow++;
    placed.push(r.comment);
    if (++sinceYield >= batchSize) {
      sinceYield = 0;
      onBatch(placed.slice().reverse(), false);
      await new Promise((resolve) => setTimeout(resolve));
    }
  }
  placed.reverse();
  onBatch(placed, true);
  return { placed, overflow };
}

/** Normalize the worker's replies. A reply carries no tag and no anchor: it
 *  inherits its parent's. */
export function placeReplies(items: unknown): PlacedReply[] {
  if (!Array.isArray(items)) return [];
  const out: PlacedReply[] = [];
  for (const item of items as FetchedReply[]) {
    if (!item || typeof item.id !== "string") continue;
    out.push({
      id: item.id,
      login: item.author?.login ?? "ghost",
      avatarUrl: isSafeAvatarUrl(item.author?.avatarUrl) ? item.author!.avatarUrl : null,
      createdAt: typeof item.createdAt === "string" ? item.createdAt : "",
      text: typeof item.text === "string" ? item.text.slice(0, MAX_RENDER_CHARS) : "",
    });
  }
  return out;
}

/** "1 reply" / "3 replies" — the collapsed toggle's label. */
export function replyCountLabel(n: number): string {
  return `${n} ${n === 1 ? "reply" : "replies"}`;
}

/** The pieces the controller reconciles into the rendered comment list. */
export interface LocalState {
  /** The worker's snapshot, replaced wholesale as hydration batches arrive. */
  serverAll: PlacedComment[];
  /** Optimistically-posted top-level comments (survive batch overwrites). */
  localComments: PlacedComment[];
  /** Optimistically-posted replies, by parent comment id. */
  localReplies: Map<string, PlacedReply[]>;
  /** Comment/reply ids deleted this session. */
  deleted: Set<string>;
}

/**
 * Merge the server snapshot with this session's optimistic additions.
 *
 * The point is that a comment or reply posted DURING hydration must not vanish
 * when the next batch overwrites the server snapshot: the local additions are
 * re-merged on top every time, deletions are filtered out (even if a still-
 * arriving batch carries a locally deleted id), and duplicates are collapsed by
 * id (server wins).
 */
export function mergeComments(s: LocalState): PlacedComment[] {
  const byId = new Map<string, PlacedComment>();
  const add = (c: PlacedComment, local: boolean) => {
    if (s.deleted.has(c.id)) return;
    if (local && byId.has(c.id)) return; // server copy already present
    byId.set(c.id, { ...c, replies: c.replies.filter((r) => !s.deleted.has(r.id)) });
  };
  for (const c of s.serverAll) add(c, false);
  for (const c of s.localComments) add(c, true);
  for (const [parentId, replies] of s.localReplies) {
    const parent = byId.get(parentId);
    if (!parent) continue;
    const have = new Set(parent.replies.map((r) => r.id));
    for (const r of replies) {
      if (s.deleted.has(r.id) || have.has(r.id)) continue;
      parent.replies.push(r);
      have.add(r.id);
    }
  }
  return [...byId.values()];
}

export interface CommentGroups {
  /** Anchored + drifted, in document order — the rail's positioned cards. */
  placed: PlacedComment[];
  /** Page-level comments — the rail's "General comments" tail group. */
  general: PlacedComment[];
  /** Quotes that no longer exist — the article-foot archive. */
  archived: PlacedComment[];
}

const byTime = (a: PlacedComment, b: PlacedComment): number =>
  a.createdAt < b.createdAt ? -1 : a.createdAt > b.createdAt ? 1 : 0;

export function groupComments(all: PlacedComment[]): CommentGroups {
  const placed = all
    .filter((c) => c.kind === "anchored" || c.kind === "drifted")
    .sort((a, b) => a.order - b.order || byTime(a, b));
  const general = all.filter((c) => c.kind === "general").sort(byTime);
  const archived = all.filter((c) => c.kind === "archived").sort(byTime);
  return { placed, general, archived };
}

/** Everything still attached to the current text — what the rail head counts. */
export function activeComments(groups: CommentGroups): PlacedComment[] {
  return [...groups.placed, ...groups.general];
}

/** "2 verified · 1 problem · 5 total" (leading groups drop when zero). */
export function countLabel(active: PlacedComment[]): string {
  const verified = active.filter((c) => c.tag === "verified" && c.kind === "anchored").length;
  const problems = active.filter((c) => c.tag === "problem").length;
  const parts: string[] = [];
  if (verified) parts.push(`${verified} verified`);
  if (problems) parts.push(`${problems} problem${problems > 1 ? "s" : ""}`);
  parts.push(`${active.length} total`);
  return parts.join(" · ");
}

export interface Highlight {
  tag: CommentTag;
  drift: boolean;
}

const TAG_RANK: Record<CommentTag, number> = { none: 1, verified: 2, problem: 3 };

/** One highlight per sentence: strongest tag wins, solid beats dashed on ties. */
export function highlightPlan(placed: PlacedComment[]): Map<string, Highlight> {
  const plan = new Map<string, Highlight>();
  for (const c of placed) {
    if (c.kind !== "anchored" && c.kind !== "drifted") continue;
    const drift = c.kind === "drifted";
    for (const sid of c.sids) {
      const cur = plan.get(sid);
      if (!cur || TAG_RANK[c.tag] > TAG_RANK[cur.tag]) {
        plan.set(sid, { tag: c.tag, drift });
      } else if (TAG_RANK[c.tag] === TAG_RANK[cur.tag]) {
        cur.drift = cur.drift && drift;
      }
    }
  }
  return plan;
}

/* ── Label strings ───────────────────────────────────────────────────────── */

export function tagLabel(tag: CommentTag): string | null {
  return tag === "verified" ? "✅ Verified" : tag === "problem" ? "⚠️ Problem" : null;
}

export function tagExplainer(tag: CommentTag): string {
  if (tag === "verified") {
    return "Pins to the exact words selected — will visibly demote if this passage is later edited.";
  }
  if (tag === "problem") {
    return "Flags an issue with this passage; archives with a “possibly addressed” note if the passage is rewritten.";
  }
  return "";
}

/** The note a drifted card carries. ✅ Verified demotes loudly; others mildly. */
export function driftNote(tag: CommentTag): { text: string; strong: boolean } {
  if (tag === "verified") {
    return {
      text: "⚠ Verified before a wording change — the passage has since been edited and may need re-checking.",
      strong: true,
    };
  }
  return { text: "The text here has changed slightly since this comment.", strong: false };
}

export function archivedNote(tag: CommentTag): string {
  if (tag === "problem") {
    return "The passage this flagged has since been rewritten — possibly addressed.";
  }
  if (tag === "verified") {
    return "This verification applies to the earlier version quoted above, not to the current text.";
  }
  return "The passage this commented on has since been rewritten.";
}

export function snapNote(count: number): string {
  return `(snapped to ${count} sentence${count > 1 ? "s" : ""})`;
}

export function truncate(s: string, n: number): string {
  return s.length > n ? `${s.slice(0, n - 1)}…` : s;
}

/** Two-letter avatar fallback, e.g. "j-metrics" → "JM". */
export function initialsOf(login: string): string {
  const parts = login.split(/[^A-Za-z0-9]+/).filter(Boolean);
  const letters = parts.length > 1 ? parts[0][0] + parts[1][0] : (parts[0] ?? "?").slice(0, 2);
  return letters.toUpperCase();
}

/** ISO timestamp → "2026-08-21"; "" when unparseable. */
export function formatWhen(iso: string): string {
  const t = Date.parse(iso);
  if (Number.isNaN(t)) return "";
  return new Date(t).toISOString().slice(0, 10);
}

/* ── Outgoing wire format ────────────────────────────────────────────────── */

/**
 * The payload for a new comment.
 *
 * Structured fields, not a serialized document: the worker stores them as they
 * are and re-validates every one, so nothing here is a security boundary — it
 * is the composer's own bounds, applied before a pointless round trip. The
 * author is deliberately absent; the worker resolves that from the token and
 * would overwrite anything sent.
 */
export function newCommentPayload(args: {
  paper: string;
  tag: CommentTag;
  text: string;
  anchor?: Anchor | null;
  revision?: string | null;
}): Record<string, unknown> {
  const payload: Record<string, unknown> = {
    paper: args.paper,
    tag: args.tag,
    text: args.text.slice(0, MAX_TEXT_CHARS),
  };
  if (args.anchor) payload.anchor = args.anchor;
  if (args.revision) payload.revision = args.revision;
  return payload;
}

/** A reply carries only its text and its parent; it inherits tag and anchor. */
export function newReplyPayload(paper: string, parentId: string, text: string) {
  return { paper, parentId, text: text.trim().slice(0, MAX_TEXT_CHARS) };
}


/**
 * Whether to OFFER the delete control on a comment.
 *
 * Convenience only, and deliberately so: the real authorization happens in the
 * worker, which re-reads the comment's stamped author and refuses anyone else.
 * Hiding the button spares readers a control that would fail; it is not what
 * stops anyone deleting someone else's comment. No viewer loaded → no button
 * (we cannot know whose it is).
 */
export function ownsComment(c: { login: string }, viewer: { login?: string } | null): boolean {
  const login = viewer?.login;
  if (typeof login !== "string" || login.length === 0) return false;
  return c.login.toLowerCase() === login.toLowerCase();
}
