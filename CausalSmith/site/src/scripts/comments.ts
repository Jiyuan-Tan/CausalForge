/**
 * Paper-page margin comments — the controller.
 *
 * Boots only when the page carries a `commentsWorker` URL (the
 * `PUBLIC_COMMENTS_WORKER` build flag): with the flag unset the paper page is
 * byte-for-byte the page it was before, and this module makes no request and
 * touches no DOM.
 *
 * With the flag on it: segments the rendered body into sentences, reads the
 * paper's comment thread through the worker, re-anchors each stored quote
 * against the CURRENT text, renders the rail / archive / highlights, and runs
 * the select → compose → post flow. Reads AND writes both go through the
 * worker, which owns the storage. The visitor's token — held in sessionStorage
 * and nowhere else — is deliberately powerless: an identity document the worker
 * checks with GitHub, never a credential that could write anything anywhere.
 *
 * Failure is always silent-and-degraded, never fatal: a dead worker leaves
 * "comments unavailable" in the rail head and a fully readable paper.
 */

import { makeAnchor, type SentenceRef } from "../lib/comments/anchor.js";
import type { CommentTag } from "../lib/comments/schema.js";
import {
  SENTENCE_CLASS,
  collectSidElements,
  segmentPaperBody,
  type SidMap,
} from "./commentsDom.js";
import * as auth from "./comments/auth.js";
import * as model from "./comments/model.js";
import * as view from "./comments/render.js";

interface Config {
  worker: string;
  paperId: string;
  revision: string;
}

interface Pending {
  start: number;
  end: number;
  sids: string[];
  quote: string;
}

interface State {
  cfg: Config;
  ui: view.CommentsUi;
  bodyRoot: HTMLElement;
  host: HTMLElement;
  /** Filled lazily by `ensureSegmented` — segmentation is deferred off the
   *  first-paint path, so these are empty until the paper is actually needed
   *  for placing comments or resolving a selection. */
  segmented: boolean;
  sentences: SentenceRef[];
  index: Map<string, number>;
  /** sid → span, built once with `collectSidElements`; the highlight/hover/
   *  layout paths read this instead of re-scanning the DOM per comment. */
  sidEls: SidMap;
  /** Sentences currently carrying a highlight class, so a repaint clears only
   *  those rather than scanning the whole document. */
  litSids: Set<string>;
  /** What the worker last gave us — replaced wholesale as hydration batches
   *  arrive. `all` is derived from this plus the optimistic local additions. */
  serverAll: model.PlacedComment[];
  /** Optimistically-posted top-level comments, kept across batch overwrites so a
   *  comment posted mid-hydration does not vanish when the next batch lands. */
  localComments: model.PlacedComment[];
  /** Optimistically-posted replies, by parent comment id, kept the same way. */
  localReplies: Map<string, model.PlacedReply[]>;
  /** Comment/reply ids deleted this session — filtered out of the merged view
   *  even if a still-arriving server batch still carries them. */
  deleted: Set<string>;
  /** The merged view (serverAll + local additions − deleted) that the rail
   *  renders. Never assigned directly; always via `rebuildAll`. */
  all: model.PlacedComment[];
  token: string | null;
  viewer: auth.Viewer | null;
  pending: Pending | null;
  tag: CommentTag;
  loadFailed: boolean;
  /** The worker served only part of the thread (per-author or per-thread cap).
   *  Surfaced in the rail head: a silently shortened thread is indistinguishable
   *  from a thread nobody wrote in. */
  truncated: boolean;
  /** Anchored comments shown unanchored because of the per-page cap. */
  overflow: number;
  /** Transient rail-head message (delete failure, expired session). */
  notice: string | null;
  /** Comment ids whose reply thread is open, kept across rail rebuilds. */
  expanded: Set<string>;
}

class AuthExpired extends Error {}

/* ── Boot ────────────────────────────────────────────────────────────────── */

/** Entry point; safe to call unconditionally. */
export function initComments(): void {
  try {
    boot();
  } catch {
    /* the paper must render even if commenting cannot */
  }
}

function readConfig(): Config | null {
  const el = document.getElementById("paper-data");
  if (!el) return null;
  let data: Record<string, unknown>;
  try {
    data = JSON.parse(el.textContent ?? "") as Record<string, unknown>;
  } catch {
    return null;
  }
  const rawWorker = typeof data.commentsWorker === "string" ? data.commentsWorker.trim() : "";
  const paperId = typeof data.paperId === "string" ? data.paperId : "";
  if (!rawWorker || !/^[A-Za-z0-9_.-]{1,128}$/.test(paperId)) return null;
  let url: URL;
  try {
    url = new URL(rawWorker);
  } catch {
    return null;
  }
  const localhost = url.hostname === "localhost" || url.hostname === "127.0.0.1";
  if (url.protocol !== "https:" && !localhost) return null;
  return {
    worker: rawWorker.replace(/\/+$/, ""),
    paperId,
    revision: typeof data.revision === "string" ? data.revision : "",
  };
}

function boot(): void {
  const cfg = readConfig();
  if (!cfg) return;
  const bodyRoot = document.getElementById("paper-body");
  const host = document.querySelector<HTMLElement>("article.paper");
  const ui = view.queryUi();
  if (!bodyRoot || !host || !ui) return;

  // NOTHING heavy here: segmentation (seconds on a big paper) is deferred so it
  // never blocks first paint. The shell is shown, events are wired, and the
  // actual hydration is scheduled for after the browser has painted.
  const state: State = {
    cfg,
    ui,
    bodyRoot,
    host,
    segmented: false,
    sentences: [],
    index: new Map(),
    sidEls: new Map(),
    litSids: new Set(),
    serverAll: [],
    localComments: [],
    localReplies: new Map(),
    deleted: new Set(),
    all: [],
    token: auth.readToken(),
    viewer: null,
    pending: null,
    tag: "none",
    loadFailed: false,
    truncated: false,
    overflow: 0,
    notice: null,
    expanded: new Set<string>(),
  };

  ui.root.hidden = false;
  wire(state);
  refresh(state);
  // Hydrate after the first frame so the paper is interactive immediately.
  afterPaint(() => {
    void hydrate(state);
  });
}

/** Run once the browser has painted at least one frame. */
function afterPaint(fn: () => void): void {
  if (typeof requestAnimationFrame === "function") {
    requestAnimationFrame(() => setTimeout(fn, 0));
  } else {
    setTimeout(fn, 0);
  }
}

/** Run when the browser is idle (falls back to a short timeout). */
function onIdle(fn: () => void): void {
  const ric = (globalThis as { requestIdleCallback?: (cb: () => void) => number })
    .requestIdleCallback;
  if (typeof ric === "function") ric(() => fn());
  else setTimeout(fn, 200);
}

async function hydrate(state: State): Promise<void> {
  await load(state);
  if (state.token) void loadViewer(state);
  // Even a paper with no comments gets segmented eventually, in idle time, so
  // the reader's first text selection is instant rather than paying for it then.
  if (!state.segmented) onIdle(() => ensureSegmented(state));
}

/**
 * Segment the paper into sentences, once.
 *
 * Idempotent and cached: the sid → span map and the sentence index are built
 * here and never rebuilt. Segmentation is the expensive DOM pass, so it runs at
 * most once per page and only when something actually needs it.
 */
function ensureSegmented(state: State): void {
  if (state.segmented) return;
  state.segmented = true;
  try {
    state.sentences = segmentPaperBody(state.bodyRoot);
  } catch {
    state.sentences = [];
  }
  state.index = new Map(state.sentences.map((s, i) => [s.id, i]));
  state.sidEls = collectSidElements(state.bodyRoot);
}

/* ── Data ────────────────────────────────────────────────────────────────── */

async function load(state: State): Promise<void> {
  const { cfg } = state;
  try {
    const res = await fetch(
      `${cfg.worker}/api/comments?paper=${encodeURIComponent(cfg.paperId)}`,
      { credentials: "omit" },
    );
    if (!res.ok) throw new Error(`worker ${res.status}`);
    const data = (await res.json()) as Partial<model.WorkerPayload>;
    state.truncated = data.truncated === true;
    const items = Array.isArray(data.comments) ? data.comments : [];
    state.loadFailed = false;
    if (items.length === 0) {
      // The common case (a paper with no comments) never segments at load — the
      // one biggest cost — so there is nothing to place and nothing to draw.
      // Any comment posted before this point is preserved via the local merge.
      state.serverAll = [];
      rebuildAll(state);
      refresh(state);
      return;
    }
    // There are comments to anchor, so segmentation is finally needed. It runs
    // here, already off the first-paint path (this is post-paint, post-fetch).
    ensureSegmented(state);
    // Placement runs in batches yielded to the event loop, rendering
    // incrementally, so a paper with hundreds of comments never blocks paint.
    // The re-anchor cap inside placeCommentsAsync bounds the total work.
    const { overflow } = await model.placeCommentsAsync(
      items,
      cfg.paperId,
      state.sentences,
      (soFar, done) => {
        // The batch is the fresh server truth; local optimistic posts are merged
        // back on top so a comment posted mid-hydration is never overwritten.
        state.serverAll = done ? soFar : soFar.slice();
        rebuildAll(state);
        refresh(state);
      },
    );
    state.overflow = overflow;
  } catch {
    state.loadFailed = true;
  }
  refresh(state);
}

/**
 * Send a write to the worker.
 *
 * The visitor's token goes no further than this: it is an identity document the
 * worker checks with GitHub, not a repository credential — the comment is stored
 * by the worker under the account it resolved from that token. That is why
 * signing in asks for nothing but "verify your GitHub identity".
 */
async function workerWrite(
  state: State,
  method: "POST" | "DELETE",
  payload: Record<string, unknown>,
): Promise<Record<string, any>> {
  const token = state.token;
  if (!token) throw new AuthExpired("not signed in");
  const res = await fetch(`${state.cfg.worker}/api/comments`, {
    method,
    credentials: "omit",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
    body: JSON.stringify({ paper: state.cfg.paperId, ...payload }),
  });
  if (res.status === 401) {
    signOut(state);
    throw new AuthExpired("session expired");
  }
  const data = (await res.json().catch(() => ({}))) as Record<string, any>;
  if (!res.ok) {
    throw new Error(String(data.error ?? `request failed (${res.status})`));
  }
  return data;
}

/**
 * Resolve who is signed in.
 *
 * `GET /user` returns public profile fields and needs no permission at all, so
 * it still works with the permissionless token this sign-in now issues.
 */
async function loadViewer(state: State): Promise<void> {
  try {
    const res = await fetch("https://api.github.com/user", {
      credentials: "omit",
      headers: { Authorization: `Bearer ${state.token ?? ""}`, Accept: "application/vnd.github+json" },
    });
    if (!res.ok) return;
    const v = (await res.json()) as { login?: unknown; avatar_url?: unknown };
    if (typeof v.login === "string") {
      state.viewer = { login: v.login, avatarUrl: String(v.avatar_url ?? "") };
    }
  } catch {
    /* chip falls back to the plain signed-in label */
  }
  renderIdentity(state);
  // Knowing who is signed in is what reveals the delete control on their own
  // cards, so the rail has to be repainted once the viewer resolves.
  refresh(state);
}

function signOut(state: State): void {
  auth.clearToken();
  state.token = null;
  state.viewer = null;
  renderIdentity(state);
}

/* ── Reconcile server + optimistic local state ───────────────────────────── */

/**
 * Rebuild the merged comment view from the authoritative server snapshot plus
 * this session's optimistic additions, minus anything deleted.
 *
 * This is what keeps a comment or reply posted DURING hydration from vanishing:
 * each arriving batch replaces `serverAll` wholesale, but the local additions
 * are re-merged on top every time. A server node that later carries a locally
 * deleted id is filtered out too.
 */
function rebuildAll(state: State): void {
  state.all = model.mergeComments(state);
}

/* ── Render ──────────────────────────────────────────────────────────────── */

function refresh(state: State): void {
  const { ui } = state;
  const groups = model.groupComments(state.all);
  const handlers: view.CardHandlers = {
    onHover: (c, on) => view.linkComment(ui, state.sidEls, c, on),
    onActivate: (c) => {
      const el = c.sids.length > 0 ? (state.sidEls.get(c.sids[0]) ?? null) : null;
      el?.scrollIntoView({ block: "center", behavior: "smooth" });
    },
    // Cosmetic gate only — the worker authorizes the delete itself.
    canDelete: (c) => model.ownsComment(c, state.viewer),
    onDelete: (c) => void remove(state, c),
    // Reply threads. Expansion is held on the controller so it survives the
    // rail being rebuilt after a post or a delete.
    isExpanded: (c) => state.expanded.has(c.id),
    setExpanded: (c, on) => {
      if (on) state.expanded.add(c.id);
      else state.expanded.delete(c.id);
    },
    onLayout: () => view.layoutRail(ui, groups.placed, state.sidEls),
    isSignedIn: () => state.token !== null,
    onSignIn: () => void doSignIn(state),
    onReply: (c, text) => reply(state, c, text),
    canDeleteReply: (r) => model.ownsComment(r, state.viewer),
    onDeleteReply: (c, r) => void removeReply(state, c, r),
  };
  state.litSids = view.renderHighlights(
    state.sidEls,
    model.highlightPlan(groups.placed),
    state.litSids,
  );
  view.renderRail(ui, groups, handlers);
  view.renderArchived(ui, groups.archived, handlers);
  ui.railCount.textContent = `· ${railHead(state, groups)}`;
  view.layoutRail(ui, groups.placed, state.sidEls);
}

/** The rail-head status line. Overflow is surfaced, never a silent truncation. */
function railHead(state: State, groups: model.CommentGroups): string {
  if (state.notice) return state.notice;
  if (state.loadFailed) return "comments unavailable";
  const counts = model.countLabel(model.activeComments(groups));
  const notes = [];
  if (state.overflow > 0) notes.push(`${state.overflow} shown unanchored (page limit)`);
  if (state.truncated) notes.push("some comments not shown (size limit)");
  return notes.length > 0 ? `${counts} · ${notes.join(" · ")}` : counts;
}

/**
 * Post a reply under an existing comment.
 *
 * Resolves once the rail has been rebuilt with the new reply; rejects with the
 * message the reply box should show. Like a top-level post this is optimistic —
 * the worker's read is edge-cached, so the reply is drawn locally and confirmed
 * by the next natural load.
 */
async function reply(state: State, c: model.PlacedComment, text: string): Promise<void> {
  if (!state.token) throw new Error("Sign in with GitHub to reply.");
  if (text.length > model.MAX_TEXT_CHARS) {
    throw new Error(`Too long — ${model.MAX_TEXT_CHARS} characters maximum.`);
  }
  let posted: Record<string, any>;
  try {
    posted = await workerWrite(state, "POST", model.newReplyPayload(state.cfg.paperId, c.id, text));
  } catch (err) {
    throw new Error(failureMessage("Could not post the reply", err));
  }
  const newReply: model.PlacedReply = {
    id: typeof posted?.id === "string" ? posted.id : `local-${Date.now()}`,
    login: state.viewer?.login ?? "you",
    avatarUrl: model.isSafeAvatarUrl(state.viewer?.avatarUrl) ? state.viewer!.avatarUrl : null,
    createdAt: typeof posted?.createdAt === "string" ? posted.createdAt : new Date().toISOString(),
    text: text.trim().slice(0, model.MAX_TEXT_CHARS),
  };
  // Held as an optimistic local addition, so a hydration batch overwriting
  // `serverAll` cannot drop it.
  const existing = state.localReplies.get(c.id) ?? [];
  state.localReplies.set(c.id, [...existing, newReply]);
  state.expanded.add(c.id);
  state.notice = null;
  rebuildAll(state);
  refresh(state);
}

/** Delete one of the visitor's own replies. GitHub is again the authority. */
async function removeReply(
  state: State,
  c: model.PlacedComment,
  r: model.PlacedReply,
): Promise<void> {
  state.notice = null;
  try {
    await workerWrite(state, "DELETE", { id: r.id });
    state.deleted.add(r.id);
    // Drop it from any optimistic local list too.
    const local = state.localReplies.get(c.id);
    if (local) state.localReplies.set(c.id, local.filter((x) => x.id !== r.id));
  } catch (err) {
    state.notice = failureMessage("could not delete the reply", err);
  }
  rebuildAll(state);
  refresh(state);
}

/**
 * A failure line that keeps GitHub's own wording, in parentheses.
 *
 * The message is a server string and is only ever written with `textContent`.
 */
function failureMessage(prefix: string, err: unknown): string {
  if (err instanceof AuthExpired) return "Session expired — sign in again.";
  const detail = err instanceof Error ? err.message.trim() : "";
  return detail ? `${prefix} (${detail}).` : `${prefix}.`;
}

/**
 * Delete one of the visitor's own comments.
 *
 * The button is only offered on the viewer's own cards, but that is not what
 * makes this safe: the worker re-checks that the comment was posted through it
 * and carries this caller's stamped login, and refuses otherwise. A failure
 * simply re-renders — the card comes back.
 */
async function remove(state: State, c: model.PlacedComment): Promise<void> {
  state.notice = null;
  try {
    await workerWrite(state, "DELETE", { id: c.id });
    state.deleted.add(c.id);
    // Drop an optimistic local copy too, so it does not reappear on rebuild.
    state.localComments = state.localComments.filter((x) => x.id !== c.id);
  } catch (err) {
    state.notice = failureMessage("could not delete", err);
  }
  rebuildAll(state);
  refresh(state);
}

function renderIdentity(state: State): void {
  const { ui } = state;
  while (ui.idChip.firstChild) ui.idChip.removeChild(ui.idChip.firstChild);
  if (!state.token) {
    ui.idChip.hidden = true;
    ui.signIn.hidden = false;
    ui.signInNote.hidden = false;
    ui.post.disabled = true;
    return;
  }
  const login = state.viewer?.login ?? "signed in";
  const avatarUrl = state.viewer?.avatarUrl;
  if (model.isSafeAvatarUrl(avatarUrl)) {
    const img = document.createElement("img");
    img.className = "cs-av";
    img.setAttribute("alt", "");
    img.setAttribute("width", "18");
    img.setAttribute("height", "18");
    img.setAttribute("referrerpolicy", "no-referrer");
    img.setAttribute("src", avatarUrl);
    ui.idChip.appendChild(img);
  } else {
    const initials = document.createElement("span");
    initials.className = "cs-av";
    initials.textContent = model.initialsOf(login);
    ui.idChip.appendChild(initials);
  }
  const name = document.createElement("span");
  name.textContent = login;
  ui.idChip.appendChild(name);
  ui.idChip.hidden = false;
  ui.signIn.hidden = true;
  ui.signInNote.hidden = true;
  ui.post.disabled = false;
}

function setStatus(state: State, message: string): void {
  state.ui.status.textContent = message;
}

/* ── Selection → composer ────────────────────────────────────────────────── */

function intersects(range: Range, el: Element): boolean {
  try {
    return range.intersectsNode(el);
  } catch {
    const own = el.ownerDocument.createRange();
    own.selectNodeContents(el);
    return (
      range.compareBoundaryPoints(Range.END_TO_START, own) < 0 &&
      range.compareBoundaryPoints(Range.START_TO_END, own) > 0
    );
  }
}

function selectionPending(state: State): Pending | null {
  const sel = window.getSelection();
  if (!sel || sel.isCollapsed || sel.rangeCount === 0) return null;
  const range = sel.getRangeAt(0);
  if (!state.bodyRoot.contains(range.commonAncestorContainer)) return null;
  const hits: number[] = [];
  for (const [sid, el] of state.sidEls) {
    if (!intersects(range, el)) continue;
    const i = state.index.get(sid);
    if (i !== undefined) hits.push(i);
  }
  if (hits.length === 0) return null;
  const start = Math.min(...hits);
  const end = Math.min(Math.max(...hits) + 1, start + model.MAX_ANCHOR_COUNT);
  const slice = state.sentences.slice(start, end);
  return { start, end, sids: slice.map((s) => s.id), quote: slice.map((s) => s.text).join(" ") };
}

/** Position an absolutely placed element; coordinates are viewport-relative. */
function place(state: State, el: HTMLElement, x: number, y: number): void {
  const box = state.host.getBoundingClientRect();
  const width = el.offsetWidth || 0;
  const clampedX = Math.min(Math.max(x, box.left + 8), Math.max(box.left + 8, box.right - width - 8));
  el.style.left = `${Math.round(clampedX - box.left)}px`;
  el.style.top = `${Math.round(y - box.top)}px`;
}

function hideSelButton(state: State): void {
  state.ui.selBtn.hidden = true;
}

function showSelButton(state: State, pending: Pending): void {
  const sel = window.getSelection();
  if (!sel || sel.rangeCount === 0) return;
  const rect = sel.getRangeAt(0).getBoundingClientRect();
  state.pending = pending;
  state.ui.selBtn.hidden = false;
  place(state, state.ui.selBtn, rect.left, rect.top - 38);
}

function openComposer(state: State): void {
  const pending = state.pending;
  if (!pending) return;
  const { ui } = state;
  for (const sid of pending.sids) state.sidEls.get(sid)?.classList.add("cs-pending");
  ui.quote.textContent = `“${model.truncate(pending.quote, 120)}”`;
  ui.snap.textContent = model.snapNote(pending.sids.length);
  setTag(state, "none");
  ui.text.value = "";
  ui.counter.textContent = "";
  setStatus(state, "");
  ui.post.disabled = !state.token;
  ui.composer.hidden = false;
  const first = state.sidEls.get(pending.sids[0]) ?? null;
  const rect = (first ?? state.bodyRoot).getBoundingClientRect();
  place(state, ui.composer, rect.left, rect.bottom + 8);
  ui.text.focus();
  window.getSelection()?.removeAllRanges();
}

function closeComposer(state: State): void {
  state.ui.composer.hidden = true;
  for (const sid of state.pending?.sids ?? []) {
    state.sidEls.get(sid)?.classList.remove("cs-pending");
  }
  state.pending = null;
}

function setTag(state: State, tag: CommentTag): void {
  state.tag = tag;
  for (const btn of Array.from(state.ui.seg.querySelectorAll<HTMLButtonElement>("button[data-tag]"))) {
    const on = btn.getAttribute("data-tag") === tag;
    btn.classList.toggle("is-on", on);
    btn.setAttribute("aria-pressed", on ? "true" : "false");
  }
  state.ui.tagNote.textContent = model.tagExplainer(tag);
}

/* ── Posting ─────────────────────────────────────────────────────────────── */

async function submit(state: State): Promise<void> {
  const pending = state.pending;
  const text = state.ui.text.value.trim();
  if (!pending || !text) return;
  if (!state.token) {
    setStatus(state, "Sign in with GitHub to post.");
    return;
  }
  if (text.length > model.MAX_TEXT_CHARS) {
    setStatus(state, `Too long — ${model.MAX_TEXT_CHARS} characters maximum.`);
    return;
  }
  state.ui.post.disabled = true;
  setStatus(state, "Posting…");
  try {
    const anchor = makeAnchor(state.sentences, pending.start, pending.end);
    const comment = await workerWrite(
      state,
      "POST",
      model.newCommentPayload({
        paper: state.cfg.paperId,
        tag: state.tag,
        text,
        anchor,
        revision: state.cfg.revision,
      }),
    );
    // Optimistic: the worker's read is edge-cached for 60s, so the new comment
    // is drawn locally and picked up naturally on the next load rather than
    // busting a cache the whole site shares. It is held as a LOCAL addition so
    // a still-arriving hydration batch cannot overwrite it out of existence.
    state.localComments.push({
      id: typeof comment?.id === "string" ? comment.id : `local-${Date.now()}`,
      login: state.viewer?.login ?? "you",
      avatarUrl: model.isSafeAvatarUrl(state.viewer?.avatarUrl) ? state.viewer!.avatarUrl : null,
      createdAt: typeof comment?.createdAt === "string" ? comment.createdAt : new Date().toISOString(),
      tag: state.tag,
      text,
      kind: "anchored",
      sids: pending.sids.slice(),
      quote: anchor.exact,
      revision: state.cfg.revision || null,
      order: pending.start,
      replies: [],
    });
    closeComposer(state);
    rebuildAll(state);
    refresh(state);
  } catch (err) {
    if (err instanceof AuthExpired) {
      setStatus(state, "Session expired — sign in again.");
    } else {
      // The worker's error message names the actual problem (thread not open,
      // muted, rate limited); it renders via textContent, so passing it through
      // is safe.
      const detail = err instanceof Error && err.message ? ` (${err.message.slice(0, 140)})` : "";
      setStatus(state, `Could not post — please try again.${detail}`);
    }
  } finally {
    state.ui.post.disabled = !state.token;
  }
}

/* ── Wiring ──────────────────────────────────────────────────────────────── */

function wire(state: State): void {
  const { ui } = state;
  renderIdentity(state);

  const maybeSelect = (target: EventTarget | null) => {
    if (!ui.composer.hidden) return;
    if (target instanceof Node && (ui.composer.contains(target) || ui.selBtn.contains(target))) return;
    window.setTimeout(() => {
      // The reader is interacting with the prose — segment now if idle time has
      // not already done so. This is the lazy path for a comment-free paper.
      ensureSegmented(state);
      const pending = selectionPending(state);
      if (!pending) {
        hideSelButton(state);
        return;
      }
      showSelButton(state, pending);
    }, 0);
  };
  document.addEventListener("mouseup", (e) => maybeSelect(e.target));
  document.addEventListener("keyup", (e) => {
    if (e.key === "Shift" || e.key.startsWith("Arrow")) maybeSelect(e.target);
  });
  document.addEventListener("mousedown", (e) => {
    const t = e.target;
    if (t instanceof Node && (ui.selBtn.contains(t) || ui.composer.contains(t))) return;
    hideSelButton(state);
    if (!ui.composer.hidden) closeComposer(state);
  });

  ui.selBtn.addEventListener("click", () => {
    hideSelButton(state);
    openComposer(state);
  });
  ui.cancel.addEventListener("click", () => closeComposer(state));
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !ui.composer.hidden) closeComposer(state);
  });
  for (const btn of Array.from(ui.seg.querySelectorAll<HTMLButtonElement>("button[data-tag]"))) {
    btn.addEventListener("click", () => {
      const tag = btn.getAttribute("data-tag");
      if (tag === "none" || tag === "verified" || tag === "problem") setTag(state, tag);
    });
  }
  ui.text.addEventListener("input", () => {
    const len = ui.text.value.length;
    ui.counter.textContent =
      len > model.TEXT_WARN_CHARS ? `${len} / ${model.MAX_TEXT_CHARS}` : "";
  });
  ui.post.addEventListener("click", () => void submit(state));
  ui.signIn.addEventListener("click", () => void doSignIn(state));

  // Hovering a highlight links its card(s); clicking scrolls the rail to them.
  // Formal blocks own their own click (the Lean drawer), so leave those alone.
  state.bodyRoot.addEventListener("mouseover", (e) => onSentenceHover(state, e, true));
  state.bodyRoot.addEventListener("mouseout", (e) => onSentenceHover(state, e, false));
  state.bodyRoot.addEventListener("click", (e) => {
    const el = sentenceFrom(e.target);
    if (!el || el.closest("[data-objid], .leanref")) return;
    const sid = el.dataset.sid ?? "";
    const c = state.all.find((x) => x.sids.includes(sid));
    if (c) view.scrollToCard(state.ui, c);
  });

  let resizeTimer = 0;
  window.addEventListener("resize", () => {
    window.clearTimeout(resizeTimer);
    resizeTimer = window.setTimeout(() => refresh(state), 120);
  });
  window.addEventListener("load", () => refresh(state));

  // One session per page: adopt a sign-in or sign-out made through another
  // widget (the Proof map shares the same stored token), so the reader never
  // signs in twice on one paper.
  window.addEventListener(auth.AUTH_EVENT, () => syncAuth(state));
}

function syncAuth(state: State): void {
  const token = auth.readToken();
  if (token === state.token) return;
  state.token = token;
  state.viewer = null;
  renderIdentity(state);
  if (token) void loadViewer(state);
  else refresh(state);
}

function sentenceFrom(target: EventTarget | null): HTMLElement | null {
  if (!(target instanceof Element)) return null;
  return target.closest<HTMLElement>(`.${SENTENCE_CLASS}`);
}

function onSentenceHover(state: State, e: Event, on: boolean): void {
  const el = sentenceFrom(e.target);
  if (!el) return;
  const sid = el.dataset.sid ?? "";
  for (const c of state.all) {
    if (c.sids.includes(sid)) view.linkComment(state.ui, state.sidEls, c, on);
  }
}

async function doSignIn(state: State): Promise<void> {
  setStatus(state, "Opening GitHub…");
  try {
    const token = await auth.signIn(state.cfg.worker);
    state.token = token; // before writeToken: its broadcast must find us in sync
    auth.writeToken(token);
    setStatus(state, "");
    renderIdentity(state);
    await loadViewer(state);
  } catch {
    setStatus(state, "Sign-in did not complete.");
  }
}
