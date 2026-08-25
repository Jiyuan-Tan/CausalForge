/**
 * DOM rendering for the margin rail, the archive, and the sentence highlights.
 *
 * Every node here is built with `createElement` + `textContent` + `setAttribute`.
 * There is no `innerHTML` anywhere in this file, and there must never be: all of
 * the strings involved (comment text, author logins, quotes, dates) come from a
 * public GitHub Discussion that anyone may write into. `src` is set on an avatar
 * only after the URL has been checked against GitHub's avatar host; anything
 * else falls back to drawn initials.
 *
 * Comment text is rendered as PLAIN TEXT — no markdown, no HTML. Line breaks
 * survive through CSS `white-space: pre-line` (see comments.css). The GitHub
 * Discussion view renders the same body as markdown; the paper page deliberately
 * does not, because rendering markdown here would mean building markup from a
 * stranger's string.
 */

import type { SidMap } from "../commentsDom.js";
import {
  archivedNote,
  driftNote,
  formatWhen,
  tagLabel,
  truncate,
  type CommentGroups,
  type Highlight,
  type PlacedComment,
} from "./model.js";
import { avatar, clear, deleteControl, textLine } from "./parts.js";
import { appendReplies, type ReplyHandlers } from "./replies.js";

/** Quote lengths in the card / archive, matching the design reference. */
const CARD_QUOTE_CHARS = 110;
const ARCHIVE_QUOTE_CHARS = 160;
/** Below this the rail flows under the paper as a plain list (see comments.css). */
export const WIDE_MIN_PX = 1300;

export interface CommentsUi {
  root: HTMLElement;
  rail: HTMLElement;
  railCount: HTMLElement;
  railThread: HTMLAnchorElement;
  railCards: HTMLElement;
  railGeneral: HTMLElement;
  railEmpty: HTMLElement;
  archived: HTMLDetailsElement;
  archivedSummary: HTMLElement;
  archivedList: HTMLElement;
  selBtn: HTMLButtonElement;
  composer: HTMLElement;
  quote: HTMLElement;
  snap: HTMLElement;
  seg: HTMLElement;
  tagNote: HTMLElement;
  text: HTMLTextAreaElement;
  counter: HTMLElement;
  status: HTMLElement;
  idChip: HTMLElement;
  signIn: HTMLButtonElement;
  cancel: HTMLButtonElement;
  post: HTMLButtonElement;
}

function need<T extends HTMLElement>(id: string): T {
  const el = document.getElementById(id);
  if (!el) throw new Error(`comments: missing #${id}`);
  return el as T;
}

/** Collect the static shell rendered by PaperComments.astro; null if absent. */
export function queryUi(): CommentsUi | null {
  try {
    return {
      root: need("cs-comments"),
      rail: need("cs-rail"),
      railCount: need("cs-rail-count"),
      railThread: need<HTMLAnchorElement>("cs-rail-thread"),
      railCards: need("cs-rail-cards"),
      railGeneral: need("cs-rail-general"),
      railEmpty: need("cs-rail-empty"),
      archived: need<HTMLDetailsElement>("cs-archived"),
      archivedSummary: need("cs-archived-summary"),
      archivedList: need("cs-archived-list"),
      selBtn: need<HTMLButtonElement>("cs-selbtn"),
      composer: need("cs-composer"),
      quote: need("cs-quote"),
      snap: need("cs-snap"),
      seg: need("cs-seg"),
      tagNote: need("cs-tagnote"),
      text: need<HTMLTextAreaElement>("cs-text"),
      counter: need("cs-counter"),
      status: need("cs-status"),
      idChip: need("cs-idchip"),
      signIn: need<HTMLButtonElement>("cs-signin"),
      cancel: need<HTMLButtonElement>("cs-cancel"),
      post: need<HTMLButtonElement>("cs-post"),
    };
  } catch {
    return null;
  }
}

const HL_CLASSES = ["cs-hl-none", "cs-hl-verified", "cs-hl-problem", "cs-hl-drift", "cs-linked"];

/** Repaint sentence highlights from the plan (clears everything first). Only the
 *  previously-lit sentences are cleared, so this never scans the whole tree. */
export function renderHighlights(
  sidmap: SidMap,
  plan: Map<string, Highlight>,
  litBefore: Set<string>,
): Set<string> {
  for (const sid of litBefore) {
    sidmap.get(sid)?.classList.remove(...HL_CLASSES);
  }
  const lit = new Set<string>();
  for (const [sid, hl] of plan) {
    const el = sidmap.get(sid);
    if (!el) continue;
    el.classList.add(`cs-hl-${hl.tag}`);
    if (hl.drift) el.classList.add("cs-hl-drift");
    lit.add(sid);
  }
  return lit;
}

function byline(c: PlacedComment, whenText: string): HTMLElement {
  const row = document.createElement("div");
  row.className = "cs-byline";
  row.appendChild(avatar(c));
  const name = document.createElement("span");
  name.className = "cs-name";
  name.textContent = c.login;
  row.appendChild(name);
  const label = tagLabel(c.tag);
  if (label) {
    const badge = document.createElement("span");
    badge.className = `cs-tagb cs-t-${c.tag}`;
    badge.textContent = label;
    row.appendChild(badge);
  }
  const when = document.createElement("span");
  when.className = "cs-when";
  when.textContent = whenText;
  row.appendChild(when);
  return row;
}

export interface CardHandlers extends ReplyHandlers {
  onHover(c: PlacedComment, on: boolean): void;
  onActivate(c: PlacedComment): void;
  /** Whether to OFFER deletion. Cosmetic — GitHub decides who may delete. */
  canDelete?(c: PlacedComment): boolean;
  onDelete?(c: PlacedComment): void;
}

function buildCard(c: PlacedComment, handlers: CardHandlers): HTMLElement {
  const card = document.createElement("div");
  card.className = `cs-card cs-kind-${c.kind}`;
  card.setAttribute("data-cid", c.id);
  // A focusable container rather than role="button": own cards nest a real
  // delete button, and an interactive control inside a role="button" is invalid.
  card.setAttribute("tabindex", "0");
  card.setAttribute(
    "aria-label",
    c.kind === "general"
      ? `General comment by ${c.login}`
      : `Comment by ${c.login} — go to the passage`,
  );
  const head = byline(c, formatWhen(c.createdAt));
  if (handlers.canDelete?.(c)) head.appendChild(deleteControl("comment", () => handlers.onDelete?.(c)));
  card.appendChild(head);
  if (c.quote) {
    card.appendChild(textLine("cs-quote", `“${truncate(c.quote, CARD_QUOTE_CHARS)}”`));
  }
  card.appendChild(textLine("cs-body", c.text));
  if (c.kind === "drifted") {
    const note = driftNote(c.tag);
    const el = textLine(`cs-drift-note${note.strong ? " cs-strong" : ""}`, note.text);
    card.appendChild(el);
  }
  appendReplies(card, c, handlers);
  card.addEventListener("mouseenter", () => handlers.onHover(c, true));
  card.addEventListener("mouseleave", () => handlers.onHover(c, false));
  card.addEventListener("focus", () => handlers.onHover(c, true));
  card.addEventListener("blur", () => handlers.onHover(c, false));
  card.addEventListener("click", (e) => {
    if (e.target instanceof Element && e.target.closest(".cs-del-wrap, .cs-footer, .cs-thread")) {
      return;
    }
    handlers.onActivate(c);
  });
  card.addEventListener("keydown", (e) => {
    // Only the card's own key presses jump; a nested button keeps its keys.
    if (e.target !== card) return;
    if (e.key === "Enter" || e.key === " ") {
      e.preventDefault();
      handlers.onActivate(c);
    }
  });
  return card;
}

function buildArchivedCard(c: PlacedComment, handlers?: CardHandlers): HTMLElement {
  const card = document.createElement("div");
  card.className = "cs-acard";
  card.setAttribute("data-cid", c.id);
  const when = formatWhen(c.createdAt);
  const row = byline(c, "");
  const version = document.createElement("span");
  version.className = "cs-vlbl";
  version.textContent = when ? `on the version of ${when}` : "on an earlier version";
  row.appendChild(version);
  if (handlers?.canDelete?.(c)) {
    row.appendChild(deleteControl("comment", () => handlers.onDelete?.(c)));
  }
  card.appendChild(row);
  if (c.quote) {
    card.appendChild(
      textLine("cs-oq", `which read: “${truncate(c.quote, ARCHIVE_QUOTE_CHARS)}”`),
    );
  }
  card.appendChild(textLine("cs-body", c.text));
  card.appendChild(textLine("cs-anote", archivedNote(c.tag)));
  if (handlers) appendReplies(card, c, handlers);
  return card;
}

/** Rebuild the rail: positioned cards, then the unanchored "General" group. */
export function renderRail(
  ui: CommentsUi,
  groups: CommentGroups,
  handlers: CardHandlers,
): void {
  clear(ui.railCards);
  clear(ui.railGeneral);
  for (const c of groups.placed) ui.railCards.appendChild(buildCard(c, handlers));
  if (groups.general.length > 0) {
    const head = document.createElement("div");
    head.className = "cs-group-head";
    head.textContent = "General comments";
    ui.railGeneral.appendChild(head);
    for (const c of groups.general) ui.railGeneral.appendChild(buildCard(c, handlers));
  }
  const total = groups.placed.length + groups.general.length;
  ui.railEmpty.hidden = total > 0;
}

export function renderArchived(
  ui: CommentsUi,
  archived: PlacedComment[],
  handlers?: CardHandlers,
): void {
  clear(ui.archivedList);
  ui.archived.hidden = archived.length === 0;
  if (archived.length === 0) return;
  ui.archivedSummary.textContent = `Comments on earlier versions (${archived.length})`;
  for (const c of archived) ui.archivedList.appendChild(buildArchivedCard(c, handlers));
}

/** Point the rail head's thread link at the paper's discussion, when there is one. */
export function renderThreadLink(
  ui: CommentsUi,
  repo: string | null,
  discussionNumber: number | null,
): void {
  const okRepo = typeof repo === "string" && /^[\w.-]{1,64}\/[\w.-]{1,64}$/.test(repo);
  const okNumber = typeof discussionNumber === "number" && Number.isInteger(discussionNumber);
  if (!okRepo || !okNumber) {
    ui.railThread.hidden = true;
    return;
  }
  ui.railThread.setAttribute("href", `https://github.com/${repo}/discussions/${discussionNumber}`);
  ui.railThread.hidden = false;
}

function cardFor(ui: CommentsUi, id: string): HTMLElement | null {
  for (const card of Array.from(ui.root.querySelectorAll<HTMLElement>(".cs-card"))) {
    if (card.getAttribute("data-cid") === id) return card;
  }
  return null;
}

/** Two-way hover link: card ↔ its highlighted sentences. */
export function linkComment(
  ui: CommentsUi,
  sidmap: SidMap,
  c: PlacedComment,
  on: boolean,
): void {
  for (const sid of c.sids) {
    sidmap.get(sid)?.classList.toggle("cs-linked", on);
  }
  cardFor(ui, c.id)?.classList.toggle("cs-linked", on);
}

export function scrollToCard(ui: CommentsUi, c: PlacedComment): void {
  cardFor(ui, c.id)?.scrollIntoView({ block: "center", behavior: "smooth" });
}

/**
 * Align each positioned card with its first sentence, pushing later cards down
 * so they never overlap. No-op below the wide breakpoint, where the rail is a
 * plain list under the paper.
 */
export function layoutRail(ui: CommentsUi, placed: PlacedComment[], sidmap: SidMap): void {
  const wide = window.innerWidth >= WIDE_MIN_PX;
  const cards = Array.from(ui.railCards.children) as HTMLElement[];
  if (!wide) {
    for (const card of cards) card.style.top = "";
    ui.railGeneral.style.marginTop = "";
    return;
  }
  const railTop = ui.rail.getBoundingClientRect().top + window.scrollY;
  let prevBottom = 34; // just under the rail head
  for (const c of placed) {
    const card = cardFor(ui, c.id);
    const first = c.sids.length > 0 ? (sidmap.get(c.sids[0]) ?? null) : null;
    if (!card || !first) continue;
    const want = first.getBoundingClientRect().top + window.scrollY - railTop;
    const top = Math.max(want, prevBottom);
    card.style.top = `${Math.round(top)}px`;
    prevBottom = top + card.offsetHeight + 10;
  }
  ui.railGeneral.style.marginTop = "";
  if (ui.railGeneral.childElementCount > 0) {
    const natural = ui.railGeneral.getBoundingClientRect().top + window.scrollY - railTop;
    ui.railGeneral.style.marginTop = `${Math.max(0, Math.round(prevBottom - natural))}px`;
  }
}
