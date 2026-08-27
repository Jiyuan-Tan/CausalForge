/**
 * The reply thread under a comment card.
 *
 * Threads are exactly one level deep — a top-level comment and
 * its replies — and that is precisely what this exposes. Replies carry no tag
 * and no anchor: they inherit the passage their parent is attached to.
 *
 * The thread is collapsed by default so the margin rail stays scannable; the
 * footer shows either "N replies" or a ghost "Reply", and expanding reveals the
 * list plus the reply box. Every state change calls back into the controller so
 * the rail can be laid out again — a card that grows must push its neighbours
 * down.
 *
 * Reply bodies are rendered as PLAIN TEXT through `textContent`, exactly like
 * comment bodies; newlines survive via CSS `white-space: pre-line`. No markdown
 * is rendered here, so a reply body full of markup is inert on the page.
 */

import {
  MAX_TEXT_CHARS,
  TEXT_WARN_CHARS,
  formatWhen,
  replyCountLabel,
  type PlacedComment,
  type PlacedReply,
} from "./model.js";
import { avatar, cardButton, clear, deleteControl, textLine } from "./parts.js";

export interface ReplyHandlers {
  /** Whether the reply thread under this comment is open. Optional so a caller
   *  that does not track expansion still gets a working (session-local) toggle;
   *  the controller supplies both so the state survives a rail rebuild. */
  isExpanded?(c: PlacedComment): boolean;
  setExpanded?(c: PlacedComment, on: boolean): void;
  /** Card heights changed — re-run the rail layout. */
  onLayout?(): void;
  /** A viewer is signed in and can post. */
  isSignedIn?(): boolean;
  onSignIn?(): void;
  /** Resolves once the reply is posted (the rail is rebuilt by then); rejects
   *  with a message to show in the reply box. */
  onReply?(c: PlacedComment, text: string): Promise<void>;
  canDeleteReply?(r: PlacedReply): boolean;
  onDeleteReply?(c: PlacedComment, r: PlacedReply): void;
}

/**
 * Append the footer (toggle) and the thread container to a card.
 *
 * The container is filled on expand and emptied on collapse, so a collapsed
 * card carries no reply DOM at all.
 */
/** Fallback expansion state for a caller that tracks none of its own. */
const locallyOpen = new Set<string>();

function isOpen(c: PlacedComment, handlers: ReplyHandlers): boolean {
  return handlers.isExpanded ? handlers.isExpanded(c) : locallyOpen.has(c.id);
}

export function appendReplies(
  card: HTMLElement,
  c: PlacedComment,
  handlers: ReplyHandlers,
): void {
  const thread = document.createElement("div");
  thread.className = "cs-thread";

  const footer = document.createElement("div");
  footer.className = "cs-footer";
  const count = c.replies.length;
  const toggle = cardButton(
    count > 0 ? replyCountLabel(count) : "Reply",
    count > 0 ? "cs-reply-toggle" : "cs-reply-toggle cs-ghost",
    count > 0 ? `Show the ${replyCountLabel(count)} to this comment` : "Reply to this comment",
    () => setOpen(!isOpen(c, handlers)),
  );
  toggle.setAttribute("aria-expanded", "false");
  footer.appendChild(toggle);
  card.appendChild(footer);
  card.appendChild(thread);

  const setOpen = (open: boolean) => {
    handlers.setExpanded?.(c, open);
    open ? locallyOpen.add(c.id) : locallyOpen.delete(c.id);
    toggle.setAttribute("aria-expanded", open ? "true" : "false");
    clear(thread);
    if (open) fillThread(thread, c, handlers);
    handlers.onLayout?.();
  };

  if (isOpen(c, handlers)) {
    toggle.setAttribute("aria-expanded", "true");
    fillThread(thread, c, handlers);
  }
}

function fillThread(thread: HTMLElement, c: PlacedComment, handlers: ReplyHandlers): void {
  for (const reply of c.replies) thread.appendChild(buildReply(c, reply, handlers));
  thread.appendChild(buildReplyBox(c, handlers));
}

function buildReply(
  c: PlacedComment,
  reply: PlacedReply,
  handlers: ReplyHandlers,
): HTMLElement {
  const item = document.createElement("div");
  item.className = "cs-reply";
  item.setAttribute("data-rid", reply.id);

  const byline = document.createElement("div");
  byline.className = "cs-byline cs-reply-byline";
  byline.appendChild(avatar(reply, "cs-av cs-av-sm"));
  const name = document.createElement("span");
  name.className = "cs-name";
  name.textContent = reply.login;
  byline.appendChild(name);
  const when = document.createElement("span");
  when.className = "cs-when";
  when.textContent = formatWhen(reply.createdAt);
  byline.appendChild(when);
  if (handlers.canDeleteReply?.(reply)) {
    byline.appendChild(deleteControl("reply", () => handlers.onDeleteReply?.(c, reply)));
  }
  item.appendChild(byline);
  item.appendChild(textLine("cs-body cs-reply-body", reply.text));
  return item;
}

function buildReplyBox(c: PlacedComment, handlers: ReplyHandlers): HTMLElement {
  const box = document.createElement("div");
  box.className = "cs-reply-box";

  if (handlers.isSignedIn?.() !== true) {
    const note = textLine("cs-reply-note", "Sign in to reply.");
    box.appendChild(note);
    box.appendChild(
      cardButton("Sign in with GitHub", "cs-signin", "Sign in with GitHub to reply", () =>
        handlers.onSignIn?.(),
      ),
    );
    return box;
  }

  const label = document.createElement("label");
  label.className = "cs-sr-only";
  const fieldId = `cs-reply-text-${c.id.replace(/[^A-Za-z0-9_-]/g, "")}`;
  label.setAttribute("for", fieldId);
  label.textContent = "Your reply";
  const field = document.createElement("textarea");
  field.id = fieldId;
  field.className = "cs-reply-text";
  field.setAttribute("rows", "2");
  field.setAttribute("maxlength", String(MAX_TEXT_CHARS));
  field.setAttribute("placeholder", "Write a reply…");
  // Typing (and the space bar) inside the box must not reach the card, whose
  // Enter/Space jumps to the passage.
  field.addEventListener("keydown", (e) => e.stopPropagation());
  field.addEventListener("click", (e) => e.stopPropagation());

  const counter = textLine("cs-counter", "");
  const status = textLine("cs-status", "");
  field.addEventListener("input", () => {
    const len = field.value.length;
    counter.textContent = len > TEXT_WARN_CHARS ? `${len} / ${MAX_TEXT_CHARS}` : "";
  });

  const row = document.createElement("div");
  row.className = "cs-reply-actions";
  const cancel = cardButton("Cancel", "cs-cancel", "Discard this reply", () => {
    field.value = "";
    counter.textContent = "";
    status.textContent = "";
    handlers.setExpanded?.(c, false);
    locallyOpen.delete(c.id);
    const thread = box.parentElement;
    if (thread) clear(thread);
    const toggle = thread?.previousElementSibling?.querySelector("button");
    toggle?.setAttribute("aria-expanded", "false");
    handlers.onLayout?.();
  });
  const post = cardButton("Reply", "cs-post", "Post this reply", () => {
    const text = field.value.trim();
    if (!text) return;
    post.disabled = true;
    status.textContent = "Posting…";
    const done = handlers.onReply?.(c, text);
    if (!done) {
      post.disabled = false;
      return;
    }
    void done.then(
      () => {
        // The rail has been rebuilt by now; this box is detached.
        field.value = "";
        status.textContent = "";
      },
      (err: unknown) => {
        post.disabled = false;
        status.textContent = err instanceof Error ? err.message : "Could not post the reply.";
      },
    );
  });
  row.appendChild(cancel);
  row.appendChild(post);

  box.appendChild(label);
  box.appendChild(field);
  box.appendChild(counter);
  box.appendChild(status);
  box.appendChild(row);
  return box;
}
