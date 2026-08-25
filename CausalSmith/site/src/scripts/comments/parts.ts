/**
 * Shared DOM primitives for the comments UI.
 *
 * Every node the paper page builds from GitHub data is assembled here or by the
 * two modules that import this one (`render.ts`, `replies.ts`). There is no
 * `innerHTML` in any of them and there must never be: comment and reply bodies,
 * author logins and avatar URLs are all written by strangers on a public
 * Discussion. Text goes in through `textContent`; the only attribute ever set
 * from remote data is an avatar `src`, and only after `isSafeAvatarUrl`.
 */

import { initialsOf, isSafeAvatarUrl } from "./model.js";

/** Anything with an author — a comment or one of its replies. */
export interface Authored {
  login: string;
  avatarUrl: string | null;
}

export function clear(el: HTMLElement): void {
  while (el.firstChild) el.removeChild(el.firstChild);
}

export function textLine(cls: string, value: string): HTMLElement {
  const el = document.createElement("div");
  el.className = cls;
  el.textContent = value;
  return el;
}

/** The author's GitHub avatar, or their initials when the URL is not GitHub's. */
export function avatar(a: Authored, cls = "cs-av"): HTMLElement {
  if (a.avatarUrl && isSafeAvatarUrl(a.avatarUrl)) {
    const img = document.createElement("img");
    img.className = cls;
    img.setAttribute("alt", "");
    img.setAttribute("width", "18");
    img.setAttribute("height", "18");
    img.setAttribute("loading", "lazy");
    img.setAttribute("referrerpolicy", "no-referrer");
    // Only reached for a validated https://avatars.githubusercontent.com/ URL.
    img.setAttribute("src", a.avatarUrl);
    return img;
  }
  const span = document.createElement("span");
  span.className = cls;
  span.textContent = initialsOf(a.login);
  return span;
}

/**
 * A button inside a card.
 *
 * Always stops propagation: the card is itself a jump-to-passage target, and
 * replying or deleting must never also scroll the paper.
 */
export function cardButton(
  label: string,
  cls: string,
  ariaLabel: string,
  onClick: () => void,
): HTMLButtonElement {
  const btn = document.createElement("button");
  btn.type = "button";
  btn.className = cls;
  btn.textContent = label;
  btn.setAttribute("aria-label", ariaLabel);
  btn.addEventListener("click", (e) => {
    e.stopPropagation();
    onClick();
  });
  return btn;
}

/**
 * The delete affordance: a plain text button that swaps itself for an inline
 * "Delete? Yes / No" — no `window.confirm`, and no dialog to position.
 *
 * Shown only where the caller says the signed-in viewer is the author, and even
 * then it is a convenience: `deleteDiscussionComment` is authorized by GitHub,
 * which refuses anyone who is not the author or a repo admin.
 */
export function deleteControl(what: string, onConfirm: () => void): HTMLElement {
  const wrap = document.createElement("span");
  wrap.className = "cs-del-wrap";

  const ask = () => {
    clear(wrap);
    const prompt = document.createElement("span");
    prompt.className = "cs-del-ask";
    prompt.textContent = "Delete?";
    wrap.appendChild(prompt);
    wrap.appendChild(
      cardButton("Yes", "cs-del-yes", `Confirm deleting your ${what}`, () => {
        prompt.textContent = "Deleting…";
        for (const b of Array.from(wrap.querySelectorAll("button"))) b.disabled = true;
        onConfirm();
      }),
    );
    wrap.appendChild(cardButton("No", "cs-del-no", `Keep your ${what}`, reset));
  };

  const reset = () => {
    clear(wrap);
    wrap.appendChild(cardButton("delete", "cs-del", `Delete your ${what}`, ask));
  };

  reset();
  return wrap;
}
