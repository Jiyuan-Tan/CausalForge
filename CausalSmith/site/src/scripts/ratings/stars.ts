/**
 * The 1–5 star strip — one renderer for every place a rating widget appears
 * (the paper title row, the Proof map's preview card), so the two cannot drift.
 *
 * Discoverability is the design problem here, and three things carry it:
 *
 *   • An explicit CALL TO ACTION: until the viewer has rated, a pill button
 *     ("☆ Rate this paper") sits in front of the stars — the storefront idiom.
 *     Clicking it pulses the star strip and moves keyboard focus to it, so the
 *     button always visibly does something and the stars are named as the input.
 *   • HOVER PREVIEW: moving across the strip fills the stars up to the cursor,
 *     the universal "these are buttons" affordance. Restored on leave.
 *   • The caption spells the numbers out — color and glyphs are never the
 *     only carrier.
 *
 * Filled stars show YOUR rating when you have one (accent), else the running
 * average (gold). Clicking the star you already gave is the withdraw gesture.
 * Everything reader-derived is written with `textContent`.
 */

import type { RatingSummary } from "./api.js";

export interface StarsOptions {
  summary: RatingSummary | null;
  signedIn: boolean;
  busy: boolean;
  /** What the thing being rated is called ("paper", "statement"). */
  noun: string;
  /** Show the "Rate this <noun>" / label pill (default true). */
  cta?: boolean;
  onRate: (stars: number) => void;
  /** Extra work on a CTA click, besides pulsing/focusing the stars — the
   *  controllers use it to start the sign-in right away, so the button's
   *  promise ("rate this") begins with one click instead of two. */
  onCta?: () => void;
}

function clear(node: Element): void {
  while (node.firstChild) node.removeChild(node.firstChild);
}

/** (Re)build the widget inside `host`. */
export function renderStars(host: HTMLElement, opts: StarsOptions): void {
  clear(host);
  const mine = opts.summary?.mine ?? null;
  const avg = opts.summary && opts.summary.count > 0 ? opts.summary.avg : null;
  const resting = mine ?? (avg === null ? 0 : Math.round(avg));

  const strip = document.createElement("span");
  strip.className = "rate-stars";
  strip.setAttribute("role", "radiogroup");
  strip.setAttribute("aria-label", `Rate this ${opts.noun}, 1 to 5 stars`);

  const buttons: HTMLButtonElement[] = [];
  /** Fill stars up to `k` (hover preview), or back to the resting display. */
  const paint = (k: number | null) => {
    const upto = k ?? resting;
    buttons.forEach((b, i) => {
      b.textContent = i < upto ? "★" : "☆";
      b.classList.toggle("is-preview", k !== null && i < upto);
      b.classList.toggle("is-mine", k === null && mine !== null && i < mine);
    });
  };

  for (let n = 1; n <= 5; n++) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "rate-star";
    btn.disabled = opts.busy;
    btn.setAttribute("role", "radio");
    btn.setAttribute("aria-checked", mine === n ? "true" : "false");
    btn.title = !opts.signedIn
      ? `Rate ${n}/5 (opens GitHub sign-in)`
      : mine === n
        ? "Click again to withdraw your rating"
        : `Rate ${n}/5`;
    btn.addEventListener("click", () => opts.onRate(n));
    btn.addEventListener("mouseenter", () => paint(n));
    btn.addEventListener("mouseleave", () => paint(null));
    btn.addEventListener("focus", () => paint(n));
    btn.addEventListener("blur", () => paint(null));
    buttons.push(btn);
    strip.appendChild(btn);
  }
  paint(null);

  if (opts.cta !== false) {
    if (mine === null) {
      // Not yet rated: a real button, and it really does something — names the
      // stars as the input by pulsing them and handing them keyboard focus.
      const cta = document.createElement("button");
      cta.type = "button";
      cta.className = "rate-cta";
      cta.textContent = opts.signedIn
        ? `☆ Rate this ${opts.noun}`
        : `☆ Sign in & rate this ${opts.noun}`;
      cta.addEventListener("click", () => {
        strip.classList.remove("rate-pulse");
        // Reflow so a second click restarts the animation.
        void strip.offsetWidth;
        strip.classList.add("rate-pulse");
        buttons[0]?.focus();
        opts.onCta?.();
      });
      host.appendChild(cta);
    } else {
      const label = document.createElement("span");
      label.className = "rate-label";
      label.textContent = "reader rating";
      host.appendChild(label);
    }
  }
  host.appendChild(strip);

  const caption = document.createElement("span");
  caption.className = "rate-caption";
  if (avg === null) {
    caption.textContent = "no ratings yet";
  } else {
    const count = opts.summary!.count;
    caption.textContent =
      `${avg}/5 · ${count} rating${count === 1 ? "" : "s"}` +
      (mine !== null ? ` · yours: ${mine}` : "");
  }
  host.appendChild(caption);
}
