/**
 * The proof map's SVG marks, as one string — the single source of truth for
 * what a chip and an edge look like.
 *
 * Both renderers use this: the Astro component emits it at BUILD time (so the
 * map draws with JavaScript off), and the client re-emits it when the rail's
 * real width differs from the width the page was built for — a rail that grows
 * with the viewport gets a graph re-wrapped to fit, not a stretched picture.
 * Keeping one generator is what stops those two from drifting apart.
 *
 * Only `<defs>` lives in the component; everything here goes inside the
 * `#pm-marks` group, which is what the client swaps.
 */

import type { ProofLayout } from "./proofGraph.js";

/** Escape a value for an XML attribute or text node. */
function esc(value: string): string {
  return value
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

/** The full title a chip carries as its tooltip and accessible name. */
export function chipTitle(label: string, title: string | null): string {
  return title ? `${label} — ${title}` : label;
}

/**
 * Edges first, then chips, so a chip is never drawn under a line it belongs to.
 * Every chip is a real `#obj-…` link: that is the JS-off navigation path, and
 * the controller only intercepts it to add the richer behaviour.
 */
export function proofMapMarks(layout: ProofLayout): string {
  const half = layout.nodeH / 2;
  const edges = layout.edges
    .map(
      (e) =>
        `<path class="pm-edge" d="${esc(e.d)}" marker-end="url(#pm-arr)"` +
        ` data-from="${esc(e.from)}" data-to="${esc(e.to)}"></path>`,
    )
    .join("");
  const nodes = layout.nodes
    .map((n) => {
      const name = chipTitle(n.label, n.title);
      return (
        `<a class="pm-node${n.top ? " pm-top" : ""}" href="#obj-${esc(n.id)}"` +
        ` data-pm-node="${esc(n.id)}" aria-label="${esc(n.title ? `${n.label}: ${n.title}` : n.label)}">` +
        `<title>${esc(name)}</title>` +
        `<rect class="pm-pill" x="${n.x - n.w / 2}" y="${n.y - half}" width="${n.w}" height="${layout.nodeH}" rx="6"></rect>` +
        `<text class="pm-lbl" x="${n.x}" y="${n.y + layout.fontPx * 0.36}" text-anchor="middle" font-size="${layout.fontPx}">${esc(n.short)}</text>` +
        `<circle class="pm-dot" cx="${n.x + n.w / 2 - 3.5}" cy="${n.y - half + 3.5}" r="2.6"></circle>` +
        `</a>`
      );
    })
    .join("");
  return edges + nodes;
}
