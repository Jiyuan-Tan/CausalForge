// @vitest-environment happy-dom
//
// Regression test against markup copied VERBATIM out of a built paper page
// (dist/papers/stat_discrete_ate_minimax_loggap_polynomial_upper_match). It
// pins the shape that broke in production: a prose paragraph whose display
// equation is rendered INSIDE it, with inline KaTeX either side — where each
// formula carries an invisible `.katex-mathml` mirror and a raw-TeX
// `<annotation>` that `textContent` happily concatenates.
//
// The symptom was: select prose plus a formula, and only the formula highlights.

import { beforeEach, describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { SENTENCE_CLASS, segmentPaperBody } from "../src/scripts/commentsDom.js";

const BLOCK = readFileSync(
  resolve(import.meta.dirname, "fixtures", "real-paper-block.html"),
  "utf8",
);

/** The text a reader sees — KaTeX's MathML mirror and TeX annotation excluded. */
function visible(node: Node): string {
  if (node.nodeType === 3) return node.nodeValue ?? "";
  if (node.nodeType !== 1) return "";
  const el = node as Element;
  if (el.classList?.contains("katex-mathml") || el.localName === "annotation") return "";
  let out = "";
  for (const child of Array.from(el.childNodes)) out += visible(child);
  return out;
}

const squash = (s: string) => s.replace(/\s+/g, " ").trim();

/** The predicate the controller uses to turn a selection into sentence ids. */
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

function mount(): { root: HTMLElement; block: HTMLElement } {
  document.body.innerHTML = `<div id="paper-body">${BLOCK}</div>`;
  const root = document.getElementById("paper-body") as HTMLElement;
  return { root, block: root.querySelector("p") as HTMLElement };
}

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("a real built paper block", () => {
  it("does not silently fail: the block yields several sentences", () => {
    const { root } = mount();
    const refs = segmentPaperBody(root);
    // The per-block try/catch means a failure is invisible in the DOM — so this
    // asserts the positive: the real structure produces real sentences.
    expect(refs.length).toBeGreaterThanOrEqual(3);
    expect(refs[0].text).toContain("This paper studies minimax estimation");
    expect(refs.at(-1)?.text).toBe(
      "The upper bound is attained by a computable two-split hybrid estimator.",
    );
    // Anchor text is the VISIBLE formula, not the tripled textContent: no raw
    // TeX backslashes leak into a stored quote.
    expect(refs.some((r) => r.text.includes("\\frac"))).toBe(false);
    expect(refs.some((r) => r.text.includes("\\epsilon"))).toBe(false);
  });

  it("puts every visible character of the block inside exactly one sentence span", () => {
    const { root, block } = mount();
    segmentPaperBody(root);

    const spans = Array.from(block.querySelectorAll<HTMLElement>(`:scope > .${SENTENCE_CLASS}`));
    expect(spans.length).toBeGreaterThanOrEqual(3);

    // Nothing is nested: each span is a direct child, so "exactly one" holds.
    expect(block.querySelectorAll(`.${SENTENCE_CLASS} .${SENTENCE_CLASS}`).length).toBe(0);

    // Every direct child that carries text is inside a span, and the spans'
    // text reassembles the block's visible text.
    const loose = Array.from(block.childNodes).filter(
      (n) => !(n as HTMLElement).classList?.contains(SENTENCE_CLASS) && visible(n).trim(),
    );
    expect(loose.map((n) => visible(n).slice(0, 40))).toEqual([]);
    expect(squash(spans.map((s) => visible(s)).join(" "))).toBe(squash(visible(block)));
  });

  it("a selection spanning prose and the display equation hits ≥2 sentences", () => {
    const { root, block } = mount();
    segmentPaperBody(root);
    const display = block.querySelector(".katex-display") as HTMLElement;
    expect(display).not.toBeNull();

    // Select from the very start of the prose through the end of the formula.
    const range = document.createRange();
    range.setStart(block, 0);
    range.setEnd(display, display.childNodes.length);

    const hit = Array.from(block.querySelectorAll<HTMLElement>(`.${SENTENCE_CLASS}`)).filter((el) =>
      intersects(range, el),
    );
    expect(hit.length).toBeGreaterThanOrEqual(2);
    // …and the prose sentence is one of them, not just the formula's.
    expect(hit[0].textContent).toContain("This paper studies minimax estimation");
  });

  it("puts both the inline formula and the display equation inside the highlight", () => {
    const { root, block } = mount();
    segmentPaperBody(root);

    const display = block.querySelector(".katex-display") as HTMLElement;
    const owner = display.closest(`.${SENTENCE_CLASS}`) as HTMLElement;
    // The same sentence also carries an inline formula — the two cases the
    // highlight has to cover.
    const inline = owner.querySelector(":scope > .katex") as HTMLElement;
    expect(inline).not.toBeNull();
    expect(display).not.toBeNull();

    owner.classList.add("cs-hl-verified");
    // Both formulas resolve to a highlighted ancestor, so the CSS that paints
    // `.cs-s[class*="cs-hl-"] > .katex{,-display}` has something to paint on.
    expect(inline.closest(".cs-hl-verified")).toBe(owner);
    expect(display.closest(".cs-hl-verified")).toBe(owner);
    expect(inline.parentElement).toBe(owner);
    expect(display.parentElement).toBe(owner);
  });

  it("leaves the display equation's own structure alone", () => {
    const { root, block } = mount();
    segmentPaperBody(root);
    const display = block.querySelector(".katex-display") as HTMLElement;

    // Still a display container wrapping its .katex — KaTeX's
    // `.katex-display > .katex { display: block; text-align: center }` rule
    // still matches, so centring is unchanged.
    expect(display.classList.contains("katex-display")).toBe(true);
    expect(display.firstElementChild?.classList.contains("katex")).toBe(true);
    expect(display.getAttribute("style")).toBeNull();

    // Depth grew by EXACTLY one level: the sentence span. Before segmentation
    // the chain was p > span.katex-display; now it is
    // p > span.cs-s > span.katex-display, and nothing else was inserted.
    const chain: string[] = [];
    for (let el: Element | null = display; el && el !== block; el = el.parentElement) {
      chain.unshift(el.tagName.toLowerCase());
    }
    expect(chain).toEqual(["span", "span"]);
    expect((display.parentElement as HTMLElement).classList.contains(SENTENCE_CLASS)).toBe(true);
  });

  it("a highlight on the matched sentences covers the prose, not just the formula", () => {
    const { root, block } = mount();
    const refs = segmentPaperBody(root);

    // Highlight the sentence carrying the display equation, the way the
    // controller does after re-anchoring.
    const display = block.querySelector(".katex-display") as HTMLElement;
    const owner = display.closest(`.${SENTENCE_CLASS}`) as HTMLElement;
    owner.classList.add("cs-hl-verified");

    const highlightedText = visible(owner);
    // The highlighted span carries real prose on BOTH sides of the formula —
    // the bug highlighted the formula alone.
    expect(highlightedText).toContain("For sufficiently large sample size");
    expect(highlightedText).toContain("up to constants depending on");
    expect(highlightedText.replace(visible(display), "").trim().length).toBeGreaterThan(80);
    // … and every prose text node in it really is a descendant of the span.
    for (const node of Array.from(block.childNodes)) {
      if (node.nodeType !== 3) continue;
      expect(visible(node).trim()).toBe("");
    }
    // The formula's own sentence is not the only sentence on the page.
    expect(refs.length).toBeGreaterThan(1);
    expect(owner.getAttribute("data-sid")).toBeTruthy();
  });
});

/**
 * A display equation is a BLOCK box inside an INLINE sentence span, so the
 * span's own background can never reach it — the formula needs a painted
 * surface of its own. happy-dom has no layout or cascade, so the guarantee is
 * pinned on the stylesheet itself.
 */
describe("the stylesheet gives math a highlight surface", () => {
  const CSS = readFileSync(
    resolve(import.meta.dirname, "..", "src", "styles", "comments.css"),
    "utf8",
  ).replace(/\/\*[\s\S]*?\*\//g, "");

  const rules = [...CSS.matchAll(/([^{}]+)\{([^{}]*)\}/g)].map((m) => ({
    selector: m[1].replace(/\s+/g, " ").trim(),
    body: m[2].replace(/\s+/g, " ").trim(),
  }));
  const mathRules = rules.filter((r) => /\.katex-display/.test(r.selector));

  it("paints display math for every highlight state", () => {
    const covered = (state: string) =>
      mathRules.some((r) => r.selector.includes(state) && /background|outline|border/.test(r.body));
    expect(covered('.cs-s[class*="cs-hl-"]')).toBe(true); // none / verified / problem
    expect(covered(".cs-s.cs-hl-drift")).toBe(true);
    expect(covered(".cs-s.cs-pending")).toBe(true);
    expect(covered(".cs-s.cs-linked")).toBe(true);
  });

  it("drives those washes from the same tokens as the prose highlight", () => {
    for (const state of ["cs-hl-none", "cs-hl-verified", "cs-hl-problem"]) {
      const rule = rules.find((r) => r.selector === `.${state}`);
      expect(rule?.body).toContain("--cs-wash:");
      expect(rule?.body).toContain("--cs-line:");
    }
    expect(mathRules.some((r) => r.body.includes("var(--cs-wash)"))).toBe(true);
  });

  it("never touches layout, so a centred equation stays centred", () => {
    for (const rule of mathRules) {
      expect(rule.body).not.toMatch(/(?:^|;\s*)(display|position|margin|width|float|padding)\s*:/);
    }
    expect(mathRules.length).toBeGreaterThanOrEqual(4);
  });
});
