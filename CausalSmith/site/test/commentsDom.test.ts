// @vitest-environment happy-dom
//
// DOM segmentation of a rendered paper body. The fixtures mirror what the
// paper page actually ships: pandoc paragraphs, build-time KaTeX (inline
// `.katex` spans and `.katex-display` blocks), a raw `span.math` the client
// fallback would render later, plus the chrome that must never be segmented.

import { beforeEach, describe, expect, it } from "vitest";
import {
  SENTENCE_CLASS,
  collectSidElements,
  segmentPaperBody,
  sidElement,
} from "../src/scripts/commentsDom.js";

/** The inline-math markup KaTeX emits, abbreviated but structurally faithful. */
const INLINE_KATEX =
  '<span class="katex"><span class="katex-mathml"><math><semantics><mrow><mi>τ</mi></mrow></semantics></math></span>' +
  '<span class="katex-html" aria-hidden="true"><span class="base"><span class="mord mathnormal">τ</span></span></span></span>';

const DISPLAY_KATEX =
  '<span class="katex-display"><span class="katex"><span class="katex-html" aria-hidden="true">' +
  "inf sup E |τ̂ − τ(P)| ≥ C √(K ⁄ n) (3.1)</span></span></span>";

function mount(html: string): HTMLElement {
  document.body.innerHTML = `<div id="paper-body">${html}</div>`;
  return document.getElementById("paper-body") as HTMLElement;
}

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("segmentPaperBody", () => {
  it("wraps each sentence of a multi-sentence paragraph", () => {
    const root = mount(
      "<p>We study the ATE under weak overlap. The lower bound uses Le Cam's method. The constant is sharp.</p>",
    );
    const refs = segmentPaperBody(root);
    expect(refs.map((r) => r.text)).toEqual([
      "We study the ATE under weak overlap.",
      "The lower bound uses Le Cam's method.",
      "The constant is sharp.",
    ]);
    expect(refs.map((r) => r.id)).toEqual(["b0-s0", "b0-s1", "b0-s2"]);
    const spans = root.querySelectorAll(`.${SENTENCE_CLASS}`);
    expect(spans.length).toBe(3);
    // The paragraph still reads the same, with no text lost at the seams.
    expect(root.textContent).toBe(
      "We study the ATE under weak overlap. The lower bound uses Le Cam's method. The constant is sharp.",
    );
  });

  it("keeps an inline KaTeX span whole and inside exactly one sentence", () => {
    const root = mount(
      `<p>The estimator ${INLINE_KATEX} is consistent. A second sentence follows.</p>`,
    );
    const refs = segmentPaperBody(root);
    expect(refs.length).toBe(2);

    const katexNodes = root.querySelectorAll(".katex");
    expect(katexNodes.length).toBe(1);
    const katex = katexNodes[0];
    // The whole subtree survived: still its own parent's child, still complete.
    expect(katex.querySelector(".katex-mathml")).not.toBeNull();
    expect(katex.querySelector(".katex-html")).not.toBeNull();
    expect(katex.querySelectorAll(".base .mord").length).toBe(1);

    // …and it lives inside one sentence span, not split across two.
    const owners = Array.from(root.querySelectorAll(`.${SENTENCE_CLASS}`)).filter((s) =>
      s.contains(katex),
    );
    expect(owners.length).toBe(1);
    expect(owners[0].getAttribute("data-sid")).toBe("b0-s0");
    // KaTeX renders the formula twice (accessible MathML mirror + visual HTML),
    // and the anchor text must carry only what a reader sees — one τ, not two.
    expect(refs[0].text).toBe("The estimator τ is consistent.");
  });

  it("shifts a sentence boundary that would fall inside an atomic element", () => {
    // The period after "Section 2" sits INSIDE the <em>, so the boundary must
    // move to the element's edge rather than splitting it.
    const root = mount(
      "<p>See <em>the overlap condition of Section 2. It</em> is standard. Then we conclude.</p>",
    );
    const refs = segmentPaperBody(root);
    expect(root.querySelectorAll("em").length).toBe(1);
    const em = root.querySelector("em") as HTMLElement;
    expect(em.textContent).toBe("the overlap condition of Section 2. It");
    const owners = Array.from(root.querySelectorAll(`.${SENTENCE_CLASS}`)).filter((s) =>
      s.contains(em),
    );
    expect(owners.length).toBe(1);
    expect(refs.length).toBeGreaterThanOrEqual(2);
  });

  it("treats a display-math block as a single sentence and does not rewrap it", () => {
    const root = mount(`<p>${DISPLAY_KATEX}</p>`);
    const refs = segmentPaperBody(root);
    expect(refs.length).toBe(1);
    // The marker lands on the wrapping paragraph — nothing inside the display
    // was re-parented, so KaTeX's `.katex-display > .katex` layout still applies.
    const p = root.querySelector("p") as HTMLElement;
    const display = root.querySelector(".katex-display") as HTMLElement;
    expect(p.classList.contains(SENTENCE_CLASS)).toBe(true);
    expect(p.getAttribute("data-sid")).toBe("b0-s0");
    expect(display.classList.contains(SENTENCE_CLASS)).toBe(false);
    expect(display.firstElementChild?.className).toBe("katex");
    expect(root.querySelectorAll(`span.${SENTENCE_CLASS}`).length).toBe(0);
  });

  it("treats a raw span.math.display (client-side fallback) as one sentence", () => {
    const root = mount('<p><span class="math display">\\[x = 1. y = 2.\\]</span></p>');
    const refs = segmentPaperBody(root);
    expect(refs.length).toBe(1);
    const math = root.querySelector("span.math.display") as HTMLElement;
    expect(math.parentElement?.tagName).toBe("P");
    expect(math.parentElement?.classList.contains(SENTENCE_CLASS)).toBe(true);
  });

  it("leaves an inline span.math atomic when the fallback has not run yet", () => {
    const root = mount(
      '<p>Write <span class="math inline">\\(\\tau. X\\)</span> for the effect. Done.</p>',
    );
    segmentPaperBody(root);
    const math = root.querySelector("span.math.inline") as HTMLElement;
    expect(math.textContent).toBe("\\(\\tau. X\\)");
    const owners = Array.from(root.querySelectorAll(`.${SENTENCE_CLASS}`)).filter((s) =>
      s.contains(math),
    );
    expect(owners.length).toBe(1);
  });

  it("segments list items and skips the paragraphs nested inside them", () => {
    const root = mount("<ul><li><p>First point. Second point.</p></li></ul>");
    const refs = segmentPaperBody(root);
    expect(refs.map((r) => r.text)).toEqual(["First point.", "Second point."]);
    // The inner <p> is the innermost candidate, so it — not the <li> — is the
    // block; segmenting the <li> would have made the <p> one atomic sentence.
    expect(root.querySelectorAll(`.${SENTENCE_CLASS}`).length).toBe(2);
  });

  it("never touches the byline, the formal layer, headings, or code", () => {
    document.body.innerHTML = `
      <nav class="paper-toc"><ul><li><a href="#s">Setup</a></li></ul></nav>
      <article class="paper">
        <div class="paper-byline"><p>WP-7 · statistics · pinned commit.</p></div>
        <div id="paper-body">
          <h1 id="s">Setup and assumptions. Two sentences.</h1>
          <p>Body prose here. And more.</p>
          <pre><code>lemma foo : True. bar</code></pre>
        </div>
        <aside class="formal-layer"><p>Every object below is formalized. Click a row.</p></aside>
      </article>`;
    const root = document.getElementById("paper-body") as HTMLElement;
    const refs = segmentPaperBody(root);
    expect(refs.map((r) => r.text)).toEqual(["Body prose here.", "And more."]);
    expect(document.querySelectorAll(`.paper-byline .${SENTENCE_CLASS}`).length).toBe(0);
    expect(document.querySelectorAll(`.formal-layer .${SENTENCE_CLASS}`).length).toBe(0);
    expect(document.querySelectorAll(`.paper-toc .${SENTENCE_CLASS}`).length).toBe(0);
    expect(document.querySelectorAll(`h1 .${SENTENCE_CLASS}`).length).toBe(0);
    expect(document.querySelectorAll(`pre .${SENTENCE_CLASS}`).length).toBe(0);
  });

  it("is idempotent: a second pass re-reads the spans instead of nesting them", () => {
    const root = mount("<p>One sentence here. And a second one.</p>");
    const first = segmentPaperBody(root);
    const html = root.innerHTML;
    const second = segmentPaperBody(root);
    expect(root.innerHTML).toBe(html);
    expect(second).toEqual(first);
    expect(root.querySelectorAll(`.${SENTENCE_CLASS} .${SENTENCE_CLASS}`).length).toBe(0);
  });

  it("skips a block that throws mid-segmentation without losing the others", () => {
    const root = mount(
      "<p id='bad'>Boom goes the block. Second sentence.</p><p id='good'>Still segmented. Yes.</p>",
    );
    const bad = root.querySelector("#bad") as HTMLElement;
    // Stand-in for any DOM operation failing part-way through a block.
    Object.defineProperty(bad, "insertBefore", {
      configurable: true,
      value: () => {
        throw new Error("boom");
      },
    });
    const refs = segmentPaperBody(root);
    expect(bad.querySelectorAll(`.${SENTENCE_CLASS}`).length).toBe(0);
    expect(refs.map((r) => r.text)).toEqual(["Still segmented.", "Yes."]);
  });

  it("segments a paragraph whose display equation sits INSIDE the prose", () => {
    // Pandoc puts `\[…\]` in the middle of the paragraph that discusses it, so
    // the rendered `.katex-display` is a sibling of the prose text nodes, not a
    // block of its own. Treating it as the block skipped the surrounding prose.
    const root = mount(
      `<p>The rate is ${DISPLAY_KATEX} up to constants. A second sentence follows.</p>`,
    );
    const refs = segmentPaperBody(root);
    expect(refs.length).toBe(2);
    expect(refs[0].text).toContain("The rate is");
    expect(refs[0].text).toContain("up to constants.");
    expect(refs[1].text).toBe("A second sentence follows.");
    // The formula joined the first sentence rather than becoming the only one.
    const first = root.querySelector('[data-sid="b0-s0"]') as HTMLElement;
    expect(first.querySelector(".katex-display")).not.toBeNull();
    expect(root.querySelectorAll(".cs-s").length).toBe(2);
  });

  it("builds a complete sid → element map in one scan", () => {
    const root = mount("<p>Alpha here. Beta there.</p><p>Gamma last.</p>");
    const refs = segmentPaperBody(root);
    const map = collectSidElements(root);
    expect(map.size).toBe(refs.length);
    for (const r of refs) {
      expect(map.get(r.id)?.getAttribute("data-sid")).toBe(r.id);
    }
    // The map is the cache the controller uses instead of re-querying per comment.
    expect(map.get("b0-s1")?.textContent).toBe("Beta there.");
  });

  it("looks a sentence up by id and refuses anything selector-shaped", () => {
    const root = mount("<p>Alpha here. Beta there.</p>");
    const refs = segmentPaperBody(root);
    expect(sidElement(refs[1].id, root)?.textContent).toBe("Beta there.");
    expect(sidElement('b0-s0"], [data-sid="b0-s1', root)).toBeNull();
    expect(sidElement("no-such-sid", root)).toBeNull();
  });
});
