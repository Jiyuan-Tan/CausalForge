// @vitest-environment happy-dom
//
// END-TO-END against the BUILT page, not a fixture.
//
// Twice now the unit suite was green while production was broken, and both
// times the cause was the same: a hand-written fixture that did not have the
// shape a real payload has, so two candidate render sources were
// indistinguishable and no assertion could tell them apart. This test removes
// that class of failure by booting the real `initDrawer()` against
// `dist/papers/<id>/index.html` and its real `paper-data.json`.
//
// The load-bearing assertion is the BIDIRECTIONAL token coverage sweep: every
// `data-xl` token in a block's prose must have a carrier in that entry's
// rendered panel, and vice versa. A one-sided token is exactly what both
// production bugs produced — the pair existed in the data, but only one half
// ever reached the screen.
//
// Cost: the built page is ~6MB of pre-rendered KaTeX, so it is parsed ONCE and
// every entry is opened ONCE, in `beforeAll`; the assertions then read that
// recorded sweep. Only the interaction tests re-open a panel.

import { afterAll, beforeAll, describe, expect, it, vi } from "vitest";
import { existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";

const PAPER_ID = "stat_discrete_ate_minimax_loggap_polynomial_upper_match";
const ROOT = resolve(import.meta.dirname, "..");
const DIST = resolve(ROOT, "dist", "papers", PAPER_ID);
const HTML_PATH = resolve(DIST, "index.html");
const DATA_PATH = resolve(DIST, "paper-data.json");
const CSS_PATH = resolve(ROOT, "src", "styles", "paper.css");

const HAVE_DIST = existsSync(HTML_PATH) && existsSync(DATA_PATH);
if (!HAVE_DIST) {
  console.warn(
    `[drawerRealPage] SKIPPED: no built page at ${DIST}\n` +
      `  This gate only runs against a build. Run \`npm run build\` to enable it.`,
  );
}
// A missing dist is "not checked", never a green tick.
const onBuiltPage = HAVE_DIST ? describe : describe.skip;

/* ── helpers ─────────────────────────────────────────────────────────────── */

const tokensOf = (el: Element): string[] =>
  (el.getAttribute("data-xl") ?? "").split(/\s+/).filter(Boolean);

const panelBody = () => document.getElementById("drawer-body") as HTMLElement;
const panelOpen = () => document.body.classList.contains("drawer-visible");
const hot = (el: Element) => el.classList.contains("xl-hot");

/** open() is async (payload fetch) and repaints once the name map resolves. */
async function flush(): Promise<void> {
  for (let i = 0; i < 4; i++) await new Promise((r) => setTimeout(r, 0));
}

const blockOf = (objId: string) =>
  document.querySelector<HTMLElement>(`[data-objid="${objId}"]`);

/** Real pointer traffic: mouseover/mouseout BUBBLE from the deepest element
 *  under the cursor — a CHILD of the annotated carrier, not the carrier itself.
 *  Hovering the carrier directly is an event flow browsers never produce, and
 *  faking it is what let the Lean-side bug through. `deepest` picks the element
 *  the pointer would really be over. */
const deepest = (el: Element): Element => {
  let n = el;
  // follow the first element child down; text-bearing leaves stop the descent
  while (n.firstElementChild) n = n.firstElementChild;
  return n;
};
const over = (el: Element) => deepest(el).dispatchEvent(new Event("mouseover", { bubbles: true }));
const out = (el: Element, to: Element | null = null) =>
  deepest(el).dispatchEvent(new MouseEvent("mouseout", { bubbles: true, relatedTarget: to }));
/** A click also originates at the deepest element and bubbles. */
const click = (el: Element) => deepest(el).dispatchEvent(new Event("click", { bubbles: true }));

async function openObj(objId: string): Promise<HTMLElement> {
  const block = blockOf(objId)!;
  block.dispatchEvent(new Event("click", { bubbles: true }));
  await flush();
  return block;
}

function closePanel(): void {
  document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
}

function tokenSet(root: ParentNode): Set<string> {
  const out = new Set<string>();
  for (const s of root.querySelectorAll("[data-xl]")) for (const t of tokensOf(s)) out.add(t);
  return out;
}

/** Every block that carries at least one annotated prose span. */
function annotatedBlocks(): HTMLElement[] {
  const seen = new Map<string, HTMLElement>();
  for (const span of document.querySelectorAll("#paper-body [data-xl]")) {
    const block = span.closest<HTMLElement>("[data-objid]");
    if (block?.dataset.objid && !seen.has(block.dataset.objid)) {
      seen.set(block.dataset.objid, block);
    }
  }
  return [...seen.values()];
}

/** What one entry looked like when its panel was open. */
interface Swept {
  objId: string;
  opened: boolean;
  body: Set<string>;
  panel: Set<string>;
  shared: string[];
  structured: boolean;
  /** an annotated prose span in this block that wraps display math */
  displaySpan: boolean;
  /** a paper-class chip pointing at a block that exists in this page */
  paperChip: string | null;
  /** container elements that wrongly carry a token (must always be empty) */
  containerCarriers: string[];
  /** carriers that enclose another carrier (must always be empty) */
  nestedCarriers: string[];
}

/** Containers a token must never sit on — a click in their padding would
 *  otherwise resolve to them and fire a far broader pairing. */
const CONTAINERS = ".ds-card, .ds-sub, .ds-lift, .ds-structured, .ds-rows, .cv-card, details.cv-lean-only";

onBuiltPage("the built paper page", () => {
  let paperCss = "";
  let sweep: Swept[] = [];
  /** An entry with at least one genuine two-sided pair — the interaction fixture. */
  let paired: Swept | undefined;

  beforeAll(async () => {
    const html = readFileSync(HTML_PATH, "utf8");
    const raw = readFileSync(DATA_PATH, "utf8");
    paperCss = readFileSync(CSS_PATH, "utf8");

    // Serve the real sibling payload AND the real library name map — an empty
    // name map suppresses the `a.lib-link` anchors the repaint injects into
    // every code block, which is precisely the kind of "fixture unlike
    // production" gap that has hidden bugs here before.
    const namesPath = resolve(ROOT, "dist", "library", "names.json");
    const names = existsSync(namesPath) ? readFileSync(namesPath, "utf8") : '{"names":{}}';
    vi.stubGlobal(
      "fetch",
      vi.fn(async (url: unknown) => {
        const u = String(url);
        if (u.includes("paper-data.json")) {
          return { ok: true, status: 200, json: async () => JSON.parse(raw) };
        }
        if (u.includes("names.json")) {
          return { ok: true, status: 200, json: async () => JSON.parse(names) };
        }
        return { ok: false, status: 404, json: async () => ({}) };
      }),
    );

    // Mount the built <body> verbatim. Scripts inserted via innerHTML never
    // execute (per spec), so the page's own module graph stays inert and we
    // drive the REAL controller ourselves — exactly the code the site ships.
    const body = html.match(/<body[^>]*>([\s\S]*)<\/body>/i);
    expect(body, "built page has a <body>").not.toBeNull();
    // Drop the bundled <script src> tags: happy-dom refuses to fetch them and
    // logs a NotSupportedError per tag. The inline application/json payload
    // block (which initDrawer reads) has no src and is kept.
    document.body.innerHTML = body![1].replace(/<script\b[^>]*\bsrc=[^>]*><\/script>/gi, "");

    const { initDrawer } = await import("../src/scripts/drawer.js");
    initDrawer();

    for (const block of annotatedBlocks()) {
      const objId = block.dataset.objid!;
      await openObj(objId);
      const opened = panelOpen();
      const bodyToks = tokenSet(block);
      const panelToks = opened ? tokenSet(panelBody()) : new Set<string>();
      const chip = opened
        ? panelBody().querySelector<HTMLElement>(".cv-paper-chip[data-paper-obj]")
        : null;
      sweep.push({
        objId,
        opened,
        body: bodyToks,
        panel: panelToks,
        shared: [...bodyToks].filter((t) => panelToks.has(t)),
        structured: opened && !!panelBody().querySelector(".ds-structured"),
        displaySpan: [...block.querySelectorAll("[data-xl]")].some((s) =>
          s.querySelector(".katex-display"),
        ),
        paperChip:
          chip && blockOf(chip.dataset.paperObj!) ? chip.dataset.paperObj! : null,
        containerCarriers: opened
          ? [...panelBody().querySelectorAll(CONTAINERS)]
              .filter((e) => e.hasAttribute("data-xl"))
              .map((e) => e.className || e.localName)
          : [],
        nestedCarriers: opened
          ? [...panelBody().querySelectorAll("[data-xl]")]
              .filter((e) => e.querySelector("[data-xl]"))
              .map((e) => e.className || e.localName)
          : [],
      });
      closePanel();
    }
    paired = sweep.find((s) => s.shared.length > 0 && s.structured);
    const pairs = sweep.reduce((n, s) => n + s.shared.length, 0);
    console.info(
      `[drawerRealPage] ${PAPER_ID}: swept ${sweep.length} annotated entr${sweep.length === 1 ? "y" : "ies"}, ` +
        `${sweep.filter((s) => s.structured).length} structured, ${pairs} two-sided token pairs`,
    );
  }, 300_000);

  afterAll(() => {
    document.body.innerHTML = "";
  });

  it("ships no scrim and opens a structured panel from a real block", () => {
    // The modal scrim is gone from the built markup, not merely unstyled.
    expect(document.getElementById("drawer-scrim")).toBeNull();
    expect(document.querySelector(".drawer-scrim")).toBeNull();

    expect(sweep.length, "built page carries annotated formal blocks").toBeGreaterThan(0);
    expect(sweep.every((s) => s.opened), `entries whose panel never opened: ${sweep.filter((s) => !s.opened).map((s) => s.objId).join(", ")}`).toBe(true);
    // structured rendering actually reached the page (not the <pre> fallback)
    const structured = sweep.filter((s) => s.structured);
    expect(structured.length, "no entry rendered a structured statement").toBeGreaterThan(0);
    expect(document.getElementById("drawer")!.getAttribute("aria-modal")).toBe("false");
  });

  it("has panel carriers whose tokens really occur in that block's prose", () => {
    expect(paired, "no entry has a two-sided crosslink at all").toBeTruthy();
    expect(paired!.shared.length).toBeGreaterThan(0);
  });

  it("bidirectional token coverage: no one-sided crosslink on any entry", () => {
    // THE gate. A token present in the prose but with no Lean carrier (or the
    // reverse) is a pair the reader can only ever see one half of — which is
    // exactly what both production bugs produced.
    const oneSided: string[] = [];
    let compared = 0;
    for (const s of sweep) {
      if (!s.opened) continue;
      compared += s.body.size + s.panel.size;
      for (const t of s.body) if (!s.panel.has(t)) oneSided.push(`${s.objId}: "${t}" prose-only`);
      for (const t of s.panel) if (!s.body.has(t)) oneSided.push(`${s.objId}: "${t}" Lean-only`);
    }
    // A coverage sweep that compares nothing passes trivially, which would turn
    // this gate into decoration the moment enrichment stops emitting tokens.
    expect(sweep.filter((s) => s.opened).length, "entries swept").toBeGreaterThanOrEqual(5);
    expect(compared, "tokens compared").toBeGreaterThanOrEqual(50);
    expect(
      oneSided,
      `${oneSided.length} one-sided crosslink token(s):\n  ${oneSided.slice(0, 40).join("\n  ")}`,
    ).toEqual([]);
  });

  it("hover lights the paper, leave clears it, click pins, Esc closes and unpins", async () => {
    const block = await openObj(paired!.objId);
    const carrier = [...panelBody().querySelectorAll<HTMLElement>("[data-xl]")].find((el) =>
      tokensOf(el).some((t) => paired!.shared.includes(t)),
    )!;
    expect(carrier, "a panel element sharing a token with the prose").toBeTruthy();
    const partners = [...block.querySelectorAll("[data-xl]")].filter((s) =>
      tokensOf(s).some((t) => tokensOf(carrier).includes(t)),
    );
    expect(partners.length).toBeGreaterThan(0);

    over(carrier);
    expect(partners.some(hot), "hovering the Lean side lights the prose").toBe(true);
    out(carrier);
    expect(partners.some(hot)).toBe(false);

    // Clicking pins AND jumps to the counterpart. happy-dom leaves
    // scrollIntoView undefined, so record it on the prototype.
    const scrolled: Element[] = [];
    const elProto = Element.prototype as unknown as Record<string, unknown>;
    const original = elProto.scrollIntoView;
    elProto.scrollIntoView = function (this: Element) {
      scrolled.push(this);
    };
    try {
      click(carrier);
      expect(partners.some(hot), "click pins the highlight").toBe(true);
      // the jump target is a real prose partner of the row that was clicked
      expect(scrolled.length, "pinning jumps to the counterpart").toBe(1);
      expect(partners).toContain(scrolled[0]);
    } finally {
      elProto.scrollIntoView = original;
    }
    closePanel();
    expect(panelOpen()).toBe(false);
    // closing releases the pin — no highlight is left stranded in the paper
    expect(document.querySelectorAll("#paper-body .xl-hot").length).toBe(0);
  }, 30_000);

  it("keeps tokens isolated: hovering one entry never lights another's prose", async () => {
    const block = await openObj(paired!.objId);
    const carrier = [...panelBody().querySelectorAll<HTMLElement>("[data-xl]")].find((el) =>
      tokensOf(el).some((t) => paired!.shared.includes(t)),
    )!;
    over(carrier);

    for (const other of annotatedBlocks()) {
      if (other === block) continue;
      const stray = [...other.querySelectorAll("[data-xl]")].filter(hot);
      expect(
        stray.map((s) => s.getAttribute("data-xl")),
        `tokens leaked from ${paired!.objId} into ${other.dataset.objid}`,
      ).toEqual([]);
    }
    out(carrier);
    closePanel();
  }, 30_000);

  it("Lean→NL works on the reported selector-bracket leaf (carrier is the leaf line)", async () => {
    // The user-reported failure, at its exact location: on
    // thm:overlap-adaptive-universal-hybrid the selector-bracket conclusion is a
    // `.ds-concl` leaf sitting inside a `.ds-sub` that carries the SAME token,
    // and the pointer only ever touches the `.ds-code` box inside the leaf.
    const OBJ = "thm:overlap-adaptive-universal-hybrid";
    const block = blockOf(OBJ);
    expect(block, `built page still has ${OBJ}`).toBeTruthy();
    await openObj(OBJ);

    const leaf = [...panelBody().querySelectorAll<HTMLElement>(".ds-concl[data-xl]")].find((e) =>
      (e.textContent ?? "").includes("selectedEstimator C_epsilon"),
    );
    expect(leaf, "the selector-bracket leaf is rendered").toBeTruthy();
    const tok = tokensOf(leaf!);
    const prose = [...block!.querySelectorAll<HTMLElement>("[data-xl]")].filter((s) =>
      tokensOf(s).some((t) => tok.includes(t)),
    );
    expect(prose.length, "the leaf's token has a prose counterpart").toBeGreaterThan(0);

    // CARRIER GRANULARITY: the leaf's enclosing card/sub is NOT a carrier, so a
    // stray pointer in its padding can no longer fire a broader token.
    const container = leaf!.parentElement?.closest<HTMLElement>(".ds-sub, .ds-card, .ds-lift");
    expect(container, "the leaf really does sit inside a card/sub container").toBeTruthy();
    expect(container!.hasAttribute("data-xl")).toBe(false);

    // 1. pointer over the code box inside the leaf → the prose must light
    const code = leaf!.querySelector<HTMLElement>(".ds-code")!;
    code.dispatchEvent(new Event("mouseover", { bubbles: true }));
    expect(prose.some(hot), "hovering the Lean row lights the NL span").toBe(true);

    // 2. drifting within the leaf is not a leave
    code.dispatchEvent(new MouseEvent("mouseout", { bubbles: true, relatedTarget: leaf }));
    expect(prose.some(hot), "moving inside one carrier keeps it lit").toBe(true);

    // 3. drifting out into the container lights NOTHING rather than a broader
    //    token — precisely the surprise the reader hit
    leaf!.dispatchEvent(new MouseEvent("mouseout", { bubbles: true, relatedTarget: container }));
    container!.dispatchEvent(new Event("mouseover", { bubbles: true }));
    expect(prose.some(hot), "a container must not carry a token of its own").toBe(false);
    expect(panelBody().querySelectorAll(".xl-hot").length).toBe(0);
    closePanel();
  }, 30_000);

  it("emits crosslink tokens only on content lines, never on containers", () => {
    // Swept across every annotated entry: no card/sub/frame carrier anywhere,
    // and no carrier encloses another, so ancestor fallthrough is impossible.
    const bad: string[] = [];
    for (const s of sweep) {
      for (const sel of s.containerCarriers) bad.push(`${s.objId}: container carrier ${sel}`);
      for (const sel of s.nestedCarriers) bad.push(`${s.objId}: nested carrier ${sel}`);
    }
    expect(sweep.some((s) => s.panel.size > 0), "entries with panel carriers").toBe(true);
    expect(bad, `carrier-granularity violations:\n  ${bad.slice(0, 20).join("\n  ")}`).toEqual([]);
  });

  it("a paper span jumps to its statement ROW, never to the card head above it", async () => {
    // Reproduced on thm:sharp-minimax-fixed-interior: prose spans there carry
    // row tokens PLUS a display-segment token (#s8) that also sits on the
    // anchor's cv-head — which is the panel's FIRST carrier in DOM order, so
    // every such click used to scroll to "sharp_minimax_fixed_interior".
    const OBJ = "thm:sharp-minimax-fixed-interior";
    const block = blockOf(OBJ);
    expect(block, `built page still has ${OBJ}`).toBeTruthy();
    await openObj(OBJ);

    const carriers = [...panelBody().querySelectorAll<HTMLElement>("[data-xl]")];
    const heads = carriers.filter((e) => e.matches(".cv-head, summary"));
    expect(heads.length, "the panel has component head carriers").toBeGreaterThan(0);
    // the head really does render before the statement rows
    expect(carriers[0].matches(".cv-head, summary")).toBe(true);

    // a prose span sharing a token with BOTH a head and a statement row
    const headTokens = new Set(heads.flatMap(tokensOf));
    const rowTokens = new Set(
      carriers.filter((e) => e.matches(".ds-row, .ds-concl, .ds-intro")).flatMap(tokensOf),
    );
    const span = [...block!.querySelectorAll<HTMLElement>("[data-xl]")].find(
      (s) => tokensOf(s).some((t) => headTokens.has(t)) && tokensOf(s).some((t) => rowTokens.has(t)),
    );
    expect(span, "a span carrying both a head token and a row token").toBeTruthy();

    // A panel target is centred inside the panel's own scroller, so the page is
    // never scrolled; the landing row is marked with `.xl-jump`.
    const paged: Element[] = [];
    const panned: Element[] = [];
    const elProto = Element.prototype as unknown as Record<string, unknown>;
    const origSIV = elProto.scrollIntoView;
    const origST = elProto.scrollTo;
    elProto.scrollIntoView = function (this: Element) {
      paged.push(this);
    };
    elProto.scrollTo = function (this: Element) {
      panned.push(this);
    };
    try {
      span!.dispatchEvent(new Event("click", { bubbles: true }));
      await flush();
    } finally {
      elProto.scrollIntoView = origSIV;
      elProto.scrollTo = origST;
    }

    const landed = panelBody().querySelector<HTMLElement>(".xl-jump");
    expect(landed, "the click jumps somewhere in the panel").toBeTruthy();
    expect(
      landed!.matches(".ds-row, .ds-concl, .ds-intro"),
      `jumped to ${landed!.className} instead of a statement row`,
    ).toBe(true);
    expect(landed!.matches(".cv-head, summary")).toBe(false);
    // and the row it landed on genuinely shares one of the span's tokens
    expect(tokensOf(landed!).some((t) => tokensOf(span!).includes(t))).toBe(true);
    // centred in the panel body, with the article left where it was
    expect(panned).toEqual([panelBody()]);
    expect(paged, "a panel target must not scroll the page").toEqual([]);
    closePanel();
  }, 30_000);

  it("a paper chip flashes its block and leaves the panel open", async () => {
    const host = sweep.find((s) => s.paperChip);
    expect(host, "built page has a paper-class chip pointing at a real block").toBeTruthy();
    await openObj(host!.objId);
    const chip = panelBody().querySelector<HTMLElement>(
      `.cv-paper-chip[data-paper-obj="${host!.paperChip}"]`,
    )!;
    const target = blockOf(host!.paperChip!)!;
    chip.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();
    expect(target.classList.contains("flash")).toBe(true);
    expect(panelOpen(), "a jump inside the paper must not close a docked panel").toBe(true);
    closePanel();
  }, 30_000);

  it("a display formula gets the highlight hook, and the stylesheet paints it", async () => {
    // happy-dom cannot tell us what a rule LOOKS like, so this asserts the two
    // halves separately: a rule exists that gives the combination a visible
    // treatment, and the class actually lands on the span wrapping display math.
    expect(paperCss).toMatch(/span\[data-xl\]\.xl-hot\s+\.katex-display/);
    expect(paperCss).toMatch(/\.formal-block span\[data-xl\]\.xl-hot/);

    const host = sweep.find((s) => s.displaySpan && s.shared.length > 0);
    expect(host, "built page has an annotated display formula with a Lean carrier").toBeTruthy();
    const block = await openObj(host!.objId);
    const display = [...block.querySelectorAll("[data-xl]")].find(
      (s) => s.querySelector(".katex-display") && tokensOf(s).some((t) => host!.shared.includes(t)),
    );
    expect(display, "a display span whose token has a Lean carrier").toBeTruthy();
    const carrier = [...panelBody().querySelectorAll<HTMLElement>("[data-xl]")].find((el) =>
      tokensOf(el).some((t) => tokensOf(display!).includes(t)),
    )!;
    over(carrier);
    expect(hot(display!), "display-formula span takes the highlight class").toBe(true);
    out(carrier);
    closePanel();
  }, 30_000);
});
