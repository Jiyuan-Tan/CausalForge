// @vitest-environment happy-dom
//
// The Proof map controller against a page shaped like the one Astro ships: the
// side rail (contents + map) as a sibling of the paper, and a paper body with
// `data-objid` formal blocks. The rail markup here is BUILT from the same
// `buildProofGraph` output the component uses, and the ids/classes it relies on
// are asserted against the component source, so the two cannot drift apart
// silently.

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { buildProofGraph, parsePaperGraph, type PaperGraph } from "../src/lib/proofGraph.js";
import { proofMapMarks } from "../src/lib/proofMapSvg.js";
import { initProofMap } from "../src/scripts/proofMap.js";

const COMPONENT = readFileSync(
  resolve(import.meta.dirname, "..", "src", "components", "ProofMap.astro"),
  "utf8",
);
/** The chips and edges themselves come from one generator, shared by the
 *  build-time render and the client's re-wrap. */
const SVG_GEN = readFileSync(
  resolve(import.meta.dirname, "..", "src", "lib", "proofMapSvg.ts"),
  "utf8",
);

const GRAPH: PaperGraph = parsePaperGraph({
  commit: "demo",
  nodes: [
    { obj_id: "thm:main", env: "theoremv", paper_label: "Theorem 1", title: "Main result" },
    { obj_id: "lem:mid", env: "lemmav", paper_label: "Lemma 2", title: "Middle step" },
    { obj_id: "lem:base", env: "lemmav", paper_label: "Lemma 1", title: "Base step" },
  ],
  edges: [
    { from: "thm:main", to: "lem:mid", kind: "proof-cites" },
    { from: "lem:mid", to: "lem:base", kind: "proof-cites" },
  ],
})!;

const PAPER_ID = "demo_paper_v1";
const WORKER = "https://worker.example.workers.dev";

/** Reproduces what ProofMap.astro emits for the given graph. */
function railMarkup(worker: string): string {
  const layout = buildProofGraph(GRAPH);
  const data = {
    paperId: PAPER_ID,
    worker,
    builtWidth: layout.width,
    graph: GRAPH,
    nodes: layout.nodes.map((n) => ({
      id: n.id,
      label: n.label,
      title: n.title,
      top: n.top,
      cites: n.cites,
      citedBy: n.citedBy,
    })),
  };
  return `
    <div class="paper-side" id="paper-side">
      <nav class="paper-toc" id="paper-toc"><div class="toc-head">Contents</div>
        <ul><li class="toc-l1"><a href="#introduction">Introduction</a></li></ul>
      </nav>
      <section class="pm-panel" id="proof-map">
        <h2 class="pm-head" id="pm-panel-title">
          <button class="pm-toggle" id="pm-toggle" type="button" aria-expanded="true" aria-controls="pm-body">
            <span class="pm-kicker">Proof map</span><span class="pm-sub">3 statements · 2 edges</span>
          </button>
          <span class="pm-coverage" id="pm-coverage" hidden>
            <span class="pm-meter"><span id="pm-coverage-bar"></span></span><span id="pm-coverage-txt"></span>
          </span>
        </h2>
        <div class="pm-body" id="pm-body">
          <div class="pm-graph-scroll" id="pm-graph-scroll">
            <svg class="pm-map" id="pm-map" viewBox="0 0 ${layout.width} ${layout.height}" width="${layout.width}" height="${layout.height}"><defs></defs><g id="pm-marks">${proofMapMarks(layout)}</g></svg>
          </div>
          <p class="pm-legend"></p>
          <div class="pm-preview" id="pm-card" role="region" aria-live="polite" hidden>
            <div class="pm-card-head">
              <p class="pm-card-kicker" id="pm-card-label"></p>
              <button class="pm-card-close" id="pm-card-close" type="button" aria-label="Clear preview">✕</button>
            </div>
            <h3 class="pm-card-title" id="pm-card-title"></h3>
            <div class="pm-stmt" id="pm-stmt"></div>
            <p class="pm-stmt-note"><button class="pm-goto" id="pm-goto" type="button">Go to…</button></p>
            <div class="pm-rel"><p class="pm-rel-label">Its proof invokes</p><div class="pm-chips" id="pm-cites"></div></div>
            <div class="pm-rel"><p class="pm-rel-label">Invoked by the proofs of</p><div class="pm-chips" id="pm-citedby"></div></div>
            <div class="pm-attest" id="pm-attest" hidden>
              <div class="pm-readers" id="pm-readers"></div>
              <button class="pm-verify" id="pm-verify" type="button"></button>
              <p class="pm-status" id="pm-attest-status"></p>
            </div>
          </div>
        </div>
      </section>
    </div>
    <script type="application/json" id="proof-map-data">${JSON.stringify(data)}</script>`;
}

const PAPER = `
  <article class="paper">
    <div id="paper-body">
      <div class="abstract"><p>Abstract.</p></div>
      <h1 id="introduction">Introduction</h1>
      <div class="formal-block kind-theorem" id="obj-thm:main" data-objid="thm:main" tabindex="0">
        <span class="env-label">Theorem 1 (Main result).</span><p>The risk is sharp.</p>
      </div>
      <div class="formal-block kind-lemma" id="obj-lem:mid" data-objid="lem:mid" tabindex="0">
        <span class="env-label">Lemma 2 (Middle step).</span><p>A middle inequality.</p>
      </div>
      <div class="formal-block kind-lemma" id="obj-lem:base" data-objid="lem:base" tabindex="0">
        <span class="env-label">Lemma 1 (Base step).</span><p>A base inequality.</p>
      </div>
    </div>
  </article>`;

/** Mount the page. `wide` decides whether the rail exists (matchMedia). */
function mount(worker = "", wide = true): void {
  vi.stubGlobal("matchMedia", (q: string) => ({
    matches: q.includes("min-width") ? wide : false,
    media: q,
    addEventListener() {},
    removeEventListener() {},
  }));
  document.body.innerHTML = railMarkup(worker) + PAPER;
}

const node = (id: string) => document.querySelector<SVGAElement>(`a.pm-node[data-pm-node="${id}"]`)!;
const $ = (id: string) => document.getElementById(id)!;
const click = (el: Element, detail = 1) =>
  el.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true, detail }));
/** mouseenter/mouseleave do not bubble; the controller binds them per chip. */
const hover = (el: Element) => el.dispatchEvent(new MouseEvent("mouseenter"));
const unhover = (el: Element) => el.dispatchEvent(new MouseEvent("mouseleave"));
const dblclick = (el: Element) =>
  el.dispatchEvent(new MouseEvent("dblclick", { bubbles: true, cancelable: true }));
const focusChip = (el: Element) => el.dispatchEvent(new FocusEvent("focus"));
const blurChip = (el: Element) => el.dispatchEvent(new FocusEvent("blur"));
const key = (el: Element, k: string) =>
  el.dispatchEvent(new KeyboardEvent("keydown", { key: k, bubbles: true, cancelable: true }));
/** Which edges are lit, as a compact fingerprint. */
const lit = () => ({
  cites: [...document.querySelectorAll(".pm-edge.is-cites")].map((p) => p.getAttribute("data-to")),
  citedBy: [...document.querySelectorAll(".pm-edge.is-citedby")].map((p) => p.getAttribute("data-from")),
  dim: document.querySelectorAll(".pm-edge.is-dim").length,
});

let scrolled: string[] = [];

beforeEach(() => {
  scrolled = [];
  Element.prototype.scrollIntoView = function (this: Element) {
    scrolled.push(this.getAttribute("data-objid") ?? this.id ?? "");
  } as typeof Element.prototype.scrollIntoView;
  sessionStorage.clear();
});

afterEach(() => {
  vi.unstubAllGlobals();
  vi.useRealTimers();
});

describe("panel markup contract", () => {
  it("the component still emits every hook the controller queries", () => {
    for (const id of [
      "proof-map",
      "pm-toggle",
      "pm-body",
      "pm-map",
      "pm-card",
      "pm-card-close",
      "pm-card-label",
      "pm-card-title",
      "pm-stmt",
      "pm-goto",
      "pm-cites",
      "pm-citedby",
      "pm-attest",
      "pm-readers",
      "pm-verify",
      "pm-attest-status",
      "pm-coverage",
      "pm-coverage-bar",
      "pm-coverage-txt",
      "proof-map-data",
    ]) {
      expect(COMPONENT, `component must keep #${id}`).toContain(`"${id}"`);
    }
    // Marks are generated, not hand-written, so the component only has to hand
    // the group over — and the client re-wrap emits exactly the same shapes.
    expect(COMPONENT).toContain("proofMapMarks(layout)");
    expect(COMPONENT).toContain('id="pm-marks"');
    expect(COMPONENT).toContain("pm-arr-cites");
    expect(COMPONENT).toContain("pm-arr-citedby");
    // …and the payload carries what a re-wrap needs.
    expect(COMPONENT).toContain("builtWidth: layout.width");
    expect(COMPONENT).toContain("graph,");
    expect(SVG_GEN).toContain("data-pm-node");
    expect(SVG_GEN).toContain('href="#obj-');
    // Reader-facing vocabulary is the "invoke" family; the wire contract and the
    // code identifiers keep saying "cites".
    expect(COMPONENT).toContain("Its proof invokes");
    expect(COMPONENT).toContain("Invoked by the proofs of");
    expect(COMPONENT).toContain("its proof invokes");
    expect(COMPONENT).toContain("invoked by");
    expect(COMPONENT).toContain("taking the results the proof invokes as given");
    expect(COMPONENT).not.toContain("Its proof cites");
    expect(COMPONENT).not.toContain("Cited by");
    // Chips are real links, which is the whole JS-off story — now emitted by
    // the shared generator rather than by the template.
    expect(SVG_GEN).toContain("href=\"#obj-");
  });
});

describe("proof map in the rail — read-only (no worker configured)", () => {
  beforeEach(() => {
    vi.stubGlobal("fetch", vi.fn());
    mount("");
    initProofMap();
  });

  it("shows the map with no selection and no strip until the reader asks", () => {
    expect($("pm-card").hidden).toBe(true);
    expect($("pm-body").hidden).toBe(false);
    expect(lit()).toEqual({ cites: [], citedBy: [], dim: 0 });
  });

  // The preview cannot overlap the paper because it is not a floating layer at
  // all: it is a block inside the rail panel, under the map.
  it("keeps the preview inside the rail, never over the paper", () => {
    expect($("pm-card").closest("#proof-map")).not.toBeNull();
    expect($("pm-card").closest("article.paper")).toBeNull();
    expect($("paper-body").querySelector(".pm-panel")).toBeNull();
    expect($("paper-body").querySelector("#pm-map")).toBeNull();
  });

  // v4: edges are cheap, so hover lights them. The STRIP is what must not move,
  // because rebuilding it under a passing cursor is what felt like churn.
  it("hover lights the edges and leaves the strip alone", () => {
    hover(node("lem:mid"));
    expect(lit()).toEqual({ cites: ["lem:base"], citedBy: ["thm:main"], dim: 0 });
    expect($("pm-card").hidden).toBe(true); // no strip on hover
    expect(scrolled).toEqual([]); // and nothing moves
    unhover(node("lem:mid"));
    expect(lit()).toEqual({ cites: [], citedBy: [], dim: 0 }); // back to neutral
    expect($("pm-card").hidden).toBe(true);
  });

  it("a single click selects: edges light, strip fills, page holds still", () => {
    click(node("lem:mid"));
    expect(lit()).toEqual({ cites: ["lem:base"], citedBy: ["thm:main"], dim: 0 });
    expect(node("lem:mid").classList.contains("is-selected")).toBe(true);
    expect($("pm-card").hidden).toBe(false);
    expect($("pm-card-label").textContent).toBe("Lemma 2");
    expect($("pm-card-title").textContent).toBe("Middle step");
    expect($("pm-stmt").textContent).toContain("A middle inequality.");
    expect($("pm-stmt").querySelector("[data-objid]")).toBeNull();
    expect(scrolled).toEqual([]); // no jump on a single click
  });

  it("hovering elsewhere previews those edges; the pin takes them back on mouse-out", () => {
    click(node("lem:base"));
    const pinned = lit();
    hover(node("thm:main"));
    expect(lit()).toEqual({ cites: ["lem:mid"], citedBy: [], dim: 1 }); // hover wins
    expect($("pm-card-label").textContent).toBe("Lemma 1"); // …but the strip does not follow
    expect(node("lem:base").classList.contains("is-selected")).toBe(true);
    expect(node("lem:base").classList.contains("is-dim")).toBe(false); // the pin is never dimmed
    unhover(node("thm:main"));
    expect(lit()).toEqual(pinned);
  });

  it("dims the results that are not neighbours", () => {
    click(node("thm:main"));
    expect(node("lem:base").classList.contains("is-dim")).toBe(true);
    expect(node("lem:mid").classList.contains("is-dim")).toBe(false);
  });

  it("a selection holds until another chip is chosen", () => {
    click(node("lem:mid"));
    click(node("lem:base"));
    expect(node("lem:base").classList.contains("is-selected")).toBe(true);
    expect(node("lem:mid").classList.contains("is-selected")).toBe(false);
    expect($("pm-card-label").textContent).toBe("Lemma 1");
  });

  it("a double click jumps, flashes, and leaves Back working", () => {
    vi.useFakeTimers();
    const push = vi.spyOn(history, "pushState");
    click(node("lem:base"));
    dblclick(node("lem:base"));
    const block = document.querySelector('.formal-block[data-objid="lem:base"]')!;
    expect(scrolled).toEqual(["lem:base"]);
    expect(block.classList.contains("flash")).toBe(true);
    // A jump is a link-follow: it goes on the history stack.
    expect(push).toHaveBeenCalledWith(null, "", "#obj-lem:base");
    vi.advanceTimersByTime(2000);
    expect(block.classList.contains("flash")).toBe(false);
    expect(node("lem:base").classList.contains("is-selected")).toBe(true);
    push.mockRestore();
  });

  it("suppresses the anchor default on a single click and on the double", () => {
    expect(node("lem:mid").getAttribute("href")).toBe("#obj-lem:mid");
    const single = new MouseEvent("click", { bubbles: true, cancelable: true });
    node("lem:mid").dispatchEvent(single);
    expect(single.defaultPrevented).toBe(true);
    const dbl = new MouseEvent("dblclick", { bubbles: true, cancelable: true });
    node("lem:mid").dispatchEvent(dbl);
    expect(dbl.defaultPrevented).toBe(true);
    expect(scrolled).toEqual(["lem:mid"]); // …because we navigated ourselves
  });

  it("Escape, ✕, and a click outside the map all clear the selection", () => {
    click(node("lem:mid"));
    document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
    expect($("pm-card").hidden).toBe(true);
    expect(lit()).toEqual({ cites: [], citedBy: [], dim: 0 });

    click(node("lem:mid"));
    click($("pm-card-close"));
    expect($("pm-card").hidden).toBe(true);

    click(node("lem:mid"));
    $("paper-body").dispatchEvent(new MouseEvent("mousedown", { bubbles: true }));
    expect($("pm-card").hidden).toBe(true);
    expect(document.querySelector("a.pm-node.is-selected")).toBeNull();

    // …but a click inside the panel (the strip's own controls) does not.
    click(node("lem:mid"));
    $("pm-card-title").dispatchEvent(new MouseEvent("mousedown", { bubbles: true }));
    expect($("pm-card").hidden).toBe(false);
  });

  // The reported "clicking L15 jumps to Lemma 16": every hop must resolve by
  // obj_id, never by position, and the chip's label must match the block's own.
  it("maps every chip to its OWN block, by obj_id", () => {
    for (const id of ["thm:main", "lem:mid", "lem:base"]) {
      scrolled = [];
      const a = node(id);
      dblclick(a);
      expect(scrolled).toEqual([id]);
      const flashed = document.querySelector(".formal-block.flash")!;
      expect(flashed.getAttribute("data-objid")).toBe(id);
      const chipLabel = a.querySelector("text")!.textContent!;
      const heading = flashed.querySelector(".env-label")!.textContent!;
      expect(heading.startsWith(chipLabel[0] === "T" ? "Theorem" : "Lemma")).toBe(true);
      expect(heading).toContain(chipLabel.slice(1));
      for (const b of Array.from(document.querySelectorAll(".formal-block"))) b.classList.remove("flash");
    }
  });

  // A touch device fires no hover and no dblclick worth relying on: a tap
  // selects, and the strip's own link is the jump. Never cardless AND jumpless.
  it("a tap selects, and the strip's link is the discoverable jump", () => {
    click(node("lem:mid"));
    expect($("pm-card").hidden).toBe(false);
    expect($("pm-card-label").textContent).toBe("Lemma 2");
    expect(scrolled).toEqual([]);
    click($("pm-goto"));
    expect(scrolled).toEqual(["lem:mid"]);
  });

  it("citation chips in the strip select without moving the paper", () => {
    click(node("thm:main"));
    const chip = $("pm-cites").querySelector("button")!;
    expect(chip.textContent).toBe("Lemma 2");
    click(chip);
    expect($("pm-card-label").textContent).toBe("Lemma 2");
    expect(node("lem:mid").classList.contains("is-selected")).toBe(true);
    expect(scrolled).toEqual([]);
  });

  it("says so when a result stands at the bottom or the top of the structure", () => {
    click(node("lem:base"));
    expect($("pm-cites").textContent).toContain("nothing in this paper");
    expect($("pm-citedby").querySelector("button")!.textContent).toBe("Lemma 2");
  });

  it("collapses and reopens from the panel header", () => {
    expect($("pm-toggle").getAttribute("aria-expanded")).toBe("true");
    click($("pm-toggle"));
    expect($("pm-body").hidden).toBe(true);
    expect($("proof-map").classList.contains("is-collapsed")).toBe(true);
    click($("pm-toggle"));
    expect($("pm-body").hidden).toBe(false);
  });
});

describe("proof map — keyboard", () => {
  beforeEach(() => {
    vi.stubGlobal("fetch", vi.fn());
    mount("");
    initProofMap();
  });

  const tabStop = () =>
    [...document.querySelectorAll("a.pm-node")].find((a) => a.getAttribute("tabindex") === "0")!;

  it("is one tab stop, not one per chip", () => {
    expect(
      [...document.querySelectorAll("a.pm-node")].filter((a) => a.getAttribute("tabindex") === "0"),
    ).toHaveLength(1);
    expect(document.querySelectorAll("a.pm-node")).toHaveLength(3);
  });

  it("arrow keys walk the map, lighting edges but never filling the strip", () => {
    const first = node("thm:main");
    focusChip(first);
    // Focus is the keyboard's hover: edges light, strip stays shut.
    expect(lit()).toEqual({ cites: ["lem:mid"], citedBy: [], dim: 1 });
    expect($("pm-card").hidden).toBe(true);
    key(first, "ArrowRight");
    expect(tabStop()).not.toBe(first);
    expect($("pm-card").hidden).toBe(true); // walking is not choosing
    key(tabStop(), "Home");
    expect(tabStop()).toBe(first);
  });

  // Enter selects; Enter again on the SAME chip jumps — the keyboard spelling
  // of click, then double-click.
  it("Enter selects, and Enter again on the selected chip jumps", () => {
    const a = node("lem:mid");
    focusChip(a);
    const first = new KeyboardEvent("keydown", { key: "Enter", bubbles: true, cancelable: true });
    a.dispatchEvent(first);
    expect(first.defaultPrevented).toBe(true); // the link's own activation is taken over
    expect($("pm-card-label").textContent).toBe("Lemma 2");
    expect(scrolled).toEqual([]);

    key(a, "Enter");
    expect(scrolled).toEqual(["lem:mid"]);
  });

  it("Space behaves as Enter does", () => {
    const a = node("lem:base");
    focusChip(a);
    key(a, " ");
    expect($("pm-card-label").textContent).toBe("Lemma 1");
    expect(scrolled).toEqual([]);
    key(a, " ");
    expect(scrolled).toEqual(["lem:base"]);
  });

  it("Escape clears the selection, and the focused chip keeps only its hover light", () => {
    const a = node("lem:mid");
    focusChip(a);
    key(a, "Enter");
    document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
    expect($("pm-card").hidden).toBe(true);
    expect(document.querySelector("a.pm-node.is-selected")).toBeNull();
    // Focus is the keyboard's cursor: it is still on the chip, so its edges stay
    // lit exactly as a hovering mouse would leave them.
    expect(lit()).toEqual({ cites: ["lem:base"], citedBy: ["thm:main"], dim: 0 });
    blurChip(a);
    expect(lit()).toEqual({ cites: [], citedBy: [], dim: 0 });
  });
});

describe("proof map — fitting the rail's real width", () => {
  /** happy-dom has no layout, so state the width the rail would have got. */
  const widen = (px: number) =>
    Object.defineProperty($("pm-graph-scroll"), "clientWidth", {
      value: px,
      configurable: true,
    });
  const settle = () => new Promise((r) => setTimeout(r, 0));
  const svgWidth = () => Number($("pm-map").getAttribute("viewBox")!.split(" ")[2]);
  const lineCount = () => {
    const ys = [...document.querySelectorAll("a.pm-node rect")].map((r) => r.getAttribute("y"));
    return new Set(ys).size;
  };

  beforeEach(() => vi.stubGlobal("fetch", vi.fn()));

  it("re-wraps the map into a wider rail, with fewer lines", async () => {
    mount("");
    const builtWidth = svgWidth();
    const builtLines = lineCount();
    widen(340);
    initProofMap();
    await settle();
    expect(svgWidth()).toBeGreaterThan(builtWidth);
    expect(svgWidth()).toBeLessThanOrEqual(340);
    expect(lineCount()).toBeLessThanOrEqual(builtLines);
    expect(document.querySelectorAll("a.pm-node")).toHaveLength(3); // nothing lost
  });

  it("keeps the re-wrapped chips fully wired", async () => {
    mount("");
    widen(340);
    initProofMap();
    await settle();
    click(node("lem:mid"));
    expect($("pm-card-label").textContent).toBe("Lemma 2");
    expect(lit()).toEqual({ cites: ["lem:base"], citedBy: ["thm:main"], dim: 0 });
    dblclick(node("lem:mid"));
    expect(scrolled).toEqual(["lem:mid"]);
    expect(
      [...document.querySelectorAll("a.pm-node")].filter((a) => a.getAttribute("tabindex") === "0"),
    ).toHaveLength(1); // roving tabindex survived the rebuild
  });

  it("re-wraps again when the window is resized", async () => {
    mount("");
    widen(230);
    initProofMap();
    await settle();
    const before = svgWidth();
    widen(400);
    window.dispatchEvent(new Event("resize"));
    await new Promise((r) => setTimeout(r, 250));
    expect(svgWidth()).toBeGreaterThan(before);
  });

  it("ignores a difference too small to change a line", async () => {
    mount("");
    widen(232);
    initProofMap();
    await settle();
    expect(svgWidth()).toBe(226); // the built layout stands
  });

  // Below the rail breakpoint the panel is IN the page's flow: re-wrapping it
  // would change its height and move the paper column, which readers' scroll
  // positions and the margin-comment anchors are pinned to.
  it("never re-wraps on a narrow viewport, so the paper column cannot move", async () => {
    mount("", false);
    widen(600);
    initProofMap();
    await settle();
    expect(svgWidth()).toBe(226);
  });
});

describe("proof map on a narrow viewport", () => {
  it("starts collapsed, because there is no rail to dock to", () => {
    vi.stubGlobal("fetch", vi.fn());
    mount("", false);
    initProofMap();
    expect($("pm-body").hidden).toBe(true);
    expect($("proof-map").classList.contains("is-collapsed")).toBe(true);
    click($("pm-toggle"));
    expect($("pm-body").hidden).toBe(false); // still fully usable once opened
  });
});

describe("proof map — reader verification", () => {
  const marks = [
    { objId: "lem:mid", login: "saskia-v", avatarUrl: null, at: "2026-08-20T10:00:00Z" },
    { objId: "lem:mid", login: "m-oberst", avatarUrl: null, at: "2026-08-21T10:00:00Z" },
  ];

  /** Worker + GitHub stub. `calls` records every request for assertions. */
  function stubNetwork(opts: { token?: string; list?: unknown } = {}) {
    const calls: { url: string; method: string; body: unknown }[] = [];
    vi.stubGlobal(
      "fetch",
      vi.fn(async (input: string, init?: RequestInit) => {
        const url = String(input);
        const method = init?.method ?? "GET";
        calls.push({ url, method, body: init?.body ? JSON.parse(String(init.body)) : null });
        if (url.startsWith("https://api.github.com/user")) {
          return new Response(JSON.stringify({ login: "jiyuan-tan", avatar_url: "" }), { status: 200 });
        }
        if (url.includes("/api/attestations") && method === "GET") {
          return new Response(JSON.stringify({ paper: PAPER_ID, attestations: opts.list ?? marks }), {
            status: 200,
          });
        }
        if (url.includes("/api/attestations") && method === "POST") {
          return new Response(
            JSON.stringify({ ok: true, login: "jiyuan-tan", avatarUrl: null, at: "now" }),
            { status: 200 },
          );
        }
        if (url.includes("/api/attestations") && method === "DELETE") {
          return new Response(JSON.stringify({ ok: true }), { status: 200 });
        }
        return new Response("{}", { status: 404 });
      }),
    );
    if (opts.token) sessionStorage.setItem("cs-gh-token", opts.token);
    return calls;
  }

  it("marks verified chips, meters coverage, and prompts an anonymous reader to sign in", async () => {
    stubNetwork();
    mount(WORKER);
    initProofMap();
    await vi.waitFor(() => expect($("pm-coverage").hidden).toBe(false));
    expect($("pm-coverage-txt").textContent).toBe("1/3 ✓");
    expect(node("lem:mid").classList.contains("is-attested")).toBe(true);
    expect(node("thm:main").classList.contains("is-attested")).toBe(false);
    click(node("lem:mid"));
    expect($("pm-readers").textContent).toContain("verified by 2 readers");
    expect(($("pm-verify") as HTMLButtonElement).textContent).toBe("Sign in with GitHub to verify");
  });

  it("records and then withdraws the signed-in reader's own attestation", async () => {
    const calls = stubNetwork({ token: "gh-token" });
    mount(WORKER);
    initProofMap();
    await vi.waitFor(() => expect($("pm-coverage").hidden).toBe(false));
    click(node("thm:main"));
    expect(($("pm-verify") as HTMLButtonElement).textContent).toBe("I verified this statement & proof");

    click($("pm-verify"));
    await vi.waitFor(() => expect($("pm-attest-status").textContent).toBe("Recorded — thank you."));
    expect(calls.find((c) => c.method === "POST")!.body).toEqual({
      paper: PAPER_ID,
      objId: "thm:main",
    });
    expect(node("thm:main").classList.contains("is-attested")).toBe(true);
    expect($("pm-coverage-txt").textContent).toBe("2/3 ✓");
    expect(($("pm-verify") as HTMLButtonElement).textContent).toBe("✓ You verified this — withdraw");

    click($("pm-verify"));
    await vi.waitFor(() => expect($("pm-attest-status").textContent).toBe("Withdrawn."));
    expect(calls.find((c) => c.method === "DELETE")!.body).toEqual({
      paper: PAPER_ID,
      objId: "thm:main",
    });
    expect(node("thm:main").classList.contains("is-attested")).toBe(false);
    expect($("pm-coverage-txt").textContent).toBe("1/3 ✓");
  });

  it("surfaces a refused write without losing the map", async () => {
    sessionStorage.setItem("cs-gh-token", "gh-token");
    vi.stubGlobal(
      "fetch",
      vi.fn(async (input: string, init?: RequestInit) => {
        const url = String(input);
        if (url.startsWith("https://api.github.com/user")) {
          return new Response(JSON.stringify({ login: "jiyuan-tan" }), { status: 200 });
        }
        if ((init?.method ?? "GET") === "GET") {
          return new Response(JSON.stringify({ attestations: [] }), { status: 200 });
        }
        return new Response(JSON.stringify({ error: "not permitted" }), { status: 403 });
      }),
    );
    mount(WORKER);
    initProofMap();
    await vi.waitFor(() => expect($("pm-coverage").hidden).toBe(false));
    click(node("thm:main"));
    click($("pm-verify"));
    await vi.waitFor(() =>
      expect($("pm-attest-status").textContent).toBe("Could not save that (not permitted)."),
    );
    expect($("pm-card").hidden).toBe(false);
  });

  it("degrades to the plain map when the worker is unreachable", async () => {
    vi.stubGlobal("fetch", vi.fn(async () => { throw new Error("network down"); }));
    mount(WORKER);
    initProofMap();
    await vi.waitFor(() => expect(fetch).toHaveBeenCalled());
    click(node("thm:main"));
    expect($("pm-card").hidden).toBe(false);
    expect($("pm-card-label").textContent).toBe("Theorem 1");
    expect(document.querySelector("a.pm-node.is-attested")).toBeNull();
  });

  it("ignores a payload that is not a list of attestations", async () => {
    stubNetwork({ list: { nope: true } });
    mount(WORKER);
    initProofMap();
    await vi.waitFor(() => expect($("pm-coverage").hidden).toBe(false));
    expect($("pm-coverage-txt").textContent).toBe("0/3 ✓");
  });
});

describe("proof map — refuses to boot without its data", () => {
  it("does nothing when the page carries no panel", () => {
    document.body.innerHTML = "<div id='paper-body'><p>Just a paper.</p></div>";
    expect(() => initProofMap()).not.toThrow();
  });

  it("does nothing when the data script is malformed", () => {
    mount("");
    $("proof-map-data").textContent = "{not json";
    expect(() => initProofMap()).not.toThrow();
  });
});
