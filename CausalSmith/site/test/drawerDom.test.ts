// @vitest-environment happy-dom
//
// The paper page's DOCKED, non-modal Lean panel. Two things are under test:
// the chrome (no scrim, panel stays open while the reader keeps using the
// paper, Esc returns focus) and the structured statement rendering — which is
// driven by OPTIONAL payload fields, so the legacy shape must still render
// exactly the plain <pre> statement it always did.

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { initDrawer } from "../src/scripts/drawer.js";

/** The panel chrome the astro page ships — note: no scrim element. */
const PANEL = `
  <aside class="drawer" id="drawer" aria-hidden="true" aria-label="Lean statement">
    <div class="drawer-head">
      <button class="close" id="drawer-close" aria-label="Close">✕</button>
      <span class="drawer-title" id="drawer-title"></span>
      <span id="drawer-sub"></span>
    </div>
    <div class="drawer-body" id="drawer-body"></div>
  </aside>`;

const BASE = {
  github: "org/repo",
  commit: "abcdef1234567",
  ref: "abcdef1234567",
  leanSubdir: "Lean",
  leanPage: null,
  leanAnchors: {},
};

const entry = (over: Record<string, unknown>) => ({
  obj_id: "T1",
  env: "theoremv",
  paper_label: "Theorem 1",
  title: null,
  lean: { file: "A.lean", decl: "thm_one", decl_kind: "theorem", line: 12 },
  fallback: null,
  uses: [],
  ...over,
});

const snippet = (over: Record<string, unknown>) => ({
  decl: "thm_one",
  file: "A.lean",
  line: 12,
  statement: "theorem thm_one (h : P) : Q := by\n  exact foo h",
  sorry_free: true,
  axioms: [],
  ...over,
});

/** Mount the paper body + panel + inline (fetch-free) payload, then wire it. */
function mount(paperData: unknown, bodyHtml: string): void {
  document.body.innerHTML = `<article class="paper"><div id="paper-body">${bodyHtml}</div></article>${PANEL}`;
  const s = document.createElement("script");
  s.type = "application/json";
  s.id = "paper-data";
  s.textContent = JSON.stringify(paperData);
  document.body.appendChild(s);
  initDrawer();
}

/** What a real pointer produces: mouseover/mouseout BUBBLE from the deepest
 *  element under the cursor — which is a CHILD of the annotated carrier, not the
 *  carrier itself — and a mouseout always names where the pointer went. Firing
 *  `mouseenter` straight at the carrier models an event flow browsers never
 *  generate, which is exactly how the Lean-side bug got past this suite. */
const over = (el: Element) => el.dispatchEvent(new Event("mouseover", { bubbles: true }));
const out = (el: Element, to: Element | null = null) =>
  el.dispatchEvent(new MouseEvent("mouseout", { bubbles: true, relatedTarget: to }));
/** Move the pointer from `from` to `to`, as a browser would: out, then over. */
const moveTo = (from: Element, to: Element) => {
  out(from, to);
  over(to);
};

const bodyEl = () => document.getElementById("drawer-body") as HTMLElement;
const drawerEl = () => document.getElementById("drawer") as HTMLElement;
const isOpen = () => document.body.classList.contains("drawer-visible");

/** open() is async (payload load) and repaints once the library name map lands. */
async function flush(): Promise<void> {
  for (let i = 0; i < 6; i++) await new Promise((r) => setTimeout(r, 0));
}

async function openBlock(objId: string): Promise<HTMLElement> {
  const block = document.querySelector(`[data-objid="${objId}"]`) as HTMLElement;
  block.dispatchEvent(new Event("click", { bubbles: true }));
  await flush();
  return block;
}

beforeEach(() => {
  // Only the library name map is fetched (the payload is inlined above). It
  // carries one distinctive entry so the external-card explorer link can
  // resolve; `libNames` is module-level and memoised on first use, so the same
  // map has to be served from the very first test.
  vi.stubGlobal(
    "fetch",
    vi.fn(async () => ({
      ok: true,
      json: async () => ({
        names: { "Causalean.Stat.MinimaxRate": { a: "Stat/Rate", n: "Causalean.Stat.MinimaxRate" } },
      }),
    })),
  );
  document.body.innerHTML = "";
});

describe("legacy payload (no structured / componentViews)", () => {
  const legacy = {
    ...BASE,
    entries: [entry({ uses: ["L1"] }), entry({ obj_id: "L1", paper_label: "Lemma 1", env: "lemmav", lean: null, fallback: "an aux fact" })],
    snippets: { T1: snippet({}) },
  };

  it("renders the plain <pre> statement, with no scrim anywhere in the page", async () => {
    mount(legacy, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    // The modal scrim is gone from the markup entirely — and its absence must
    // not stop the panel from wiring up.
    expect(document.getElementById("drawer-scrim")).toBeNull();
    expect(document.querySelector(".drawer-scrim")).toBeNull();

    await openBlock("T1");
    expect(isOpen()).toBe(true);
    const pre = bodyEl().querySelector("pre");
    expect(pre).not.toBeNull();
    expect(pre!.textContent).toContain("theorem thm_one (h : P) : Q");
    expect(pre!.textContent).toContain("exact foo h");
    // …and none of the structured chrome appears.
    expect(bodyEl().querySelector(".ds-structured")).toBeNull();
    expect(bodyEl().querySelector(".cv-card")).toBeNull();
    // Existing plumbing survives: status badge, GitHub link, uses jump list.
    expect(bodyEl().querySelector(".badge-ok")).not.toBeNull();
    expect(bodyEl().innerHTML).toContain("github.com/org/repo/blob/");
    expect(bodyEl().querySelector("a[data-jump]")?.textContent).toBe("Lemma 1 (L1)");
  });

  it("is a NON-modal dialog: aria-modal false and the paper stays live", async () => {
    mount(legacy, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(drawerEl().getAttribute("role")).toBe("dialog");
    expect(drawerEl().getAttribute("aria-modal")).toBe("false");
    expect(drawerEl().getAttribute("aria-hidden")).toBe("false");
  });

  it("a uses-list jump scrolls + flashes WITHOUT closing the panel", async () => {
    mount(
      legacy,
      `<div class="formal-block" data-objid="T1">Theorem 1.</div>
       <div class="formal-block" data-objid="L1">Lemma 1.</div>`,
    );
    await openBlock("T1");
    const jump = bodyEl().querySelector("a[data-jump]") as HTMLElement;
    jump.dispatchEvent(new Event("click", { bubbles: true }));
    expect(document.querySelector('[data-objid="L1"]')!.classList.contains("flash")).toBe(true);
    // Deliberate change from the modal drawer: the panel is docked, so jumping
    // keeps the statement on screen next to the block it points at.
    expect(isOpen()).toBe(true);
  });
});

describe("structured statement", () => {
  it("renders a Hypotheses block, chips, and one card per conclusion", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [
              { chip: "hyp", code: "hP : P x" },
              { chip: "decl", code: "n : ℕ" },
            ],
            conclusions: [
              { hyps: [{ chip: "hyp", code: "hx : 0 < x" }], code: "Q x" },
              { hyps: [], code: "R x\n  ∧ S x" },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    const labels = [...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent);
    expect(labels).toEqual(["Hypotheses", "Conclusion 1", "Conclusion 2"]);
    // Deliberately "Conclusion", never "Clause".
    expect(bodyEl().textContent).not.toContain("Clause");

    const shared = bodyEl().querySelector(".ds-sect")!;
    const chips = [...shared.querySelectorAll(".ds-chip")].map((c) => c.textContent);
    expect(chips).toEqual(["hyp", "decl"]);
    expect(shared.querySelector(".ds-row-hyp .ds-code")!.textContent).toBe("hP : P x");
    expect(shared.querySelectorAll(".ds-row").length).toBe(2);

    const cards = bodyEl().querySelectorAll(".ds-card");
    expect(cards.length).toBe(2);
    // Card-local hypothesis rows sit above the ⊢ conclusion.
    expect(cards[0].querySelector(".ds-row .ds-code")!.textContent).toBe("hx : 0 < x");
    expect(cards[0].querySelector(".ds-turnstile")!.textContent).toBe("⊢");
    expect(cards[0].querySelector(".ds-concl .ds-code")!.textContent).toBe("Q x");
    expect(cards[1].querySelectorAll(".ds-row").length).toBe(0);
    // Line breaks inside a conclusion survive.
    expect(cards[1].querySelector(".ds-concl .ds-code")!.textContent).toBe("R x\n  ∧ S x");
    // Structured rendering REPLACES the raw block.
    expect(bodyEl().querySelector("pre")).toBeNull();
  });

  it("uses assumption vocabulary for a decomposed Prop-valued assumption", async () => {
    const data = {
      ...BASE,
      entries: [entry({ env: "assumptionv", paper_label: "Assumption 11" })],
      snippets: {
        T1: snippet({
          statement: "def Envelope (P : Law) : Prop := ∃ C, 0 < C ∧ ∀ n, 0 < n → Bound P C n",
          structured: {
            sharedHyps: [
              { chip: "decl", code: "(P : Law)" },
              { chip: "hyp", code: "hP : Admissible P" },
            ],
            conclusions: [
              {
                hyps: [],
                intro: "∃ C : ℝ,",
                sub: [
                  { hyps: [], code: "0 < C" },
                  { hyps: [{ chip: "hyp", code: "0 < n" }], code: "Bound P C n" },
                ],
              },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Assumption 11.</div>`);
    await openBlock("T1");

    expect([...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent)).toEqual([
      "Parameters",
      "Assumption clause 1",
    ]);
    expect([...bodyEl().querySelectorAll(".ds-chip")].map((n) => n.textContent)).toEqual([
      "param",
      "premise",
      "condition",
      "premise",
    ]);
    expect(bodyEl().textContent).not.toContain("Hypotheses");
    expect(bodyEl().textContent).not.toContain("Conclusion");
  });

  it("uses defining-clause vocabulary for a decomposed Prop definition", async () => {
    const data = {
      ...BASE,
      entries: [entry({ env: "definitionv", paper_label: "Definition 4" })],
      snippets: {
        T1: snippet({
          statement: "def Regular (P : Law) : Prop := A P ∧ B P",
          structured: {
            sharedHyps: [{ chip: "decl", code: "(P : Law)" }],
            conclusions: [{ hyps: [], code: "A P" }, { hyps: [], code: "B P" }],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Definition 4.</div>`);
    await openBlock("T1");

    expect([...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent)).toEqual([
      "Parameters",
      "Defining clause 1",
      "Defining clause 2",
    ]);
    expect(bodyEl().querySelector(".ds-chip")!.textContent).toBe("param");
  });

  it("labels a single assumption clause and distinguishes quantified variables", async () => {
    const data = {
      ...BASE,
      entries: [entry({ env: "assumptionv", paper_label: "Assumption 4" })],
      snippets: {
        T1: snippet({
          statement: "def Exchangeable (Q : Law) : Prop := ∀ k a, Independent Q k a",
          structured: {
            sharedHyps: [
              { chip: "decl", code: "(Q : Law)" },
              { chip: "decl", code: "∀ k a" },
            ],
            conclusions: [{ hyps: [], code: "Independent Q k a" }],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Assumption 4.</div>`);
    await openBlock("T1");

    expect([...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent)).toEqual([
      "Parameters",
      "Assumption clause",
    ]);
    expect([...bodyEl().querySelectorAll(".ds-chip")].map((n) => n.textContent)).toEqual([
      "param",
      "for each",
    ]);
    expect(bodyEl().querySelector(".ds-card .ds-code")!.textContent).toBe("Independent Q k a");
  });

  it("renders a cited chip distinctly from a hyp chip", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [
              { chip: "hyp", code: "he : 0 < ε" },
              { chip: "cited", code: "hZeng : ZengOneArmMinimaxLower ε" },
              { chip: "decl", code: "n : ℕ" },
            ],
            conclusions: [{ hyps: [], code: "Q" }],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    const rows = [...bodyEl().querySelectorAll(".ds-row")];
    expect(rows.map((r) => r.querySelector(".ds-chip")!.textContent)).toEqual([
      "hyp",
      "cited",
      "decl",
    ]);
    // its own class (so it can carry its own colour) and an explanatory tooltip
    const chip = rows[1].querySelector(".ds-chip-cited")!;
    expect(chip.getAttribute("title")).toBe(
      "assumed external result — stated, not proven in this development",
    );
    expect(rows[1].classList.contains("ds-row-cited")).toBe(true);
    expect(rows[0].querySelector(".ds-chip-cited")).toBeNull();
    expect(rows[0].querySelector(".ds-chip-hyp")!.getAttribute("title")).toBeNull();
    // an unknown chip name never becomes a CSS class
    expect(rows[2].querySelector(".ds-chip-decl")).not.toBeNull();
  });

  it("a single unconditional conclusion renders as one bare ⊢ block", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({ structured: { sharedHyps: [], conclusions: [{ hyps: [], code: "Q x" }] } }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelectorAll(".ds-card").length).toBe(0);
    expect(bodyEl().querySelectorAll(".ds-label").length).toBe(0);
    expect(bodyEl().querySelectorAll(".ds-concl").length).toBe(1);
    expect(bodyEl().querySelector(".ds-concl .ds-code")!.textContent).toBe("Q x");
  });

  it("an ∃-headed statement numbers the CLAIMS, not the existential", async () => {
    // Shape of thm:sharp-minimax-fixed-interior: the whole theorem is one
    // `∃ …, …` clause. Numbering that clause "Conclusion 1" names the
    // existential and hides (i)…(iii), which is what the reader came for.
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "hP : P", xl: "h#0" }],
            conclusions: [
              {
                hyps: [{ chip: "hyp", code: "hε : 0 < ε" }],
                intro: "∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,",
                xl: "goal",
                sub: [
                  { hyps: [], code: "0 < C_epsilon", xl: "side#1" },
                  { hyps: [], code: "rho_epsilon < 1" },
                  {
                    hyps: [{ chip: "hyp", code: "hn : N_epsilon ≤ n" }],
                    intro: "∀ n : ℕ,",
                    xl: "claim#1",
                    sub: [{ hyps: [], code: "dist (x n) x₀ ≤ C_epsilon * rho_epsilon ^ n" }],
                  },
                  { hyps: [], code: "Tendsto x atTop (𝓝 x₀)", xl: "claim#2" },
                ],
              },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    // The ∃ frame is UNLABELLED; the numbering moved down onto the claims.
    const labels = [...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent);
    expect(labels).toEqual(["Hypotheses", "Conclusion 1", "Conclusion 2"]);

    const lift = bodyEl().querySelector(".ds-lift")!;
    expect(lift.querySelector(".ds-label")).toBeNull();
    expect(lift.querySelector(":scope > .ds-rows .ds-code")!.textContent).toBe("hε : 0 < ε");
    const intro = lift.querySelector(":scope > .ds-intro")!;
    expect(intro.textContent).toBe("∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,");
    // an intro introduces binders; it is NOT a conclusion, so it never gets ⊢
    expect(intro.querySelector(".ds-turnstile")).toBeNull();

    // the LEADING hypothesis-free leaves become quiet side rows, not claims
    const sides = [...lift.querySelectorAll(".ds-sides .ds-row-side")];
    expect(sides.map((s) => s.querySelector(".ds-code")!.textContent)).toEqual([
      "0 < C_epsilon",
      "rho_epsilon < 1",
    ]);
    expect(sides.map((s) => s.querySelector(".ds-chip")!.textContent)).toEqual(["side", "side"]);
    expect(lift.querySelector(".ds-sides .ds-turnstile")).toBeNull();
    // re-parenting must not drop crosslink tokens — and each rides on its own
    // CONTENT LINE, never on the frame or card container around it
    expect(sides[0].getAttribute("data-xl")).toBe("side#1");
    expect(lift.hasAttribute("data-xl")).toBe(false);
    expect(intro.getAttribute("data-xl")).toBe("goal");

    // the remaining subs are numbered cards, each rendered in full
    const cards = [...bodyEl().querySelectorAll(".ds-card")];
    expect(cards.length).toBe(2);
    expect(cards[0].hasAttribute("data-xl")).toBe(false);
    // a BRANCH card's token sits on its ∃ intro line
    expect(cards[0].querySelector(":scope > .ds-intro")!.getAttribute("data-xl")).toBe("claim#1");
    expect(cards[0].querySelector(":scope > .ds-rows .ds-code")!.textContent).toBe("hn : N_epsilon ≤ n");
    expect(cards[0].querySelector(":scope > .ds-intro")!.textContent).toBe("∀ n : ℕ,");
    // …and anything BELOW a numbered card stays unlabelled
    const deeper = [...cards[0].querySelectorAll(":scope > .ds-subs > .ds-sub")];
    expect(deeper.length).toBe(1);
    expect(deeper[0].querySelector(".ds-label")).toBeNull();
    expect(deeper[0].querySelector(".ds-concl .ds-code")!.textContent).toBe(
      "dist (x n) x₀ ≤ C_epsilon * rho_epsilon ^ n",
    );
    expect(cards[1].querySelector(".ds-concl .ds-code")!.textContent).toBe("Tendsto x atTop (𝓝 x₀)");

    // ⊢ still marks exactly the leaves that are CLAIMS — the side rows are not.
    expect(bodyEl().querySelectorAll(".ds-turnstile").length).toBe(2);
    expect(bodyEl().textContent).not.toContain("Conclusion 3");
  });

  it("does not demote real claims: all-leaf ∃ subs stay numbered conclusions", async () => {
    // `∃ x, P x ∧ Q x` — every sub is a hypothesis-free leaf, so the leading-run
    // rule would swallow the whole theorem into side conditions. Numbering a
    // qualifier is verbose; demoting a claim is wrong, so nothing is lifted.
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [],
            conclusions: [
              {
                hyps: [],
                intro: "∃ x : ℝ,",
                sub: [{ hyps: [], code: "P x" }, { hyps: [], code: "Q x" }],
              },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".ds-sides")).toBeNull();
    expect([...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent)).toEqual([
      "Conclusion 1",
      "Conclusion 2",
    ]);
    expect(bodyEl().querySelectorAll(".ds-turnstile").length).toBe(2);
  });

  it("a lone ∃ card with no sub (pure leaf) is unchanged", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [],
            conclusions: [{ hyps: [], intro: "∃ y : ℕ,", code: "0 < y" }],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".ds-lift")).toBeNull();
    expect(bodyEl().querySelector(".ds-sides")).toBeNull();
    expect(bodyEl().querySelector(".ds-label")!.textContent).toBe("Conclusion 1");
    expect(bodyEl().querySelector(".ds-intro")!.textContent).toBe("∃ y : ℕ,");
    expect(bodyEl().querySelector(".ds-concl .ds-code")!.textContent).toBe("0 < y");
  });

  it("a multi-card statement is untouched by the ∃ rule", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [],
            conclusions: [
              { hyps: [], intro: "∃ x : ℝ,", sub: [{ hyps: [], code: "0 < x" }, { hyps: [], code: "P x" }] },
              { hyps: [], code: "Q" },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    // two TOP-LEVEL cards → the outer numbering stays where it was, and the
    // first card keeps its nested (unlabelled) sub-cards.
    expect(bodyEl().querySelector(".ds-lift")).toBeNull();
    expect([...bodyEl().querySelectorAll(".ds-label")].map((n) => n.textContent)).toEqual([
      "Conclusion 1",
      "Conclusion 2",
    ]);
    const first = bodyEl().querySelectorAll(".ds-card")[0];
    expect(first.querySelectorAll(":scope > .ds-subs > .ds-sub").length).toBe(2);
  });

  it("a malformed card (both / neither of code|sub) prefers code and never throws", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [],
            conclusions: [
              // both: code wins, the sub split is dropped
              { hyps: [], code: "Q x", sub: [{ hyps: [], code: "never rendered" }] },
              // neither: renders its intro and simply has no ⊢
              { hyps: [], intro: "∃ y : ℕ," },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    const cards = bodyEl().querySelectorAll(".ds-card");
    expect(cards.length).toBe(2);
    expect(cards[0].querySelector(".ds-concl .ds-code")!.textContent).toBe("Q x");
    expect(cards[0].querySelector(".ds-sub")).toBeNull();
    expect(bodyEl().textContent).not.toContain("never rendered");
    expect(cards[1].querySelector(".ds-intro")!.textContent).toBe("∃ y : ℕ,");
    expect(cards[1].querySelector(".ds-concl")).toBeNull();
  });

  it("marks an unstated row, quietly and only where the payload says so", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [
              { chip: "hyp", code: "hPaired : P x" },
              { chip: "hyp", code: "hTechnical : Measurable f", unstated: true },
            ],
            conclusions: [
              {
                hyps: [],
                intro: "∃ C : ℝ,",
                sub: [
                  // a leading side condition …
                  { hyps: [], code: "0 < C", unstated: true },
                  // … then real claims (the hyps stop the leading run)
                  { hyps: [{ chip: "hyp", code: "hx : 0 < x" }], code: "Q x", unstated: true },
                  { hyps: [], code: "S x" },
                ],
              },
            ],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    // exactly the rows the payload flagged — hyp row, side row, and ⊢ leaf
    const marks = [...bodyEl().querySelectorAll(".ds-unstated")];
    expect(marks.length).toBe(3);
    expect(new Set(marks.map((m) => m.textContent))).toEqual(
      new Set(["not stated in the paper"]),
    );
    expect(new Set(marks.map((m) => m.getAttribute("title")))).toEqual(
      new Set([
        "this formal clause has no counterpart sentence in the paper — verified as unstated",
      ]),
    );

    // it rides on the right rows and nowhere else — one of each kind
    const cells = [...bodyEl().querySelectorAll(".ds-row, .ds-concl")];
    const cellOf = (code: string) =>
      cells.find((r) => r.querySelector(".ds-code")!.textContent === code)!;
    // a hypothesis row
    expect(cellOf("hTechnical : Measurable f").querySelector(".ds-unstated")).not.toBeNull();
    expect(cellOf("hPaired : P x").querySelector(".ds-unstated")).toBeNull();
    // a side-condition row lifted under the ∃
    const side = cellOf("0 < C");
    expect(side.classList.contains("ds-row-side")).toBe(true);
    expect(side.querySelector(".ds-unstated")).not.toBeNull();
    // a ⊢ conclusion leaf
    const qx = cellOf("Q x");
    expect(qx.classList.contains("ds-concl")).toBe(true);
    expect(qx.querySelector(".ds-unstated")).not.toBeNull();
    expect(cellOf("S x").querySelector(".ds-unstated")).toBeNull();

    // it is NOT one of the role chips — those say what a row IS, this says
    // something about the pairing
    expect(marks.every((m) => !m.classList.contains("ds-chip"))).toBe(true);
    expect(bodyEl().querySelectorAll(".ds-chip-unstated").length).toBe(0);
  });

  it("renders no unstated marker when the payload omits the flag", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "h : P" }],
            conclusions: [{ hyps: [], code: "Q" }],
          },
        }),
      },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".ds-unstated")).toBeNull();
    expect(bodyEl().textContent).not.toContain("not stated in the paper");
  });

  it("falls back to <pre> when a structured view carries no conclusion", async () => {
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: { T1: snippet({ structured: { sharedHyps: [], conclusions: [] } }) },
    };
    mount(data, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".ds-structured")).toBeNull();
    expect(bodyEl().querySelector("pre")!.textContent).toContain("theorem thm_one");
  });
});

describe("component views", () => {
  const LONG = Array.from({ length: 30 }, (_, i) => `  line ${i}`).join("\n");
  const withViews = {
    ...BASE,
    entries: [entry({}), entry({ obj_id: "P1", paper_label: "Assumption 2", env: "assumptionv", lean: null, fallback: "" })],
    snippets: {
      T1: snippet({
        componentViews: [
          {
            decl: "thm_one",
            file: "A.lean",
            line: 12,
            statement: "theorem thm_one (h : P) : Q",
            cls: "anchor",
            depth: 0,
            structured: { sharedHyps: [{ chip: "hyp", code: "h : P" }], conclusions: [{ hyps: [], code: "Q" }] },
          },
          { decl: "IsWeaklyOverlapping", file: "B.lean", line: 4, statement: "def IsWeaklyOverlapping (e : Ω → ℝ) : Prop := ∀ ω, 0 < e ω", cls: "env", depth: 1 },
          { decl: "assumption_two", file: "C.lean", line: 7, statement: "", cls: "paper", paperObjId: "P1", paperLabel: "Assumption 2", depth: 1 },
          { decl: "aux_deep", file: "D.lean", line: 90, statement: `lemma aux_deep : True\n${LONG}`, cls: "lean_only", depth: 3 },
          { decl: "aux_shallow", file: "D.lean", line: 3, statement: "lemma aux_shallow : True", cls: "lean_only", depth: 1 },
        ],
      }),
    },
  };

  // `withViews` is the PRE-dedupe shape: no declSources, every component
  // carrying its own file/line/statement inline. It must keep rendering exactly
  // as it did before the shared side table existed.
  it("renders the four classes in order, with the anchor as the statement", async () => {
    expect("declSources" in withViews).toBe(false);
    mount(withViews, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    // anchor: the statement itself, structured, with a red-wash "anchor decl" pill
    const anchor = bodyEl().querySelector(".cv-card-anchor")!;
    expect(anchor.querySelector(".cv-tag-anchor")!.textContent).toBe("anchor decl");
    expect(anchor.querySelector(".cv-decl")!.textContent).toBe("thm_one");
    expect(anchor.querySelector(".ds-concl .ds-code")!.textContent).toBe("Q");

    // env: decl name + file + the "↔ formula in this statement" tag, code inlined
    const env = bodyEl().querySelector(".cv-card-env")!;
    expect(env.querySelector(".cv-decl")!.textContent).toBe("IsWeaklyOverlapping");
    expect(env.querySelector(".cv-file")!.textContent).toBe("B.lean:4");
    expect(env.querySelector(".cv-tag-env")!.textContent).toBe("↔ formula in this statement");
    expect(env.querySelector("pre")!.textContent).toContain("IsWeaklyOverlapping");

    // paper: a chip, never inlined code
    const chip = bodyEl().querySelector(".cv-paper-chip") as HTMLElement;
    expect(chip.textContent).toContain("assumption_two → Assumption 2");
    expect(chip.textContent).toContain("↑ view in paper");
    expect(chip.dataset.paperObj).toBe("P1");

    // lean_only: exact section wording, collapsed <details>, FULL source inside
    const sect = bodyEl().querySelector(".cv-sect-lean-only")!;
    expect(sect.querySelector(".cv-label")!.textContent).toBe("Lean only — not stated in the paper");
    const details = [...sect.querySelectorAll("details")];
    expect(details.length).toBe(2);
    expect(details.every((d) => !d.open)).toBe(true);
    // sorted by depth, then given order
    expect(details.map((d) => d.querySelector("summary")!.textContent!.trim().split(" ")[0])).toEqual([
      "aux_shallow",
      "aux_deep",
    ]);
    expect(details[1].querySelector("summary")!.textContent).toContain("(31 lines)");
    // never truncated: the last line of a 31-line body is present
    expect(details[1].querySelector("pre")!.textContent).toContain("line 29");
  });

  it("a paper chip flashes its block in the paper and leaves the panel open", async () => {
    mount(
      withViews,
      `<div class="formal-block" data-objid="T1">Theorem 1.</div>
       <div class="formal-block" data-objid="P1">Assumption 2.</div>`,
    );
    await openBlock("T1");
    const chip = bodyEl().querySelector(".cv-paper-chip") as HTMLElement;
    chip.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();

    const target = document.querySelector('[data-objid="P1"]')!;
    expect(target.classList.contains("flash")).toBe(true);
    expect(isOpen()).toBe(true);
    // The panel still shows Theorem 1 — the chip navigates the PAPER, not the panel.
    expect(document.getElementById("drawer-title")!.textContent).toContain("Theorem 1");
  });

  it("resolves every component's source through the shared declSources table", async () => {
    // Post-dedupe shape: the views carry only a key; the statements live once.
    const deduped = {
      ...BASE,
      entries: [entry({})],
      declSources: {
        "Paper.thm_one": {
          file: "A.lean",
          line: 12,
          statement: "theorem thm_one (h : P) : Q",
          structured: { sharedHyps: [{ chip: "hyp", code: "h : P" }], conclusions: [{ hyps: [], code: "Q" }] },
        },
        "Paper.IsWeaklyOverlapping": {
          file: "B.lean",
          line: 4,
          statement: "def IsWeaklyOverlapping (e : Ω → ℝ) : Prop := ∀ ω, 0 < e ω",
        },
        "Paper.aux_deep": { file: "D.lean", line: 90, statement: `lemma aux_deep : True\n${LONG}` },
      },
      snippets: {
        T1: snippet({
          // Production always carries the ENTRY's own structured view alongside
          // the table copy — same content, and the only place xl tokens live.
          // Omitting it here used to let the anchor read from either source
          // without the test noticing.
          structured: { sharedHyps: [{ chip: "hyp", code: "h : P" }], conclusions: [{ hyps: [], code: "Q" }] },
          componentViews: [
            { decl: "thm_one", key: "Paper.thm_one", cls: "anchor", depth: 0 },
            { decl: "IsWeaklyOverlapping", key: "Paper.IsWeaklyOverlapping", cls: "env", depth: 1 },
            { decl: "aux_deep", key: "Paper.aux_deep", cls: "lean_only", depth: 3 },
          ],
        }),
      },
    };
    mount(deduped, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    const anchor = bodyEl().querySelector(".cv-card-anchor")!;
    expect(anchor.querySelector(".cv-file")!.textContent).toBe("A.lean:12");
    // the table's structured view drives the render, not a <pre>
    expect(anchor.querySelector(".ds-concl .ds-code")!.textContent).toBe("Q");
    expect(anchor.querySelector(".ds-row .ds-code")!.textContent).toBe("h : P");

    const env = bodyEl().querySelector(".cv-card-env")!;
    expect(env.querySelector(".cv-file")!.textContent).toBe("B.lean:4");
    expect(env.querySelector("pre")!.textContent).toContain("∀ ω, 0 < e ω");

    // full source still expands from the table — never truncated
    const det = bodyEl().querySelector(".cv-sect-lean-only details")!;
    expect(det.querySelector("summary")!.textContent).toContain("(31 lines)");
    expect(det.querySelector("pre")!.textContent).toContain("line 29");
  });

  it("renders a keyed anchor from the ENTRY's structured view, so xl tokens survive", async () => {
    // Regression, production-shaped. The shared declSources copy is cited by
    // every drawer that uses the decl, so it is deliberately token-free;
    // enrichment attaches xl to the ENTRY's structured view. Rendering the
    // shared copy for the anchor silently dropped every statement-level
    // crosslink on the live site — the pairs existed but were one-sided.
    const prod = {
      ...BASE,
      entries: [entry({})],
      declSources: {
        "Paper.thm_one": {
          file: "A.lean",
          line: 12,
          statement: "theorem thm_one (h : P x) : Q x",
          // same content as the entry view below, minus the tokens
          structured: {
            sharedHyps: [{ chip: "hyp", code: "h : P x" }],
            conclusions: [{ hyps: [], code: "Q x" }],
          },
        },
      },
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "h : P x", xl: "h#1" }],
            conclusions: [{ hyps: [], code: "Q x", xl: "goal#0" }],
          },
          componentViews: [{ decl: "thm_one", key: "Paper.thm_one", cls: "anchor", depth: 0 }],
        }),
      },
    };
    mount(
      prod,
      `<div class="formal-block" data-objid="T1">If <span id="hp" data-xl="h#1">P holds of x</span>
         then <span id="gq" data-xl="goal#0">Q holds of x</span>.</div>`,
    );
    await openBlock("T1");

    const anchor = bodyEl().querySelector(".cv-card-anchor")!;
    // dedupe still works: the header comes from the shared table
    expect(anchor.querySelector(".cv-file")!.textContent).toBe("A.lean:12");
    // …but the STATEMENT comes from the entry, tokens intact
    const row = anchor.querySelector(".ds-row")!;
    const leaf = anchor.querySelector(".ds-concl")!;
    expect(row.getAttribute("data-xl")).toBe("h#1");
    expect(leaf.getAttribute("data-xl")).toBe("goal#0");

    // …and the crosslink actually reaches the paper, in both directions
    over(row);
    expect(document.getElementById("hp")!.classList.contains("xl-hot")).toBe(true);
    expect(document.getElementById("gq")!.classList.contains("xl-hot")).toBe(false);
    out(row);

    over(document.getElementById("gq")!);
    expect(leaf.classList.contains("xl-hot")).toBe(true);
    expect(row.classList.contains("xl-hot")).toBe(false);
  });

  it("mixes a keyed component and an inline-only one in the same payload", async () => {
    const mixed = {
      ...BASE,
      entries: [entry({})],
      declSources: {
        "Paper.by_key": { file: "K.lean", line: 5, statement: "def by_key : Prop := True" },
      },
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "by_key", key: "Paper.by_key", cls: "env", depth: 1 },
            // no key at all — the pre-dedupe inline shape, still honoured
            { decl: "inline_only", file: "I.lean", line: 9, statement: "def inline_only : Prop := False", cls: "env", depth: 1 },
            // a key the table does not have: degrade to the inline fields
            { decl: "stale_key", key: "Paper.missing", file: "S.lean", line: 2, statement: "def stale_key : Prop := True", cls: "env", depth: 1 },
          ],
        }),
      },
    };
    mount(mixed, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    const cards = [...bodyEl().querySelectorAll(".cv-card-env")];
    expect(cards.map((c) => c.querySelector(".cv-decl")!.textContent)).toEqual([
      "by_key",
      "inline_only",
      "stale_key",
    ]);
    expect(cards.map((c) => c.querySelector(".cv-file")!.textContent)).toEqual([
      "K.lean:5",
      "I.lean:9",
      "S.lean:2",
    ]);
    expect(cards[0].querySelector("pre")!.textContent).toContain("def by_key");
    expect(cards[1].querySelector("pre")!.textContent).toContain("def inline_only");
    expect(cards[2].querySelector("pre")!.textContent).toContain("def stale_key");
  });

  it("emits data-xl on every class of component card and cross-highlights it", async () => {
    const xlViews = {
      ...BASE,
      entries: [entry({}), entry({ obj_id: "P1", paper_label: "Definition 9", env: "definitionv", lean: null, fallback: "" })],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "thm_one", file: "A.lean", line: 12, statement: "theorem thm_one : Q", cls: "anchor", depth: 0, xl: "a#0" },
            { decl: "Env", file: "B.lean", line: 4, statement: "def Env : Prop := True", cls: "env", depth: 1, xl: "d#9 d#9b" },
            { decl: "paper_decl", file: "C.lean", line: 7, statement: "", cls: "paper", paperObjId: "P1", paperLabel: "Definition 9", depth: 1, xl: "d#9" },
            { decl: "aux", file: "D.lean", line: 3, statement: "lemma aux : True", cls: "lean_only", depth: 1, xl: "x#1" },
          ],
        }),
      },
    };
    mount(
      xlViews,
      `<div class="formal-block" data-objid="T1">Theorem 1, see
         <span id="d9" data-xl="d#9">Definition 9</span> and
         <span id="x1" data-xl="x#1">the helper</span>.</div>`,
    );
    await openBlock("T1");

    // all four classes carry the token list verbatim — on their content LINE
    // (the head, the summary, the chip), never on the card container
    const anchorHead = bodyEl().querySelector(".cv-card-anchor > .cv-head")!;
    const envHead = bodyEl().querySelector(".cv-card-env > .cv-head")!;
    const summary = bodyEl().querySelector(".cv-lean-only > summary")!;
    expect(anchorHead.getAttribute("data-xl")).toBe("a#0");
    expect(envHead.getAttribute("data-xl")).toBe("d#9 d#9b");
    expect(bodyEl().querySelector(".cv-paper-chip")!.getAttribute("data-xl")).toBe("d#9");
    expect(summary.getAttribute("data-xl")).toBe("x#1");
    expect(bodyEl().querySelector(".cv-card-anchor")!.hasAttribute("data-xl")).toBe(false);
    expect(bodyEl().querySelector(".cv-card-env")!.hasAttribute("data-xl")).toBe(false);
    expect(bodyEl().querySelector("details.cv-lean-only")!.hasAttribute("data-xl")).toBe(false);

    // …and they take part in the hover crosslink, in both directions
    const chip = bodyEl().querySelector(".cv-paper-chip")!;
    over(envHead);
    // env names d#9, which the paper chip and the body span both carry
    expect(chip.classList.contains("xl-hot")).toBe(true);
    expect(document.getElementById("d9")!.classList.contains("xl-hot")).toBe(true);
    expect(document.getElementById("x1")!.classList.contains("xl-hot")).toBe(false);
    out(envHead);

    // paper side → panel side: the lean-only summary lights from its own span
    over(document.getElementById("x1")!);
    expect(summary.classList.contains("xl-hot")).toBe(true);
    expect(envHead.classList.contains("xl-hot")).toBe(false);
  });

  it("warns about sorries in the closure: per-card chip, entry badge, truncation note", async () => {
    const sorries = {
      ...BASE,
      entries: [entry({})],
      declSources: {
        "Paper.clean": { file: "B.lean", line: 4, statement: "def clean : Prop := True", usesSorry: false },
        "Paper.dirty": { file: "D.lean", line: 9, statement: "lemma dirty : True := by sorry", usesSorry: true },
      },
      snippets: {
        T1: snippet({
          // the ANCHOR is sorry-free; a pulled-in helper is not
          sorry_free: true,
          closureHasSorry: true,
          closureTruncated: 3,
          componentViews: [
            { decl: "clean", key: "Paper.clean", cls: "env", depth: 1 },
            { decl: "dirty", key: "Paper.dirty", cls: "lean_only", depth: 2 },
          ],
        }),
      },
    };
    mount(sorries, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    // (a) the chip rides on the card whose RESOLVED source says so, not others.
    // `clean` is known-clean (usesSorry: false), so it carries NO chip at all.
    expect(bodyEl().querySelector(".cv-card-env .cv-tag-sorry")).toBeNull();
    expect(bodyEl().querySelector(".cv-card-env .cv-tag-unknown")).toBeNull();
    const fold = bodyEl().querySelector("details.cv-lean-only")!;
    expect(fold.querySelector(".cv-tag-sorry")!.textContent).toBe("⚠ uses sorry");

    // (b) the green anchor badge is still there, but no longer stands alone
    const meta = bodyEl().querySelector(".drawer-meta")!;
    expect(meta.querySelector(".badge-ok")!.textContent).toContain("sorry-free");
    expect(meta.querySelector(".badge-warn")!.textContent).toBe("⚠ a pulled-in helper uses sorry");

    // (c) the closure list does not pretend to be complete
    expect(bodyEl().querySelector(".cv-truncated")!.textContent).toBe(
      "closure truncated — 3 more declarations at depth >4 (see the Lean development page)",
    );
  });

  it("says nothing about the closure when the payload reports nothing", async () => {
    mount(withViews, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".cv-tag-sorry")).toBeNull();
    expect(bodyEl().querySelector(".cv-truncated")).toBeNull();
    expect(bodyEl().querySelector(".drawer-meta .badge-warn")).toBeNull();
    expect(bodyEl().querySelector(".drawer-meta .badge-unknown")).toBeNull();
  });

  it("treats a missing usesSorry as UNKNOWN, never as clean", async () => {
    const triState = {
      ...BASE,
      entries: [entry({})],
      declSources: {
        // an index built before the field existed reports nothing
        "Paper.silent": { file: "B.lean", line: 4, statement: "def silent : Prop := True" },
        "Paper.clean": { file: "C.lean", line: 5, statement: "def clean : Prop := True", usesSorry: false },
        "Paper.dirty": { file: "D.lean", line: 9, statement: "lemma dirty : True", usesSorry: true },
      },
      snippets: {
        T1: snippet({
          closureSorryUnknown: 4,
          componentViews: [
            { decl: "silent", key: "Paper.silent", cls: "env", depth: 1 },
            { decl: "clean", key: "Paper.clean", cls: "env", depth: 1 },
            { decl: "dirty", key: "Paper.dirty", cls: "env", depth: 1 },
          ],
        }),
      },
    };
    mount(triState, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    const [silent, clean, dirty] = [...bodyEl().querySelectorAll(".cv-card-env")];
    // undefined → the neutral grey chip
    expect(silent.querySelector(".cv-tag-unknown")!.textContent).toBe("verification unknown");
    expect(silent.querySelector(".cv-tag-sorry")).toBeNull();
    // false → no chip of either kind
    expect(clean.querySelector(".cv-tag-unknown")).toBeNull();
    expect(clean.querySelector(".cv-tag-sorry")).toBeNull();
    // true → the existing red chip, unaffected by the new state
    expect(dirty.querySelector(".cv-tag-sorry")!.textContent).toBe("⚠ uses sorry");
    expect(dirty.querySelector(".cv-tag-unknown")).toBeNull();

    // the entry-level count, quiet and separate from the red warning
    const meta = bodyEl().querySelector(".drawer-meta")!;
    expect(meta.querySelector(".badge-unknown")!.textContent).toBe(
      "verification status of 4 pulled-in helpers unknown",
    );
    // this payload claims no sorry in the closure, so no red badge appears
    expect(meta.querySelector(".badge-warn")).toBeNull();
  });

  it("says 'helper' for one and 'helpers' for many", async () => {
    const one = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          closureSorryUnknown: 1,
          closureTruncated: 1,
          componentViews: [
            { decl: "aux", file: "D.lean", line: 3, statement: "lemma aux : True", cls: "lean_only", depth: 1 },
          ],
        }),
      },
    };
    mount(one, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".badge-unknown")!.textContent).toBe(
      "verification status of 1 pulled-in helper unknown",
    );
    // the other count-bearing copy pluralizes on the same rule
    expect(bodyEl().querySelector(".cv-truncated")!.textContent).toBe(
      "closure truncated — 1 more declaration at depth >4 (see the Lean development page)",
    );
  });

  it("folds a legacy `support` component into the Lean-only section", async () => {
    // `support` encoded v2 pipeline provenance, not reader-relevant meaning, so
    // it is gone from the payload. A pre-merge payload must still render its
    // components rather than silently dropping them.
    const legacyCls = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "Linked", file: "B.lean", line: 4, statement: "def Linked : Prop := True", cls: "env", depth: 1 },
            { decl: "Legacy", file: "C.lean", line: 9, statement: "def Legacy : Prop := False", cls: "support", depth: 0 },
            { decl: "Helper", file: "D.lean", line: 2, statement: "lemma Helper : True", cls: "lean_only", depth: 2 },
          ],
        }),
      },
    };
    mount(legacyCls, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    // no support card, tag or section survives anywhere
    expect(bodyEl().querySelector(".cv-card-support")).toBeNull();
    expect(bodyEl().querySelector(".cv-tag-support")).toBeNull();
    expect(bodyEl().textContent).not.toContain("supporting definition");

    // it renders as an ordinary unlinked piece, and being depth-0 sorts first
    const sect = bodyEl().querySelector(".cv-sect-lean-only")!;
    expect(sect.querySelector(".cv-label")!.textContent).toBe(
      "Lean only — not stated in the paper",
    );
    const folds = [...sect.querySelectorAll("details")];
    expect(folds.map((d) => d.querySelector("summary")!.textContent!.trim().split(" ")[0])).toEqual([
      "Legacy",
      "Helper",
    ]);
    expect(folds[0].querySelector("pre")!.textContent).toContain("def Legacy");

    // env is untouched by the merge
    const env = bodyEl().querySelector(".cv-card-env")!;
    expect(env.querySelector(".cv-tag-env")!.textContent).toBe("↔ formula in this statement");
    expect(env.querySelector(".cv-decl")!.textContent).toBe("Linked");
  });

  it("does not read data-xl-decl, however many names it lists", async () => {
    // v3 makes it a SPACE-SEPARATED list of fully-qualified names. It is a
    // naming aid: the shared token drives highlighting, and nothing here may
    // parse this attribute — least of all as a single name.
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "h : P x", xl: "T1#r1" }],
            conclusions: [{ hyps: [], code: "Q x", xl: "T1#r2" }],
          },
        }),
      },
    };
    mount(
      data,
      `<div class="formal-block" data-objid="T1">If
         <span id="a" data-xl="T1#r1" data-xl-decl="Ns.One Ns.Two Ns.Three">P holds</span>, then
         <span id="b" data-xl-decl="Ns.Four">an aid with no token</span>.</div>`,
    );
    await openBlock("T1");

    // a decl list without a token is still not a carrier
    const block = document.querySelector('[data-objid="T1"]')!;
    expect([...block.querySelectorAll("[data-xl]")].map((e) => e.id)).toEqual(["a"]);
    // highlighting keys off the token alone, and the multi-name list is inert
    over(bodyEl().querySelector(".ds-row")!);
    expect(document.getElementById("a")!.classList.contains("xl-hot")).toBe(true);
    expect(document.getElementById("b")!.classList.contains("xl-hot")).toBe(false);
    // the attribute is untouched — not rewritten, not split, not consumed
    expect(document.getElementById("a")!.getAttribute("data-xl-decl")).toBe(
      "Ns.One Ns.Two Ns.Three",
    );
  });

  it("gives cited assumptions their own section, unfolded, opening their own panel", async () => {
    const withCited = {
      ...BASE,
      entries: [
        entry({}),
        // a citedv crosswalk entry: it has NO block in the paper body
        entry({
          obj_id: "C1",
          // a citedv entry has no paper number: its label is the raw crosswalk id
          paper_label: "Object lem:zeng-one-arm-minimax-lower",
          title: "Zeng one-arm minimax lower bound",
          env: "citedv",
          lean: { file: "Z.lean", decl: "ZengOneArmMinimaxLower", decl_kind: "def", line: 8 },
        }),
        entry({ obj_id: "P1", paper_label: "Definition 9", env: "definitionv", lean: null, fallback: "" }),
      ],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "Env", file: "B.lean", line: 4, statement: "def Env : Prop := True", cls: "env", depth: 1 },
            {
              decl: "ZengOneArmMinimaxLower",
              file: "Z.lean",
              line: 8,
              statement: "def ZengOneArmMinimaxLower (ε : ℝ) : Prop :=\n  ∀ n, rate n ≥ c * ε",
              cls: "cited",
              paperObjId: "C1",
              paperLabel: "Object lem:zeng-one-arm-minimax-lower",
              depth: 1,
            },
            { decl: "paper_decl", file: "C.lean", line: 7, statement: "", cls: "paper", paperObjId: "P1", paperLabel: "Definition 9", depth: 1 },
          ],
        }),
        C1: snippet({ decl: "ZengOneArmMinimaxLower", file: "Z.lean", line: 8, statement: "def ZengOneArmMinimaxLower (ε : ℝ) : Prop := True" }),
      },
    };
    mount(withCited, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    const sect = bodyEl().querySelector(".cv-sect-cited")!;
    expect(sect.querySelector(".cv-label")!.textContent).toBe(
      "Cited assumptions — assumed, not proven here",
    );
    const card = sect.querySelector(".cv-card-cited")!;
    expect(card.querySelector(".cv-tag-cited")!.textContent).toBe("cited — assumed");
    // The raw crosswalk id is machinery, never a label the reader should see;
    // the decl name plus a fixed descriptor and the entry's title stand in.
    expect(card.textContent).not.toContain("Object lem:");
    expect(card.querySelector(".cv-decl")!.textContent).toBe("ZengOneArmMinimaxLower");
    expect(card.querySelector(".cv-cited-desc")!.textContent).toBe(
      "cited result — Zeng one-arm minimax lower bound",
    );
    // it opens a panel, it does not scroll the paper — so it must not say "in paper"
    expect(card.querySelector(".cv-open-go")!.textContent).toBe("view assumed statement");
    expect(card.textContent).not.toContain("view in paper");
    // UNFOLDED: an assumption the reader cannot see cannot be checked
    expect(card.querySelector("details")).toBeNull();
    expect(card.querySelector("pre")!.textContent).toContain("∀ n, rate n ≥ c * ε");

    // the cited section follows the whole "Stated in the paper" section, which
    // now holds the env card AND the paper chips
    const statedSect = bodyEl().querySelector(".cv-sect-stated")!;
    expect(statedSect.contains(bodyEl().querySelector(".cv-card-env")!)).toBe(true);
    expect(statedSect.contains(bodyEl().querySelector(".cv-paper-chip")!)).toBe(true);
    expect(bodyEl().querySelector(".cv-sect-paper"), "the chips no longer get their own section").toBeNull();
    expect(
      statedSect.compareDocumentPosition(sect) & Node.DOCUMENT_POSITION_FOLLOWING,
    ).toBeTruthy();

    // the header opens the cited entry's OWN panel (there is no block to flash)
    const head = card.querySelector("button.cv-head-open") as HTMLElement;
    expect(head.dataset.openObj).toBe("C1");
    head.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();
    expect(document.getElementById("drawer-title")!.textContent).toContain(
      "Zeng one-arm minimax lower bound",
    );
    expect(isOpen()).toBe(true);
  });

  it("falls back to the bare descriptor when a cited entry has no title", async () => {
    const untitled = {
      ...BASE,
      entries: [entry({}), entry({ obj_id: "C1", paper_label: "Object lem:anon", title: null, env: "citedv", lean: null, fallback: "" })],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "AnonAssumption", file: "Z.lean", line: 2, statement: "def AnonAssumption : Prop := True", cls: "cited", paperObjId: "C1", paperLabel: "Object lem:anon", depth: 1 },
          ],
        }),
      },
    };
    mount(untitled, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    const card = bodyEl().querySelector(".cv-card-cited")!;
    expect(card.querySelector(".cv-cited-desc")!.textContent).toBe("cited result");
    expect(card.textContent).not.toContain("Object lem:");
  });

  it("shows exactly three sections, with anchor + env + chips under one header", async () => {
    const all = {
      ...BASE,
      entries: [
        entry({}),
        entry({ obj_id: "P1", paper_label: "Definition 9", env: "definitionv", lean: null, fallback: "" }),
        entry({ obj_id: "C1", paper_label: "Object lem:z", title: "Zeng bound", env: "citedv", lean: null, fallback: "" }),
      ],
      snippets: {
        T1: snippet({
          closureTruncated: 2,
          componentViews: [
            { decl: "thm_one", file: "A.lean", line: 12, statement: "theorem thm_one : Q", cls: "anchor", depth: 0 },
            { decl: "Env", file: "B.lean", line: 4, statement: "def Env : Prop := True", cls: "env", depth: 1 },
            { decl: "cited_decl", file: "Z.lean", line: 8, statement: "def cited_decl : Prop := True", cls: "cited", paperObjId: "C1", depth: 1 },
            { decl: "paper_decl", file: "C.lean", line: 7, statement: "", cls: "paper", paperObjId: "P1", paperLabel: "Definition 9", depth: 1 },
            { decl: "aux", file: "D.lean", line: 3, statement: "lemma aux : True", cls: "lean_only", depth: 1 },
          ],
        }),
      },
    };
    mount(all, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    // three sections, in this order, and no others
    const sects = [...bodyEl().querySelectorAll(".cv-sect")];
    expect(sects.map((s) => s.querySelector(".cv-label")!.textContent)).toEqual([
      "Stated in the paper",
      "Cited assumptions — assumed, not proven here",
      "Lean only — not stated in the paper",
    ]);

    // section 1 holds the anchor statement, then the env card, then the chips
    const stated = sects[0];
    const kids = [...stated.children].slice(1).map((n) => n.className.split(" ")[0]);
    expect(kids).toEqual(["cv-card", "cv-card", "cv-chips"]);
    expect(stated.querySelector(".cv-card-anchor")).not.toBeNull();
    expect(stated.querySelector(".cv-card-env .cv-tag-env")!.textContent).toBe(
      "↔ formula in this statement",
    );
    expect(stated.querySelector(".cv-paper-chip")!.textContent).toContain("→ Definition 9");
    // the anchor really is first
    expect((stated.children[1] as Element).classList.contains("cv-card-anchor")).toBe(true);

    // the cited card did NOT get pulled into section 1
    expect(stated.querySelector(".cv-card-cited")).toBeNull();
    expect(sects[1].querySelector(".cv-card-cited")).not.toBeNull();

    // the truncation note closes section 3, the list it qualifies
    const leanOnly = sects[2];
    expect(leanOnly.querySelector("details")).not.toBeNull();
    expect(leanOnly.lastElementChild!.className).toBe("cv-truncated");
    expect(leanOnly.querySelector(".cv-truncated")!.textContent).toBe(
      "closure truncated — 2 more declarations at depth >4 (see the Lean development page)",
    );
  });

  it("renders an external declaration as a name-and-link card among the env cards", async () => {
    const ext = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "Env", file: "B.lean", line: 4, statement: "def Env : Prop := True", cls: "env", depth: 1 },
            {
              decl: "minimaxRate",
              cls: "env",
              depth: 1,
              external: true,
              fullName: "Causalean.Stat.MinimaxRate",
              module: "Causalean/Stat/Rate.lean",
              xl: "T1#s4",
            },
          ],
        }),
      },
    };
    mount(ext, `<div class="formal-block" data-objid="T1">Uses <span id="mr" data-xl="T1#s4">the minimax rate</span>.</div>`);
    await openBlock("T1");

    // it sits in section 1, alongside the env cards, in payload order
    const stated = bodyEl().querySelector(".cv-sect-stated")!;
    const cards = [...stated.querySelectorAll(".cv-card")].map((c) => c.className.split(" ")[1]);
    expect(cards).toEqual(["cv-card-env", "cv-card-external"]);

    const card = stated.querySelector(".cv-card-external")!;
    expect(card.querySelector(".cv-decl")!.textContent).toBe("minimaxRate");
    expect(card.querySelector(".cv-tag-external")!.textContent).toBe("library declaration");
    expect(card.querySelector(".cv-file")!.textContent).toBe("Causalean/Stat/Rate.lean");

    // resolved through names.json into the explorer, in a new tab
    const link = card.querySelector("a.cv-ext-link") as HTMLAnchorElement;
    expect(link.getAttribute("href")).toBe("/library/Stat/Rate#Causalean.Stat.MinimaxRate");
    expect(link.getAttribute("target")).toBe("_blank");
    expect(link.getAttribute("rel")).toBe("noopener");

    // no source body, no fold, no verification chip — nothing was scanned
    expect(card.querySelector("pre")).toBeNull();
    expect(card.querySelector("details")).toBeNull();
    expect(card.querySelector(".ds-structured")).toBeNull();
    expect(card.querySelector(".cv-tag-sorry")).toBeNull();
    expect(card.querySelector(".cv-tag-unknown")).toBeNull();

    // …and it is a normal two-sided carrier
    const head = card.querySelector(".cv-head")!;
    const span = document.getElementById("mr")!;
    expect(head.getAttribute("data-xl")).toBe("T1#s4");
    over(head);
    expect(span.classList.contains("xl-hot")).toBe(true);
    out(head);
    expect(span.classList.contains("xl-hot")).toBe(false);
    // paper → panel jumps to it (no statement row shares the token)
    span.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();
    expect(document.querySelector(".xl-jump")).toBe(head);
    expect(head.classList.contains("xl-hot")).toBe(true);
  });

  it("prefers docUrl over the explorer, and refuses a non-http href", async () => {
    const ext = (over: Record<string, unknown>) => ({
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "Finset.sum_le_sum", cls: "env", depth: 1, external: true, fullName: "Causalean.Stat.MinimaxRate", ...over },
          ],
        }),
      },
    });

    mount(
      ext({ docUrl: "https://leanprover-community.github.io/mathlib4_docs/Finset.html#sum_le_sum" }),
      `<div class="formal-block" data-objid="T1">Theorem 1.</div>`,
    );
    await openBlock("T1");
    let link = bodyEl().querySelector("a.cv-ext-link") as HTMLAnchorElement;
    // docUrl wins even though fullName would also have resolved
    expect(link.getAttribute("href")).toBe(
      "https://leanprover-community.github.io/mathlib4_docs/Finset.html#sum_le_sum",
    );
    expect(link.textContent).toBe("docs ↗");
    expect(link.getAttribute("target")).toBe("_blank");

    // a non-http docUrl is not rendered; it falls back to the explorer link
    mount(ext({ docUrl: "javascript:alert(1)" }), `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    link = bodyEl().querySelector("a.cv-ext-link") as HTMLAnchorElement;
    expect(link.getAttribute("href")).toBe("/library/Stat/Rate#Causalean.Stat.MinimaxRate");
    expect(bodyEl().innerHTML).not.toContain("javascript:");
  });

  it("renders name and tag with NO link when the name map has no entry", async () => {
    const unknown = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "someUpstreamThing", cls: "env", depth: 1, external: true, fullName: "Nowhere.In.The.Map", module: "Mathlib/Foo.lean" },
          ],
        }),
      },
    };
    mount(unknown, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");

    const card = bodyEl().querySelector(".cv-card-external")!;
    expect(card.querySelector(".cv-decl")!.textContent).toBe("someUpstreamThing");
    expect(card.querySelector(".cv-tag-external")!.textContent).toBe("library declaration");
    // never a dead link
    expect(card.querySelector("a")).toBeNull();
    expect(card.textContent).not.toContain("↗");
  });

  it("renders no cited section when nothing is cited", async () => {
    mount(withViews, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".cv-sect-cited")).toBeNull();
    expect(bodyEl().textContent).not.toContain("Cited assumptions");
  });

  it("a paper component with no block and no entry degrades to plain text", async () => {
    const orphan = {
      ...withViews,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          componentViews: [
            { decl: "ghost", file: "C.lean", line: 1, statement: "", cls: "paper", paperObjId: "Z9", paperLabel: "Remark 9", depth: 1 },
          ],
        }),
      },
    };
    mount(orphan, `<div class="formal-block" data-objid="T1">Theorem 1.</div>`);
    await openBlock("T1");
    expect(bodyEl().querySelector(".cv-paper-chip")).toBeNull();
    expect(bodyEl().querySelector(".cv-paper-flat")!.textContent).toBe("ghost → Remark 9");
  });
});

describe("NL↔Lean crosslink tokens", () => {
  // `xl` / `data-xl` is a space-separated token list, like `class`: one row may
  // translate several binders, one phrase may cover several rows.
  const XL = {
    ...BASE,
    entries: [entry({})],
    snippets: {
      T1: snippet({
        structured: {
          sharedHyps: [
            { chip: "hyp", code: "hP : P x", xl: "h#1 h#2" },
            { chip: "hyp", code: "hQ : Q x", xl: "h#3" },
          ],
          conclusions: [{ hyps: [], code: "R x", xl: "goal#0" }],
        },
      }),
    },
  };
  const BLOCK = `<div class="formal-block" data-objid="T1">Theorem 1: if
      <span id="p1" data-xl="h#1">P holds</span> and
      <span id="p2" data-xl="h#2">x is regular</span> and
      <span id="p3" data-xl="h#3">Q holds</span>, then
      <span id="pg" data-xl="goal#0">R holds</span>.</div>`;

  const hot = (id: string) => document.getElementById(id)!.classList.contains("xl-hot");
  const fire = (el: Element, type: string) =>
    type === "mouseenter"
      ? over(el)
      : type === "mouseleave"
        ? out(el)
        : el.dispatchEvent(new Event(type, { bubbles: true }));

  /** Record scrollIntoView targets. happy-dom leaves the method undefined, so
   *  it is installed on the prototype and removed again afterwards. */
  type Scrolled = { el: Element; opts: ScrollIntoViewOptions };
  type Panned = { el: Element; opts: ScrollToOptions };
  const elProto = Element.prototype as unknown as Record<string, unknown>;
  const win = window as unknown as Record<string, unknown>;
  /** page-level scrolls (paper targets) */
  let scrolled: Scrolled[] = [];
  /** scroller-local scrolls (panel targets) — the panel body must move, the
   *  page must not, so these are recorded separately. */
  let panned: Panned[] = [];
  let originalSIV: unknown;
  let originalST: unknown;
  let originalMM: unknown;
  beforeEach(() => {
    scrolled = [];
    panned = [];
    originalSIV = elProto.scrollIntoView;
    elProto.scrollIntoView = function (this: Element, opts: ScrollIntoViewOptions) {
      scrolled.push({ el: this, opts });
    };
    originalST = elProto.scrollTo;
    elProto.scrollTo = function (this: Element, opts: ScrollToOptions) {
      panned.push({ el: this, opts });
    };
    originalMM = win.matchMedia;
  });
  afterEach(() => {
    elProto.scrollIntoView = originalSIV;
    elProto.scrollTo = originalST;
    win.matchMedia = originalMM;
  });
  /** The element a jump landed on, marked so it is visible after the scroll. */
  const jumpTarget = () => document.querySelector(".xl-jump");

  it("emits the token list verbatim on rows and on the ⊢ leaf", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    const rows = [...bodyEl().querySelectorAll(".ds-row")];
    expect(rows.map((r) => r.getAttribute("data-xl"))).toEqual(["h#1 h#2", "h#3"]);
    expect(bodyEl().querySelector(".ds-concl")!.getAttribute("data-xl")).toBe("goal#0");
  });

  it("hovering a MULTI-token row lights the union of its counterpart spans", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    const row = bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!;

    fire(row, "mouseenter");
    // both tokens resolve: h#1 → p1, h#2 → p2
    expect([hot("p1"), hot("p2")]).toEqual([true, true]);
    expect(row.classList.contains("xl-hot")).toBe(true);
    // …and nothing it does not name
    expect([hot("p3"), hot("pg")]).toEqual([false, false]);

    fire(row, "mouseleave");
    expect([hot("p1"), hot("p2")]).toEqual([false, false]);
    expect(row.classList.contains("xl-hot")).toBe(false);
  });

  it("a SINGLE-token body span still lights the multi-token row that covers it", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    const row = bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!;
    const other = bodyEl().querySelector('.ds-row[data-xl="h#3"]')!;

    // p2 names only h#2, which the two-token row contains — word match, not
    // whole-attribute equality.
    fire(document.getElementById("p2")!, "mouseenter");
    expect(row.classList.contains("xl-hot")).toBe(true);
    expect(other.classList.contains("xl-hot")).toBe(false);
    expect(hot("p2")).toBe(true);
    // p1 shares no token with p2, so it stays cold
    expect(hot("p1")).toBe(false);

    fire(document.getElementById("p2")!, "mouseleave");
    expect(row.classList.contains("xl-hot")).toBe(false);
  });

  it("clicking a panel row JUMPS to its counterpart in the paper", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    const row = bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!;

    fire(row, "click");
    // the first token-sharing element on the OTHER side, centred in the page
    expect(scrolled.length).toBe(1);
    expect(scrolled[0].el).toBe(document.getElementById("p1"));
    expect(scrolled[0].opts).toMatchObject({ behavior: "smooth", block: "center" });
    expect(jumpTarget()).toBe(document.getElementById("p1"));
    // a paper target needs no panel-local scroll
    expect(panned.length).toBe(0);

    // unpinning is not a navigation
    fire(row, "click");
    expect(scrolled.length).toBe(1);
    expect(jumpTarget(), "unpinning clears the jump marker").toBeNull();
  });

  it("clicking a paper span JUMPS to its counterpart inside the panel", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    const row = bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!;

    document.getElementById("p2")!.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();
    // The row is CENTERED in the panel's own scroller — and the page is never
    // scrolled, so the article stays where the reader left it.
    expect(jumpTarget()).toBe(row);
    expect(panned.length).toBe(1);
    expect(panned[0].el).toBe(bodyEl());
    expect(panned[0].opts.behavior).toBe("smooth");
    expect(typeof panned[0].opts.top).toBe("number");
    expect(scrolled.length, "a panel target must not scroll the page").toBe(0);
    // and the click did not repaint the panel out from under the pin
    expect(row.classList.contains("xl-hot")).toBe(true);
    expect(isOpen()).toBe(true);
  });

  it("a token with no counterpart scrolls nothing", async () => {
    mount(XL, `<div class="formal-block" data-objid="T1">Theorem 1, no annotations.</div>`);
    await openBlock("T1");
    fire(bodyEl().querySelector('.ds-row[data-xl="h#3"]')!, "click");
    expect(scrolled).toEqual([]);
    expect(panned).toEqual([]);
    expect(jumpTarget()).toBeNull();
  });

  it("honours prefers-reduced-motion", async () => {
    win.matchMedia = (q: string) => ({ matches: q.includes("reduced-motion"), media: q });
    mount(XL, BLOCK);
    await openBlock("T1");
    fire(bodyEl().querySelector('.ds-row[data-xl="h#3"]')!, "click");
    expect(scrolled.length).toBe(1);
    expect(scrolled[0].el).toBe(document.getElementById("p3"));
    expect(scrolled[0].opts.behavior).toBe("auto");
  });

  it("pinning a row pins its FULL token set until it is unpinned", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    const row = bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!;

    fire(row, "click");
    expect([hot("p1"), hot("p2")]).toEqual([true, true]);
    // a pin freezes the highlight: hovering elsewhere changes nothing
    fire(document.getElementById("p3")!, "mouseenter");
    expect(hot("p3")).toBe(false);
    expect([hot("p1"), hot("p2")]).toEqual([true, true]);

    fire(row, "click"); // same element again → unpin
    expect([hot("p1"), hot("p2"), hot("p3")]).toEqual([false, false, false]);
  });

  it("pins on the LIVE block's annotated span, but still opens on another block's", async () => {
    const two = {
      ...BASE,
      entries: [
        entry({}),
        entry({
          obj_id: "T2",
          paper_label: "Theorem 2",
          lean: { file: "B.lean", decl: "thm_two", decl_kind: "theorem", line: 3 },
        }),
      ],
      snippets: {
        T1: XL.snippets.T1,
        T2: snippet({ decl: "thm_two", file: "B.lean", line: 3, statement: "theorem thm_two : S" }),
      },
    };
    mount(
      two,
      `${BLOCK}<div class="formal-block" data-objid="T2">Theorem 2: <span id="q1" data-xl="s#1">S holds</span>.</div>`,
    );
    await openBlock("T1");
    const row = bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!;

    // A click on an annotated span of the block the panel is ALREADY showing is
    // a pin — the block's open handler must not also fire.
    document.getElementById("p1")!.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();
    expect(hot("p1")).toBe(true);
    expect(row.classList.contains("xl-hot")).toBe(true); // p1's token h#1 is in the row
    expect(hot("p2")).toBe(false); // p2 shares no token with p1
    // The very same row node is still mounted, so the panel was never rebuilt —
    // a repaint would have discarded the pin.
    expect(bodyEl().contains(row)).toBe(true);
    expect(document.getElementById("drawer-title")!.textContent).toContain("Theorem 1");

    // A click on a DIFFERENT block's annotated span still opens that block.
    document.getElementById("q1")!.dispatchEvent(new Event("click", { bubbles: true }));
    await flush();
    expect(document.getElementById("drawer-title")!.textContent).toContain("Theorem 2");
    expect(document.querySelector('[data-objid="T2"]')!.classList.contains("drawer-open")).toBe(true);
    expect(document.querySelector('[data-objid="T1"]')!.classList.contains("drawer-open")).toBe(false);
    // swapping the panel released the pin
    expect(hot("p1")).toBe(false);
  });

  it("lights from a CHILD of the row, and survives nested same-token carriers", async () => {
    // Regression, thm:overlap-adaptive-universal-hybrid. The Lean side nests:
    // a `.ds-sub` card and the `.ds-concl` leaf inside it carry the SAME token,
    // and the pointer never touches either directly — it is over the `.ds-code`
    // box that fills the row. Per-element mouseenter/mouseleave got both wrong,
    // so the Lean→NL direction looked dead while NL→Lean worked.
    const nested = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [],
            conclusions: [
              {
                hyps: [],
                intro: "∃ C_epsilon : ℝ,",
                sub: [
                  { hyps: [], code: "0 < C_epsilon", xl: "t#4" },
                  {
                    hyps: [],
                    // wrapper and leaf both carry t#11 — the production shape
                    xl: "t#11",
                    sub: [{ hyps: [], code: "worstCaseMSE ≤ max C_epsilon 4", xl: "t#11" }],
                  },
                ],
              },
            ],
          },
        }),
      },
    };
    mount(
      nested,
      `<div class="formal-block" data-objid="T1">Theorem 1:
         <span id="n11" data-xl="t#11">the selector bracket</span> and
         <span id="n4" data-xl="t#4">positivity</span>.</div>`,
    );
    await openBlock("T1");

    const leaf = [...bodyEl().querySelectorAll(".ds-concl[data-xl]")].find((e) =>
      (e.textContent ?? "").includes("worstCaseMSE"),
    )!;
    const wrapper = leaf.closest(".ds-sub")!;
    // CARRIER GRANULARITY: the token lives on the ⊢ leaf LINE, and the sub
    // container around it carries nothing — so a stray click in the container's
    // padding can no longer fall through to a broader token.
    expect(leaf.getAttribute("data-xl")).toBe("t#11");
    expect(wrapper.hasAttribute("data-xl")).toBe(false);

    // 1. the pointer enters the CODE BOX, never the annotated row itself
    const code = leaf.querySelector(".ds-code")!;
    over(code);
    expect(hot("n11"), "hovering the row's code box lights the prose").toBe(true);
    expect(hot("n4")).toBe(false);

    // 2. drifting within the same carrier (code box → the row around it) is not
    //    a leave: the pointer never left the thing it is highlighting
    out(code, leaf);
    expect(hot("n11"), "moving inside one carrier keeps it lit").toBe(true);

    // 3. drifting out of the leaf into the container around it now lights
    //    NOTHING rather than a broader token — the container is not a carrier
    moveTo(leaf, wrapper);
    expect(hot("n11"), "the container is not a carrier, so the pairing clears").toBe(false);
    expect(document.querySelectorAll(".xl-hot").length).toBe(0);

    // 4. and coming back onto the leaf re-lights exactly it
    moveTo(wrapper, code);
    expect(hot("n11")).toBe(true);
    out(code, null);
    expect(hot("n11")).toBe(false);
  });

  it("never emits a token on a card/sub/frame container", async () => {
    // The user-visible bug: clicking near the edge of Conclusion 1's ⊢ leaf
    // resolved up to the enclosing card and fired the ∃-frame's token, lighting
    // a much broader NL segment than the row aimed at.
    const framed = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [],
            conclusions: [
              {
                hyps: [],
                intro: "∃ C : ℝ,",
                xl: "frame",
                sub: [
                  { hyps: [], code: "0 < C", xl: "side" },
                  { hyps: [{ chip: "hyp", code: "hx : 0 < x" }], code: "Q x", xl: "claim" },
                ],
              },
            ],
          },
        }),
      },
    };
    mount(
      framed,
      `<div class="formal-block" data-objid="T1">
         <span id="f" data-xl="frame">there exist constants</span>
         <span id="s" data-xl="side">positive</span>
         <span id="c" data-xl="claim">the bound holds</span>.</div>`,
    );
    await openBlock("T1");

    // no container anywhere in the panel is a carrier
    for (const sel of [".ds-card", ".ds-sub", ".ds-lift", ".ds-structured", ".cv-card"]) {
      for (const el of bodyEl().querySelectorAll(sel)) {
        expect(el.hasAttribute("data-xl"), `${sel} must not carry a token`).toBe(false);
      }
    }
    // every carrier IS a content line, and none contains another carrier
    const carriers = [...bodyEl().querySelectorAll<HTMLElement>("[data-xl]")];
    expect(carriers.length).toBe(3);
    expect(carriers.every((el) => el.matches(".ds-row, .ds-concl, .ds-intro"))).toBe(true);
    for (const el of carriers) {
      expect(el.querySelector("[data-xl]"), "carriers must not nest").toBeNull();
    }
    // the frame's own token sits on its ∃ line
    expect(bodyEl().querySelector(".ds-intro")!.getAttribute("data-xl")).toBe("frame");

    // clicking the card's padding (its label, outside every row) hits nothing
    const label = bodyEl().querySelector(".ds-card > .ds-label")!;
    fire(label, "click");
    expect(document.querySelectorAll(".xl-hot").length, "card chrome is not clickable").toBe(0);
    expect(scrolled.length).toBe(0);

    // while the leaf itself still pairs precisely
    over(bodyEl().querySelector(".ds-card .ds-concl")!);
    expect([hot("c"), hot("f"), hot("s")]).toEqual([true, false, false]);
  });

  it("treats tokens as OPAQUE ids: no '#n' format is assumed anywhere", async () => {
    // v3 replaced "<objid>#<n>" with stable row ids. Nothing in the renderer
    // parses a token — they are only whitespace-split and compared — so the
    // whole machinery must behave identically on ids with no '#' at all.
    const ids = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [
              { chip: "hyp", code: "h : P x", xl: "row_7a2f1e overlap.hyp/2" },
              { chip: "hyp", code: "g : Q x", xl: "row_bb0c94" },
            ],
            conclusions: [{ hyps: [], code: "R x", xl: "goal~main" }],
          },
        }),
      },
    };
    mount(
      ids,
      `<div class="formal-block" data-objid="T1">If
         <span id="i1" data-xl="row_7a2f1e">P holds</span> and
         <span id="i2" data-xl="overlap.hyp/2">x overlaps</span> and
         <span id="i3" data-xl="row_bb0c94">Q holds</span> then
         <span id="i4" data-xl="goal~main">R holds</span>.</div>`,
    );
    await openBlock("T1");

    const row = bodyEl().querySelector('.ds-row[data-xl="row_7a2f1e overlap.hyp/2"]')!;
    // verbatim round trip: separators, dots and slashes are not touched
    expect(row.getAttribute("data-xl")).toBe("row_7a2f1e overlap.hyp/2");

    // union hover across a multi-token id row
    over(row);
    expect([hot("i1"), hot("i2")]).toEqual([true, true]);
    expect([hot("i3"), hot("i4")]).toEqual([false, false]);
    out(row);

    // reverse direction on a single id
    over(document.getElementById("i3")!);
    expect(bodyEl().querySelector('.ds-row[data-xl="row_bb0c94"]')!.classList.contains("xl-hot")).toBe(true);
    out(document.getElementById("i3")!);

    // pin + jump on an id-style conclusion token
    fire(bodyEl().querySelector('.ds-concl[data-xl="goal~main"]')!, "click");
    expect(hot("i4")).toBe(true);
    expect(scrolled.length).toBe(1);
    expect(scrolled[0].el).toBe(document.getElementById("i4"));
  });

  it("ignores the sibling data-xl-* attributes on body display segments", async () => {
    // v3 adds `data-xl-decl` and a bare `data-xl-presentation` to display
    // segments. Attribute selectors match whole names, so `[data-xl]` must not
    // pick these up — a presentation-only segment is NOT a crosslink carrier,
    // and treating one as a carrier would light on hover with nothing to pair.
    const data = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "h : P x", id: "r1", xl: "T1#r1" }],
            conclusions: [{ hyps: [], code: "Q x", id: "r2", xl: "T1#r2" }],
          },
        }),
      },
    };
    mount(
      data,
      `<div class="formal-block" data-objid="T1">If
         <span id="real" data-xl="T1#r1">P holds</span>, then
         <span id="pres" data-xl-presentation>a restatement</span> and
         <span id="decl" data-xl-decl="someDecl">a named decl</span>.</div>`,
    );
    await openBlock("T1");

    // neither sibling attribute makes an element a carrier
    const block = document.querySelector('[data-objid="T1"]')!;
    expect([...block.querySelectorAll("[data-xl]")].map((e) => e.id)).toEqual(["real"]);

    // hovering the paired row lights only the real carrier
    over(bodyEl().querySelector(".ds-row")!);
    expect(hot("real")).toBe(true);
    expect(hot("pres")).toBe(false);
    expect(hot("decl")).toBe(false);
    out(bodyEl().querySelector(".ds-row")!);

    // and hovering a presentation-only segment is a no-op, not a stray clear
    over(document.getElementById("pres")!);
    expect(document.querySelectorAll(".xl-hot").length).toBe(0);
  });

  it("jumps to the statement ROW, not the card head that renders above it", async () => {
    // Reproduced on thm:sharp-minimax-fixed-interior: a prose span carries the
    // row tokens it translates PLUS a display-segment token (#s8) that also
    // sits on the anchor's cv-head. The head is the panel's first carrier in
    // DOM order, so every click landed on "sharp_minimax_fixed_interior"
    // instead of the hypothesis row the reader aimed at.
    const shaped = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [
              { chip: "hyp", code: "he0 : 0 < epsilon", xl: "T1#r11" },
              { chip: "hyp", code: "he1 : epsilon < 1 / 2", xl: "T1#r12" },
            ],
            conclusions: [{ hyps: [], code: "minimaxRisk n d epsilon ≤ C / n", xl: "T1#r14" }],
          },
          componentViews: [
            // the anchor head carries the display-segment tokens, and renders
            // above every row
            { decl: "sharp_minimax_fixed_interior", file: "S.lean", line: 3, statement: "theorem sharp_minimax_fixed_interior : True", cls: "anchor", depth: 0, xl: "T1#s8 T1#s10" },
          ],
        }),
      },
    };
    mount(
      shaped,
      `<div class="formal-block" data-objid="T1">
         <span id="mix" data-xl="T1#r11 T1#r12 T1#s8">for every law with overlap</span>.</div>`,
    );
    await openBlock("T1");

    const head = bodyEl().querySelector(".cv-card-anchor > .cv-head")!;
    const rows = [...bodyEl().querySelectorAll(".ds-row")];
    // the shape under test: the head really does share a token AND come first
    expect(head.getAttribute("data-xl")).toBe("T1#s8 T1#s10");
    const carriers = [...bodyEl().querySelectorAll("[data-xl]")];
    expect(carriers[0]).toBe(head);

    fire(document.getElementById("mix")!, "click");
    await flush();
    // the jump lands on the first matching statement row, never the head
    expect(jumpTarget()).toBe(rows[0]);
    expect(jumpTarget()).not.toBe(head);
    expect(jumpTarget()!.querySelector(".ds-code")!.textContent).toBe("he0 : 0 < epsilon");
    // centered inside the panel, page untouched
    expect(panned.map((p) => p.el)).toEqual([bodyEl()]);
    expect(scrolled.length).toBe(0);
    // highlighting is unchanged: every token-sharing element still lights
    expect(head.classList.contains("xl-hot")).toBe(true);
    expect(rows[0].classList.contains("xl-hot")).toBe(true);
    expect(rows[1].classList.contains("xl-hot")).toBe(true);
  });

  it("falls back to the card head when NO row shares the token", async () => {
    // A pure display→decl link on a definition with no rows of its own: the
    // declaration card is then genuinely the right destination.
    const rowless = {
      ...BASE,
      entries: [entry({})],
      snippets: {
        T1: snippet({
          structured: {
            sharedHyps: [{ chip: "hyp", code: "h : P", xl: "T1#r1" }],
            conclusions: [{ hyps: [], code: "Q", xl: "T1#r2" }],
          },
          componentViews: [
            { decl: "minimaxRate", file: "M.lean", line: 8, statement: "def minimaxRate : ℝ := 0", cls: "env", depth: 1, xl: "T1#s4" },
          ],
        }),
      },
    };
    mount(
      rowless,
      `<div class="formal-block" data-objid="T1">
         <span id="only-decl" data-xl="T1#s4">the minimax rate</span>.</div>`,
    );
    await openBlock("T1");

    const envHead = bodyEl().querySelector(".cv-card-env > .cv-head")!;
    fire(document.getElementById("only-decl")!, "click");
    await flush();
    expect(jumpTarget()).toBe(envHead);
    expect(panned.map((p) => p.el)).toEqual([bodyEl()]);
    expect(scrolled.length).toBe(0);
  });

  it("panel → paper jump order is untouched by the row preference", async () => {
    mount(XL, BLOCK);
    await openBlock("T1");
    // clicking a panel row still jumps to the first token-sharing prose span
    fire(bodyEl().querySelector('.ds-row[data-xl="h#1 h#2"]')!, "click");
    expect(scrolled.length).toBe(1);
    expect(scrolled[0].el).toBe(document.getElementById("p1"));
  });

  it("stays inert when the payload carries no tokens", async () => {
    mount(
      { ...BASE, entries: [entry({})], snippets: { T1: snippet({}) } },
      `<div class="formal-block" data-objid="T1">Theorem 1.</div>`,
    );
    await openBlock("T1");
    expect(bodyEl().querySelector("[data-xl]")).toBeNull();
    expect(document.querySelectorAll(".xl-hot").length).toBe(0);
  });
});

describe("close", () => {
  it("Esc closes the panel and returns focus to the opening block", async () => {
    mount(
      { ...BASE, entries: [entry({})], snippets: { T1: snippet({}) } },
      `<div class="formal-block" data-objid="T1">Theorem 1.</div>`,
    );
    const block = await openBlock("T1");
    expect(isOpen()).toBe(true);
    expect(block.classList.contains("drawer-open")).toBe(true);

    document.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
    expect(isOpen()).toBe(false);
    expect(drawerEl().getAttribute("aria-hidden")).toBe("true");
    expect(block.classList.contains("drawer-open")).toBe(false);
    expect(document.activeElement).toBe(block);
  });

  it("the ✕ button closes too", async () => {
    mount(
      { ...BASE, entries: [entry({})], snippets: { T1: snippet({}) } },
      `<div class="formal-block" data-objid="T1">Theorem 1.</div>`,
    );
    await openBlock("T1");
    (document.getElementById("drawer-close") as HTMLElement).dispatchEvent(
      new Event("click", { bubbles: true }),
    );
    expect(isOpen()).toBe(false);
  });
});
