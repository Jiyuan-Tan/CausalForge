import { beforeEach, describe, expect, it } from "vitest";
import { mkdtempSync, mkdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  clearRetrievalCache,
  createRetrieval,
  fuseRankedListsRrf,
  rankPremisesFromProofRefs,
  parseF1Items,
  expandQuery,
} from "../src/formalization/reuse_retrieval.js";
import { reuseCandidateBlock } from "../src/formalization/reuse_render.js";

/** A fixture Causalean root with a hand-built index covering the cases we care about. */
function fixtureRoot(): string {
  const root = mkdtempSync(join(tmpdir(), "reuse-"));
  mkdirSync(join(root, "doc", "library_review"), { recursive: true });
  const entries = [
    {
      name: "Causalean.PO.ID.ConditionalExchangeability",
      kind: "def",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 10,
      statement: "(s : POSystem) → Prop",
      doc: "Conditional exchangeability of the potential outcomes given covariates.\n\nMeasure-theoretic note.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // same concept, but sorried — must rank below the clean one on equal overlap
      name: "Causalean.PO.ID.ConditionalExchangeabilityWeak",
      kind: "def",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 40,
      statement: "(s : POSystem) → Prop",
      doc: "Conditional exchangeability of the potential outcomes given covariates.\n\nWeak variant.",
      refs: [],
      axioms: [],
      usesSorry: true,
    },
    {
      name: "Causalean.PO.ID.Overlap",
      kind: "def",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 70,
      statement: "(s : POSystem) → Prop",
      doc: "Overlap (positivity): the propensity score is bounded away from 0 and 1.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.PO.ID.Exact.ate_backdoor",
      kind: "theorem",
      module: "Causalean.PO.ID.Exact.Backdoor",
      file: "Causalean/PO/ID/Exact/Backdoor.lean",
      line: 100,
      statement: "ate s = ∫ x, condExp s x ∂μ",
      doc: "The ATE equals the backdoor adjustment integral.",
      refs: [],
      proofRefs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // noise: name shares the connective word "conditional" with the ignorability
      // alias phrase, but is unrelated. Must NOT surface for "ignorability".
      name: "Causalean.PO.ID.Exact.IV.conditionalMarginResponse",
      kind: "def",
      module: "Causalean.PO.ID.Exact.IV",
      file: "Causalean/PO/ID/Exact/IV.lean",
      line: 3,
      statement: "(s : POSystem) → ℝ",
      doc: "Variable-intensity IV margin response.",
      refs: [],
      proofRefs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // an auto-generated instance — must be penalized below a real def on equal match.
      name: "Causalean.PO.ID.instOverlapWitness",
      kind: "instance",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 90,
      statement: "(s : POSystem) → Prop",
      doc: "Overlap positivity instance.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // qualified identifier in the statement — exercises symbolSet dot-splitting.
      name: "Causalean.PO.indep_lemma",
      kind: "theorem",
      module: "Causalean.PO.Indep",
      file: "Causalean/PO/Indep.lean",
      line: 1,
      statement: "ProbabilityTheory.CondIndepFun m h Y A",
      doc: "Conditional independence of Y and A.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Stat.Minimax.foo_rate",
      kind: "theorem",
      module: "Causalean.Stat.Minimax.Rate",
      file: "Causalean/Stat/Minimax/Rate.lean",
      line: 5,
      statement: "minimaxRate s = c",
      doc: "A minimax rate result.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // generic-token-heavy name: "treatment"+"effect" must NOT outrank a single
      // specific "quantile" hit (the fractional name-weighting guard).
      name: "Causalean.Panel.EventStudy.TreatmentEffectFixed",
      kind: "def",
      module: "Causalean.Panel.EventStudy",
      file: "Causalean/Panel/EventStudy.lean",
      line: 1,
      statement: "(s : Panel) → ℝ",
      doc: "Fixed treatment effect of an event-study panel.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Stat.Quantile.quantile_le_iff",
      kind: "theorem",
      module: "Causalean.Stat.Quantile",
      file: "Causalean/Stat/Quantile.lean",
      line: 1,
      statement: "quantile p ≤ x ↔ p ≤ cdf x",
      doc: "Characterization of the quantile by the cdf.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // Matchable only by symbol shape (math operators ⨆ ∈ ⊥), which word-tokenization
      // strips — so the type-signature pass surfaces it where concept mode cannot. Its
      // name/doc/word-tokens are deliberately disjoint from the probe item's prose.
      name: "Causalean.Geo.bigsup_perp",
      kind: "theorem",
      module: "Causalean.Geo.Lattice",
      file: "Causalean/Geo/Lattice.lean",
      line: 1,
      statement: "⨆ i ∈ s, f i ⊥ g",
      doc: "Indexed supremum orthogonality witness.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
  ];
  writeFileSync(
    join(root, "doc", "library_index.json"),
    JSON.stringify({ commit: "deadbeef", toolchain: "t", entries }),
  );
  writeFileSync(
    join(root, "doc", "library_review", "PO.json"),
    JSON.stringify({ headline_theorems: [], reviews: [], flags: [] }),
  );
  return root;
}

beforeEach(() => clearRetrievalCache());

describe("alias expansion", () => {
  it("expands ignorability to the exchangeability family + PO/ID module", () => {
    const e = expandQuery("ignorability of potential outcomes");
    expect(e.terms).toContain("exchangeability");
    expect(e.terms).toContain("unconfoundedness");
    expect(e.modules).toContain("Causalean/PO/ID/");
  });

  it("does not inject the ambiguous bare 'lp' token (Lebesgue Lp collision)", () => {
    const e = expandQuery("local projection impulse response");
    expect(e.terms).toContain("local projection");
    expect(e.terms).not.toContain("lp");
  });

  it("bare 'adjustment' does not bridge frontdoor → backdoor", () => {
    // "adjustment" alone is generic (frontdoor/covariate/backdoor all use it); a frontdoor
    // query must not pull in the backdoor synonym set and demote `frontdoorAdjustment`.
    const e = expandQuery("frontdoor adjustment");
    expect(e.concepts).toContain("frontdoor adjustment");
    expect(e.concepts).not.toContain("backdoor adjustment");
  });
});

describe("concept mode (synonym bridge)", () => {
  it("query 'ignorability' surfaces ConditionalExchangeability via alias", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "concept", title: "ignorability" });
    expect(hits[0].name).toBe("Causalean.PO.ID.ConditionalExchangeability");
    expect(hits[0].matchedVia).toBe("alias");
  });

  it("a clean decl outranks an equally-matching usesSorry decl", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "concept", title: "conditional exchangeability" });
    const clean = hits.findIndex((h) => h.name.endsWith("ConditionalExchangeability"));
    const weak = hits.findIndex((h) => h.name.endsWith("ConditionalExchangeabilityWeak"));
    expect(clean).toBeGreaterThanOrEqual(0);
    expect(weak).toBeGreaterThan(clean);
  });

  it("a connective alias token (conditional) on a name does not surface unrelated decls", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "concept", title: "ignorability" });
    expect(hits.find((h) => h.name.endsWith("conditionalMarginResponse"))).toBeUndefined();
    expect(hits[0].name).toBe("Causalean.PO.ID.ConditionalExchangeability");
  });

  it("query 'positivity' surfaces Overlap", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "concept", title: "positivity" });
    expect(hits[0].name).toBe("Causalean.PO.ID.Overlap");
  });

  it("a single specific name hit outranks several generic name hits", () => {
    // "treatment"+"effect" are generic; "quantile" is specific. The quantile decl must win.
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "concept", title: "quantile treatment effect" });
    expect(hits[0].name).toBe("Causalean.Stat.Quantile.quantile_le_iff");
    const q = hits.findIndex((h) => h.name.endsWith("quantile_le_iff"));
    const te = hits.findIndex((h) => h.name.endsWith("TreatmentEffectFixed"));
    expect(te === -1 || q < te).toBe(true);
  });

  it("an auto-instance ranks below a real def on the same match", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "concept", title: "overlap" });
    const def = hits.findIndex((h) => h.name === "Causalean.PO.ID.Overlap");
    const inst = hits.findIndex((h) => h.name.endsWith("instOverlapWitness"));
    expect(def).toBeGreaterThanOrEqual(0);
    expect(inst === -1 || inst > def).toBe(true);
  });
});

describe("typePattern + goal modes (vocabulary-independent)", () => {
  it("typePattern '∫ condExp' surfaces the backdoor integral lemma", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "typePattern", pattern: "∫ condExp _" });
    expect(hits[0].name).toBe("Causalean.PO.ID.Exact.ate_backdoor");
  });

  it("a pattern of only ubiquitous operators matches nothing", () => {
    const r = createRetrieval(fixtureRoot());
    expect(r.search({ mode: "typePattern", pattern: "→ ∀ ≤ ∈" })).toEqual([]);
  });

  it("typePattern matches a qualified identifier (dot-split)", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "typePattern", pattern: "CondIndepFun" });
    expect(hits[0].name).toBe("Causalean.PO.indep_lemma");
  });

  it("goal mode ranks the lemma whose conclusion shares the goal head", () => {
    const r = createRetrieval(fixtureRoot());
    const hits = r.search({ mode: "goal", goalType: "ate s = ∫ x, condExp s x ∂μ" });
    expect(hits[0].name).toBe("Causalean.PO.ID.Exact.ate_backdoor");
  });

  it("goal mode without semantic returns the symbol-overlap list unchanged", () => {
    const r = createRetrieval(fixtureRoot());
    const noSemantic = r.search({ mode: "goal", goalType: "ate s = ∫ x, condExp s x ∂μ" }, { topK: 3 });
    const explicitNoSemantic = r.search(
      { mode: "goal", goalType: "ate s = ∫ x, condExp s x ∂μ" },
      { topK: 3, semantic: undefined },
    );
    expect(explicitNoSemantic).toEqual(noSemantic);
    expect(noSemantic.map((h) => h.name)).toEqual(["Causalean.PO.ID.Exact.ate_backdoor"]);
  });
});

describe("goal-mode hybrid helpers", () => {
  it("weights neighbour proofRefs by 1/(i+2) and ranks accumulated premises", () => {
    const out = rankPremisesFromProofRefs([
      { name: "Neighbour.one", proofRefs: ["Premise.alpha", "Premise.shared"] },
      { name: "Neighbour.two", proofRefs: ["Premise.beta", "Premise.shared"] },
      { name: "Neighbour.three", proofRefs: ["Premise.alpha"] },
    ]);

    expect(out.map((p) => p.name)).toEqual(["Premise.shared", "Premise.alpha", "Premise.beta"]);
    expect(out.find((p) => p.name === "Premise.shared")!.score).toBeCloseTo(1 / 2 + 1 / 3, 5);
    expect(out.find((p) => p.name === "Premise.alpha")!.score).toBeCloseTo(1 / 2 + 1 / 4, 5);
    expect(out.find((p) => p.name === "Premise.beta")!.score).toBeCloseTo(1 / 3, 5);
  });

  it("fuses ranked premise and symbol lists with RRF k0=10", () => {
    const out = fuseRankedListsRrf(
      [
        ["B", "shared", "A"],
        ["A", "shared", "C"],
      ],
      10,
      4,
    );

    expect(out.map((x) => x.name)).toEqual(["A", "shared", "B", "C"]);
    expect(out.find((x) => x.name === "A")!.score).toBeCloseTo(1 / 12 + 1 / 10, 5);
    expect(out.find((x) => x.name === "shared")!.score).toBeCloseTo(1 / 11 + 1 / 11, 5);
  });
});

describe("cluster filter", () => {
  it("a Stat decl is excluded by the exactid cluster but kept by the stat cluster", () => {
    const r = createRetrieval(fixtureRoot());
    const q = { mode: "concept", title: "minimax" } as const;
    expect(r.search(q, { cluster: "exactid" }).find((h) => h.name.endsWith("foo_rate"))).toBeUndefined();
    expect(r.search(q, { cluster: "stat" }).find((h) => h.name.endsWith("foo_rate"))).toBeDefined();
  });
});

describe("F1 plan parser", () => {
  it("extracts P-/L- items with titles and bodies, stopping at the next header", () => {
    const md = [
      "## 4. P-block",
      "### P-1: TwoCellSetup at `x`",
      "Some body text.",
      "### P-2: ConditionalExchangeability",
      "Independence of outcomes.",
      "## 5. L-block",
      "### L-3a: Rectangle minimization",
      "Affine functional.",
      "### T-2 — main theorem",
      "not an item",
    ].join("\n");
    const items = parseF1Items(md);
    expect(items.map((i) => i.label)).toEqual(["P-1", "P-2", "L-3a"]);
    expect(items[1].title).toBe("ConditionalExchangeability");
    expect(items[0].body).toContain("Some body text");
  });

  it("parses the bold-inline research dialect (P/L/A on one line)", () => {
    const md = [
      "## 4. P-block",
      "**P-1 (Propensity clip).** `e_λ(x)=e(x)∨λ`. Depends on S-3.",
      "## 4a. Assumption blocks (A-k)",
      "**A-1 (Identification).** Consistency and conditional exchangeability.",
      "## 5. L-block",
      "**L-2 (Rectangle minimization).** Affine functional argmin.",
    ].join("\n");
    const items = parseF1Items(md);
    expect(items.map((i) => i.label)).toEqual(["P-1", "A-1", "L-2"]);
    expect(items[0].title).toBe("Propensity clip");
    expect(items[1].title).toBe("Identification");
    expect(items[1].body).toContain("conditional exchangeability");
  });

  it("does not mistake inline math parens for the title (em-dash dialect)", () => {
    const items = parseF1Items("- **L-4 — Description of `H_a(B)` via the ball.** body");
    expect(items[0].label).toBe("L-4");
    expect(items[0].title).toBe("Description of H_a(B) via the ball");
  });

  it("returns [] when there are no P/L headers", () => {
    expect(parseF1Items("# Title\n\nNo blocks here.")).toEqual([]);
  });
});

describe("brief candidate block", () => {
  it("renders the contract + candidates for F1 items", () => {
    const root = fixtureRoot();
    const md = ["### P-1: Ignorability of potential outcomes", "Independence given covariates."].join("\n");
    const mdPath = join(root, "plan.md");
    writeFileSync(mdPath, md);
    const block = reuseCandidateBlock(root, mdPath, null);
    expect(block).toContain("CAUSALEAN REUSE CANDIDATES");
    expect(block).toContain("CONTRACT");
    expect(block).toContain("Causalean.PO.ID.ConditionalExchangeability");
    expect(block).toContain("P-1 — Ignorability of potential outcomes");
  });

  it("type-signature pass surfaces a symbol-shaped fit that concept mode misses", () => {
    // Prose words (lattice/join/family) match nothing; the backtick operators ⨆ ∈ ⊥ do.
    const root = fixtureRoot();
    const md = ["### P-1: Lattice join", "The join `⨆ i ∈ s, f i ⊥ g` of the family."].join("\n");
    const mdPath = join(root, "sym.md");
    writeFileSync(mdPath, md);
    const block = reuseCandidateBlock(root, mdPath, null);
    // the rendered section header (distinct from the CONTRACT's mention of the tier)
    expect(block).toContain("(vocabulary-independent — confirm the shape fits)");
    expect(block).toContain("Causalean.Geo.bigsup_perp");
  });

  it("no type-signature section for an item without Lean/math backticks", () => {
    const root = fixtureRoot();
    const md = ["### P-1: Ignorability", "Independence given covariates, no symbols here."].join("\n");
    const mdPath = join(root, "prose.md");
    writeFileSync(mdPath, md);
    const block = reuseCandidateBlock(root, mdPath, null);
    expect(block).not.toContain("(vocabulary-independent — confirm the shape fits)");
  });

  it("a large plan never starves later items on a hard cap", () => {
    // A 30-item plan must give EVERY item a line, not exhaust a fixed budget on the first few.
    const root = fixtureRoot();
    const md = Array.from({ length: 30 }, (_, i) =>
      `### P-${i + 1}: Overlap positivity item ${i + 1}\nThe propensity score is bounded.`,
    ).join("\n");
    const mdPath = join(root, "big.md");
    writeFileSync(mdPath, md);
    const block = reuseCandidateBlock(root, mdPath, null);
    expect(block).not.toContain("cap"); // no "candidate cap … reached" message
    // the final item is present AND received a real candidate, not a starvation note
    expect(block).toContain("P-30 — Overlap positivity item 30");
    const tail = block.slice(block.indexOf("P-30 —"));
    expect(tail).toContain("Causalean.PO.ID.Overlap");
  });
});

describe("graceful degradation", () => {
  it("missing index → empty results, no throw", () => {
    const r = createRetrieval(join(tmpdir(), "does-not-exist-" + "x"));
    expect(r.library).toBeNull();
    expect(r.search({ mode: "concept", title: "ignorability" })).toEqual([]);
    expect(r.get("Whatever")).toBeNull();
  });

  it("missing F1 artifact / index → empty candidate block", () => {
    expect(reuseCandidateBlock(join(tmpdir(), "nope-root"), join(tmpdir(), "nope.md"), null)).toBe("");
  });
});
