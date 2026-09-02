import { describe, expect, it } from "vitest";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { bundleRoots } from "../src/lib/config.js";
import type { NlBlock } from "../src/lib/nlLinks.js";
import {
  enrichSnippets,
  resolveDisplayLinks,
  structurePropRecordView,
  structureStatementView,
  type ComponentView,
  type ConclusionCard,
  type DeclSource,
  type PaperLeanEntry,
  type PaperLeanSnippet,
} from "../src/lib/paperLean.js";

// ---------------------------------------------------------------------------
// A miniature stand-in for the discrete-ATE paper's module index: a composite
// "Definition 9" whose estimator is defined three layers deep, and a
// "Definition 7" that owns one of the pieces Definition 9 lists. Synthetic on
// purpose — the real bundle is multi-MB and this must stay a unit test.
// ---------------------------------------------------------------------------

interface Decl {
  name: string;
  kind: string;
  file: string;
  line: number;
  source: string;
  refs: string[];
  proofRefs: string[];
  usesSorry: boolean;
  extRefs: { n: string; m: string }[];
}

const decl = (
  name: string,
  line: number,
  source: string,
  refs: string[] = [],
  proofRefs: string[] = [],
  kind = "def",
  usesSorry = false,
): Decl => ({
  name: `Demo.${name}`,
  kind,
  file: "Demo/Estimator.lean",
  line,
  source,
  refs,
  proofRefs,
  usesSorry,
  extRefs: [],
});

const OBS = decl("Obs", 10, "abbrev Obs (d : ℕ) := Fin d × Bool × Bool", [], [], "abbrev");
const SPLIT_INDICES = decl(
  "splitIndices",
  20,
  "def splitIndices (n : ℕ) (j : Fin 2) : Finset (Fin n) :=\n  Finset.univ.filter (fun i => i.1 < n / 2)",
);
const SPLIT_CELL_COUNT = decl(
  "splitCellCount",
  30,
  "def splitCellCount {n d : ℕ} (sample : Fin n → Obs d) (j : Fin 2) : ℕ :=\n  ((splitIndices n j).filter (fun i => sample i = default)).card",
  ["Demo.Obs"],
  ["Demo.splitIndices"],
);
const EMPIRICAL_RATIO_CELL = decl(
  "empiricalRatioCell",
  40,
  "noncomputable def empiricalRatioCell {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=\n  (splitCellCount sample 1 : ℝ)",
  ["Demo.Obs"],
  ["Demo.splitCellCount"],
);
const HEAVY_CELLS = decl(
  "heavyCells",
  50,
  "noncomputable def heavyCells {n d : ℕ} (sample : Fin n → Obs d) : Finset (Fin d) := Finset.univ",
  ["Demo.Obs"],
);
const LIGHT_CELLS = decl(
  "lightCells",
  60,
  "noncomputable def lightCells {n d : ℕ} (sample : Fin n → Obs d) : Finset (Fin d) := (heavyCells sample)ᶜ",
  ["Demo.Obs"],
  ["Demo.heavyCells"],
);
const HEAVY_CONTRIBUTION = decl(
  "heavyContribution",
  70,
  "noncomputable def heavyContribution {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=\n  ∑ k ∈ heavyCells sample, empiricalRatioCell sample",
  ["Demo.Obs"],
  ["Demo.heavyCells", "Demo.empiricalRatioCell"],
);
const LIGHT_CONTRIBUTION = decl(
  "lightContribution",
  80,
  "noncomputable def lightContribution {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=\n  ∑ k ∈ lightCells sample, (0 : ℝ)",
  ["Demo.Obs"],
  ["Demo.lightCells"],
);
const HYBRID = decl(
  "hybridEstimator",
  90,
  "/-- Universally calibrated hybrid. -/\nnoncomputable def hybridEstimator {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=\n  max (-1) (min 1 (heavyContribution sample + lightContribution sample))",
  ["Demo.Obs"],
  ["Demo.heavyContribution", "Demo.lightContribution"],
);

const LIB: Decl[] = [
  OBS,
  SPLIT_INDICES,
  SPLIT_CELL_COUNT,
  EMPIRICAL_RATIO_CELL,
  HEAVY_CELLS,
  LIGHT_CELLS,
  HEAVY_CONTRIBUTION,
  LIGHT_CONTRIBUTION,
  HYBRID,
];

const DEF9: PaperLeanEntry = {
  obj_id: "def:hybrid-estimator-handle",
  env: "definitionv",
  paper_label: "Definition 9",
  lean: null,
  status: "matched",
};
const DEF7: PaperLeanEntry = {
  obj_id: "def:sample-splits",
  env: "definitionv",
  paper_label: "Definition 7",
  lean: { decl: "Demo.splitCellCount", decl_kind: "def" },
  status: "matched",
};

const DEF9_SNIPPET: PaperLeanSnippet = {
  decl: "(composite)",
  file: "Demo/Estimator.lean",
  line: 0,
  statement: "",
  components: [
    { label: "Demo.hybridEstimator", statement: HYBRID.source },
    { label: "Obs", statement: OBS.source },
    { label: "Demo.splitCellCount", statement: SPLIT_CELL_COUNT.source },
  ],
};
const DEF7_SNIPPET: PaperLeanSnippet = {
  decl: "Demo.splitCellCount",
  file: "Demo/Estimator.lean",
  line: 30,
  statement: SPLIT_CELL_COUNT.source,
};

/** Enriches, and adds two lookups the assertions below want: an entry's views
 *  by short decl name, and the shared-table row a view's `key` points at. */
const run = (
  entries: PaperLeanEntry[],
  snippets: Record<string, PaperLeanSnippet>,
  lib: readonly unknown[] | null = LIB,
  nlLinks: Record<string, NlBlock> | null = null,
) => {
  const result = enrichSnippets({ entries, snippets, paperLibEntries: lib, nlLinks });
  return {
    ...result,
    views: (objId: string): Record<string, ComponentView> =>
      Object.fromEntries((result.snippets[objId]?.componentViews ?? []).map((v) => [v.decl, v])),
    /** A view's source, wherever it lives: the shared table, or inline. */
    sourceOf: (v: ComponentView): DeclSource | undefined =>
      v.key ? result.declSources[v.key] : { file: v.file!, line: v.line!, statement: v.statement! },
  };
};

/** An artifact block with everything defaulted, so a test states only what it
 *  is about. The digest is irrelevant here: `enrichSnippets` consumes blocks
 *  the loader has already validated against the body. */
const block = (over: Partial<NlBlock> = {}): NlBlock => ({
  structured: null,
  segments: [],
  assignments: [],
  displayLinks: [],
  digest: "test-digest",
  byteLength: 0,
  ...over,
});

/** The phantom-row shape: a card that only branches renders nothing of its
 *  own, so it has no id and is never assigned. */
const branchingCard = (): NlBlock["structured"] => ({
  sharedHyps: [{ chip: "hyp", code: "0 < n", id: "h1" }],
  conclusions: [
    { hyps: [], sub: [{ hyps: [], code: "P n", id: "c1" }, { hyps: [], code: "Q n", id: "c2" }] },
  ],
});

const byDecl = (views: ComponentView[] | undefined) =>
  Object.fromEntries((views ?? []).map((v) => [v.decl, v]));

describe("component closure", () => {
  const enriched = run([DEF9, DEF7], {
    "def:hybrid-estimator-handle": DEF9_SNIPPET,
    "def:sample-splits": DEF7_SNIPPET,
  });
  const def9 = enriched.snippets["def:hybrid-estimator-handle"];

  it("uses a composite's principal Prop record when the optional artifact is absent", () => {
    const source = `structure ExperimentClass (n : ℕ) (P : Law) : Prop where
      positive : 0 < n
      sampling : IidSampling P`;
    const EXPERIMENT = decl("ExperimentClass", 110, source, [], [], "structure");
    const IID = decl("IidSampling", 120, "def IidSampling (P : Law) : Prop := Good P");
    const result = run(
      [{ obj_id: "def:experiment", env: "definitionv", paper_label: "Definition 2", lean: null, status: "matched" }],
      {
        "def:experiment": {
          decl: "(composite)",
          file: "Demo/Estimator.lean",
          line: 0,
          statement: "",
          components: [
            { label: "Demo.ExperimentClass", statement: source },
            { label: "Demo.IidSampling", statement: IID.source },
          ],
        },
      },
      [...LIB, EXPERIMENT, IID],
      null,
    );
    expect(result.snippets["def:experiment"].structured?.sharedHyps.map((h) => h.code)).toEqual([
      "(n : ℕ)",
      "(P : Law)",
    ]);
    expect(result.snippets["def:experiment"].structured?.conclusions.map((c) => c.code)).toEqual([
      "positive : 0 < n",
      "sampling : IidSampling P",
    ]);
  });

  // The bug this whole module exists for: the drawer showed `hybridEstimator`
  // (`… heavyContribution sample + lightContribution sample …`) and neither
  // contribution, so the definition could not be checked without the sources.
  it("pulls the estimator's whole definitional chain into Definition 9", () => {
    const views = byDecl(def9.componentViews);
    for (const name of [
      "heavyContribution",
      "lightContribution",
      "heavyCells",
      "lightCells",
      "empiricalRatioCell",
    ]) {
      expect(views[name], `${name} missing from the closure`).toBeDefined();
      expect(views[name].cls).toBe("lean_only");
      // The view carries only a key; the source itself is held once per paper.
      expect(views[name].key).toBe(`Demo.${name}`);
      expect(views[name].statement).toBeUndefined();
      expect(enriched.declSources[`Demo.${name}`].statement).toBe(
        LIB.find((d) => d.name === `Demo.${name}`)!.source,
      );
    }
    expect(views.heavyContribution.depth).toBe(1);
    expect(views.lightContribution.depth).toBe(1);
    expect(views.heavyCells.depth).toBe(2);
    expect(views.empiricalRatioCell.depth).toBe(2);
  });

  // Verified against the real index: `refs` is the elaborated TYPE's
  // references, `proofRefs` the value's. For a `def` the value IS the
  // statement, so `hybridEstimator`'s `refs` (just `Obs`) is not enough.
  it("treats a def's proofRefs as statement references but a theorem's as proof-only", () => {
    const views = byDecl(def9.componentViews);
    expect(views.Obs).toBeDefined(); // from `refs`
    expect(views.heavyContribution).toBeDefined(); // from `proofRefs`

    // `proofOnly` is reachable ONLY as a proof reference of the theorem — it
    // appears in no statement anywhere — so it must never enter the drawer.
    const proofOnly = decl("proofOnly", 99, "theorem proofOnly : True := trivial", [], [], "theorem");
    const thm = decl(
      "hybrid_bounded",
      100,
      "theorem hybrid_bounded {n d : ℕ} (sample : Fin n → Obs d) :\n    hybridEstimator sample ≤ 1 := by\n  simpa [proofOnly] using heavyContribution",
      ["Demo.Obs", "Demo.hybridEstimator"],
      ["Demo.proofOnly", "Demo.heavyContribution"],
      "theorem",
    );
    const e: PaperLeanEntry = {
      obj_id: "lem:bounded",
      env: "lemmav",
      paper_label: "Lemma 1",
      lean: { decl: "Demo.hybrid_bounded", decl_kind: "theorem" },
    };
    const out = run([e], { "lem:bounded": { decl: "Demo.hybrid_bounded", file: "f", line: 100, statement: thm.source } }, [
      ...LIB,
      proofOnly,
      thm,
    ]);
    const names = (out.snippets["lem:bounded"].componentViews ?? []).map((v) => v.decl);
    expect(names).toContain("hybridEstimator"); // statement reference
    expect(names).not.toContain("proofOnly"); // proof reference only
    // heavyContribution is here on hybridEstimator's account (depth 2), not the
    // theorem's proofRefs — and so lands below the statement's own references.
    expect(out.views("lem:bounded").heavyContribution.depth).toBe(2);
    // …and the table holds exactly what some view points at, nothing more.
    expect(Object.keys(out.declSources)).not.toContain("Demo.proofOnly");
  });

  // splitCellCount is listed as a component of Definition 9 AND is the anchor
  // of Definition 7. A reader checks it at Definition 7, so Definition 9 links
  // to that block instead of inlining a second copy.
  it("reclassifies a component that another block anchors as `paper`", () => {
    const v = byDecl(def9.componentViews).splitCellCount;
    expect(v.cls).toBe("paper");
    expect(v.paperObjId).toBe("def:sample-splits");
    expect(v.paperLabel).toBe("Definition 7");
    expect(v.depth).toBe(0); // still a seed: it IS one of this block's pieces
  });

  it("does not recurse through a `paper` declaration", () => {
    // splitIndices is only reachable via splitCellCount, which stops the walk.
    expect(byDecl(def9.componentViews).splitIndices).toBeUndefined();
    // …and Definition 7, which owns splitCellCount, does pull it.
    expect(enriched.views("def:sample-splits").splitIndices).toBeDefined();
  });

  it("classifies the owning block's own anchor as `anchor`, not `paper`", () => {
    const v = enriched.views("def:sample-splits").splitCellCount;
    expect(v.cls).toBe("anchor");
    expect(v.depth).toBe(0);
    expect(v.paperObjId).toBeUndefined();
    expect(enriched.sourceOf(v)!.statement).toBe(SPLIT_CELL_COUNT.source);
  });

  // The same declaration reached from several blocks is stored once, and every
  // view of it points at that one row.
  it("stores each declaration once, whatever reaches it", () => {
    const fromDef9 = byDecl(def9.componentViews).splitCellCount;
    const fromDef7 = enriched.views("def:sample-splits").splitCellCount;
    expect(fromDef9.key).toBe("Demo.splitCellCount");
    expect(fromDef7.key).toBe(fromDef9.key);
    expect(fromDef9.cls).not.toBe(fromDef7.cls); // classified per entry, stored once
    const table = enriched.declSources["Demo.splitCellCount"];
    expect(table).toEqual({
      file: "Demo/Estimator.lean",
      line: 30,
      statement: SPLIT_CELL_COUNT.source,
      usesSorry: false,
    });
    // Every key some view names resolves, and the table holds nothing else.
    const named = new Set<string>();
    for (const s of Object.values(enriched.snippets))
      for (const v of s.componentViews ?? []) if (v.key) named.add(v.key);
    expect(new Set(Object.keys(enriched.declSources))).toEqual(named);
  });

  it("orders views by depth then source position, deterministically", () => {
    const views = def9.componentViews!;
    for (let i = 1; i < views.length; i++) {
      const [a, b] = [views[i - 1], views[i]];
      expect(a.depth <= b.depth).toBe(true);
      const [sa, sb] = [enriched.sourceOf(a)!, enriched.sourceOf(b)!];
      if (a.depth === b.depth && sa.file === sb.file) expect(sa.line <= sb.line).toBe(true);
    }
    const again = run([DEF9, DEF7], {
      "def:hybrid-estimator-handle": DEF9_SNIPPET,
      "def:sample-splits": DEF7_SNIPPET,
    });
    expect(JSON.stringify(again.snippets)).toBe(JSON.stringify(enriched.snippets));
    expect(JSON.stringify(again.declSources)).toBe(JSON.stringify(enriched.declSources));
  });

  it("only treats blocks the reader can jump to as `paper` owners", () => {
    // Same paper, but Definition 7 is a web-only Formal-layer row: there is no
    // block to link to, so its anchor stays a plain component of Definition 9.
    const webOnly: PaperLeanEntry = { ...DEF7, env: "auxiliary" };
    const out = run([DEF9, webOnly], {
      "def:hybrid-estimator-handle": DEF9_SNIPPET,
      "def:sample-splits": DEF7_SNIPPET,
    });
    const v = out.views("def:hybrid-estimator-handle").splitCellCount;
    expect(v.cls).toBe("env");
    expect(out.sourceOf(v)!.statement).toBe(SPLIT_CELL_COUNT.source);
  });

  it("ignores identifiers that are not paper declarations", () => {
    const names = def9.componentViews!.map((v) => v.decl);
    // Mathlib names appear all over these sources; the client-side highlighter
    // already links them to the library explorer.
    expect(names).not.toContain("Finset");
    expect(names).not.toContain("Fin");
    expect(names).not.toContain("sample"); // a bound parameter, not a reference
  });
});

describe("closure guards", () => {
  const chain = (i: number, next: string | null) =>
    decl(`a${i}`, i, `def a${i} : ℕ := ${next ? `${next} + 1` : "0"}`, [], next ? [`Demo.${next}`] : []);

  it("stops at the depth cap", () => {
    const lib = [0, 1, 2, 3, 4, 5, 6, 7, 8].map((i) => chain(i, i < 8 ? `a${i + 1}` : null));
    const e: PaperLeanEntry = { obj_id: "d", env: "definitionv", paper_label: "Definition 1", lean: { decl: "Demo.a0" } };
    const out = run([e], { d: { decl: "Demo.a0", file: "f", line: 0, statement: lib[0].source } }, lib);
    const names = out.snippets.d.componentViews!.map((v) => v.decl);
    expect(names).toEqual(["a0", "a1", "a2", "a3", "a4", "a5", "a6"]); // a7, a8 beyond the cap
    expect(out.snippets.d.componentViews!.map((v) => v.depth)).toEqual([0, 1, 2, 3, 4, 5, 6]);
  });

  it("terminates on a reference cycle and lists each declaration once", () => {
    const loopA = decl("loopA", 1, "def loopA : ℕ := loopB + 1", [], ["Demo.loopB"]);
    const loopB = decl("loopB", 2, "def loopB : ℕ := loopA + 1", [], ["Demo.loopA"]);
    const e: PaperLeanEntry = { obj_id: "d", env: "definitionv", paper_label: "Definition 1", lean: { decl: "Demo.loopA" } };
    const out = run([e], { d: { decl: "Demo.loopA", file: "f", line: 1, statement: loopA.source } }, [loopA, loopB]);
    expect(out.snippets.d.componentViews!.map((v) => `${v.decl}@${v.depth}`)).toEqual(["loopA@0", "loopB@1"]);
  });
});

describe("degradation", () => {
  it("enriches an old-shape snippet with no components at all", () => {
    const e: PaperLeanEntry = {
      obj_id: "def:hyb",
      env: "definitionv",
      paper_label: "Definition 9",
      lean: { decl: "Demo.hybridEstimator", decl_kind: "def" },
    };
    const out = run([e], {
      "def:hyb": { decl: "Demo.hybridEstimator", file: "Demo/Estimator.lean", line: 90, statement: HYBRID.source },
    });
    const views = out.views("def:hyb");
    expect(views.hybridEstimator.cls).toBe("anchor");
    expect(views.heavyContribution.cls).toBe("lean_only");
    expect(views.lightContribution.cls).toBe("lean_only");
  });

  it("keeps pipeline-attached components the module index does not know", () => {
    const out = run(
      [DEF9],
      {
        "def:hybrid-estimator-handle": {
          ...DEF9_SNIPPET,
          components: [{ label: "SomeOtherModule.mystery", statement: "def mystery : ℕ := 0" }],
        },
      },
      LIB,
    );
    const v = out.views("def:hybrid-estimator-handle").mystery;
    expect(v.cls).toBe("env");
    // No index entry, so no shared-table row: this one keeps its text inline.
    expect(v.key).toBeUndefined();
    expect(v.statement).toBe("def mystery : ℕ := 0");
    expect(v.file).toBe(DEF9_SNIPPET.file);
  });

  it("still structures statements when there is no module index at all", () => {
    const src = "theorem t (h : 0 < 1) : True := by trivial";
    const e: PaperLeanEntry = { obj_id: "t", env: "theoremv", paper_label: "Theorem 1", lean: { decl: "t", decl_kind: "theorem" } };
    const out = run([e], { t: { decl: "t", file: "f", line: 1, statement: src } }, null);
    expect(out.snippets.t.structured!.sharedHyps).toEqual([{ chip: "hyp", code: "(h : 0 < 1)" }]);
    expect(out.snippets.t.componentViews).toBeUndefined();
    expect(out.declSources).toEqual({});
  });
});

describe("structureStatementView", () => {
  it("splits a top-level conjunction and lifts each conjunct's own telescope", () => {
    const v = structureStatementView(
      `theorem thm (n : ℕ) (hn : 0 < n) :
    Computable ∧
    (∀ eps : ℝ, 0 < eps → eps < 1 / 2 →
      risk n eps ≤ eps) ∧
    (∀ d : ℕ, 0 < d → rate n d ≤ 1) := by
  sorry`,
    )!;
    expect(v).not.toBeNull();
    expect(v.sharedHyps).toEqual([
      { chip: "decl", code: "(n : ℕ)" },
      { chip: "hyp", code: "(hn : 0 < n)" },
    ]);
    expect(v.conclusions).toHaveLength(3);
    expect(v.conclusions[0]).toEqual({ hyps: [], code: "Computable" });
    expect(v.conclusions[1].hyps).toEqual([
      { chip: "decl", code: "∀ eps : ℝ" },
      { chip: "hyp", code: "0 < eps" },
      { chip: "hyp", code: "eps < 1 / 2" },
    ]);
    expect(v.conclusions[1].code).toBe("risk n eps ≤ eps");
    expect(v.conclusions[2].hyps.map((h) => h.code)).toEqual(["∀ d : ℕ", "0 < d"]);
    expect(v.conclusions[2].code).toBe("rate n d ≤ 1");
  });

  it("lifts a goal-level ∀/→ prefix into the shared hypotheses", () => {
    const v = structureStatementView("theorem thm : ∀ n : ℕ, 0 < n → P n ∧ Q n := by sorry")!;
    expect(v.sharedHyps).toEqual([
      { chip: "decl", code: "∀ n : ℕ" },
      { chip: "hyp", code: "0 < n" },
    ]);
    expect(v.conclusions.map((c) => c.code)).toEqual(["P n", "Q n"]);
  });

  // `∧` binds tighter than `→`, so `A → B ∧ C` is `A → (B ∧ C)`. Splitting the
  // ∧ before lifting the arrow would silently restate the theorem.
  it("respects ∧/→ precedence instead of splitting across an implication", () => {
    const v = structureStatementView("theorem thm : A → B ∧ C := by sorry")!;
    expect(v.sharedHyps).toEqual([{ chip: "hyp", code: "A" }]);
    expect(v.conclusions.map((c) => c.code)).toEqual(["B", "C"]);
  });

  it("does not split ∧ underneath a looser connective", () => {
    const v = structureStatementView("theorem thm : A ∨ B ∧ C := by sorry")!;
    expect(v.conclusions).toHaveLength(1);
    expect(v.conclusions[0].code).toBe("A ∨ B ∧ C");
  });

  // A depth-0 `→` inside `∃ f : α → β, …` is the arrow of f's TYPE. Reading it
  // as an implication would invent the hypothesis `∃ f : α`.
  it("never mistakes a binder's function-type arrow for an implication", () => {
    const v = structureStatementView("theorem thm : ∃ f : ℕ → ℕ, f 0 = 0 := by sorry")!;
    expect(v.sharedHyps).toEqual([]);
    expect(v.conclusions).toEqual([{ hyps: [], code: "∃ f : ℕ → ℕ, f 0 = 0" }]);
  });

  it("hoists a leading ∃ run and splits what it scopes", () => {
    const v = structureStatementView("theorem thm : ∃ C N : ℝ, ∃ K : ℕ, 0 < C ∧ 0 < N ∧ P K := by sorry")!;
    const card = v.conclusions[0];
    expect(v.conclusions).toHaveLength(1);
    expect(card.intro).toBe("∃ C N : ℝ, ∃ K : ℕ,");
    expect(card.code).toBeUndefined();
    expect(card.sub!.map((s) => s.code)).toEqual(["0 < C", "0 < N", "P K"]);
  });

  it("structures the body of an explicit Prop-valued definition", () => {
    const v = structureStatementView(`def VCLocalizedEnvelope
      (P : Law) (policySet : Set Policy) (α : ℝ) : Prop :=
      ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
        ∀ m : ℕ, 0 < m → EnvelopeBound P policySet α C p m`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual([
      "(P : Law)",
      "(policySet : Set Policy)",
      "(α : ℝ)",
    ]);
    expect(v.conclusions[0].intro).toBe("∃ C p : ℝ,");
    expect(v.conclusions[0].sub?.map((c) => c.code)).toEqual([
      "0 < C",
      "0 ≤ p",
      "EnvelopeBound P policySet α C p m",
    ]);
    expect(v.conclusions[0].sub?.[2].hyps.map((h) => h.code)).toEqual(["∀ m : ℕ", "0 < m"]);
  });

  it("structures a Prop-valued record into parameters and defining clauses", () => {
    const v = structurePropRecordView(`structure ExperimentClass (n : ℕ) {d : ℕ} (epsilon : ℝ)
      (P : Law d) (mu_n : Measure (Fin n → Obs d)) : Prop where
      epsilon_pos : 0 < epsilon
      epsilon_le_half : epsilon ≤ 1 / 2
      product_law : IidSampling P mu_n
      overlap : Overlap epsilon P`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual([
      "(n : ℕ)",
      "{d : ℕ}",
      "(epsilon : ℝ)",
      "(P : Law d)",
      "(mu_n : Measure (Fin n → Obs d))",
    ]);
    expect(v.conclusions.map((c) => c.code)).toEqual([
      "epsilon_pos : 0 < epsilon",
      "epsilon_le_half : epsilon ≤ 1 / 2",
      "product_law : IidSampling P mu_n",
      "overlap : Overlap epsilon P",
    ]);
    expect(structurePropRecordView("structure Ordinary where value : Nat")).toBeNull();
  });

  // An ∃ that reveals nothing is left where the author wrote it: an `intro` row
  // over a single leaf would be scaffolding, not structure.
  it("keeps an ∃ inline when its body does not split", () => {
    const v = structureStatementView("theorem thm : ∃ n : ℕ, 0 < n := by sorry")!;
    expect(v.conclusions).toEqual([{ hyps: [], code: "∃ n : ℕ, 0 < n" }]);
  });

  it("splits a conjunction whose last conjunct is an unparenthesised ∀", () => {
    // `∀` extends to the end of the clause, so this is three conjuncts and the
    // `→` inside the last one is not the top level's.
    const v = structureStatementView("theorem thm : 0 < C ∧ 0 < r ∧ ∀ n : ℕ, 0 < n → P n := by sorry")!;
    expect(v.conclusions.map((c) => c.code)).toEqual(["0 < C", "0 < r", "P n"]);
    expect(v.conclusions[2].hyps.map((h) => h.code)).toEqual(["∀ n : ℕ", "0 < n"]);
  });

  it("nests to the deeper readability cap and then stops", () => {
    // Eight nested levels of `∀ xᵢ, … ∧ …`; the card at the cap keeps whatever
    // is left of its clause verbatim instead of recursing without a bound.
    const at = (i: number, body: string) => `∀ x${i} : ℕ, ${body}`;
    const src = `theorem thm : ${at(1, `A ∧ ${at(2, `B ∧ ${at(3, `C ∧ ${at(4, `D ∧ ${at(5, `E ∧ ${at(6, `F ∧ ${at(7, `G ∧ ${at(8, "H ∧ I")}`)}`)}`)}`)}`)}`)}`)} := by sorry`;
    const v = structureStatementView(src)!;
    const depthOf = (c: ConclusionCard): number => (c.sub ? 1 + Math.max(...c.sub.map(depthOf)) : 0);
    expect(Math.max(...v.conclusions.map(depthOf))).toBe(6);
    const deepest = (c: ConclusionCard): ConclusionCard => (c.sub ? deepest(c.sub[c.sub.length - 1]) : c);
    const leaf = deepest(v.conclusions[v.conclusions.length - 1]);
    expect(leaf.hyps.map((h) => h.code)).toEqual(["∀ x8 : ℕ"]);
    expect(leaf.code).toBe("H ∧ I"); // un-split at the cap, but nothing lost
  });

  it("turns conclusion-local lets into declaration rows and splits their body", () => {
    const v = structureStatementView(`theorem sharp_sign (x : ℝ) :
      let W := x + 1
      let denominator := W ^ 2 + 1
      let derivative := W / denominator
      HasDerivAt (fun y => y) derivative x ∧
      0 < denominator ∧
      (derivative < 0 ↔ W < 0) := by sorry`)!;
    const card = v.conclusions[0];
    expect(card.hyps.map((h) => [h.chip, h.code])).toEqual([
      ["decl", "let W := x + 1"],
      ["decl", "let denominator := W ^ 2 + 1"],
      ["decl", "let derivative := W / denominator"],
    ]);
    expect(card.sub?.map((c) => c.code)).toEqual([
      "HasDerivAt (fun y => y) derivative x",
      "0 < denominator",
      "derivative < 0 ↔ W < 0",
    ]);
  });

  it("peels semicolon lets before splitting their scoped conjunction", () => {
    const v = structureStatementView(`theorem recovery (x : ℝ) :
      (let f := x + 1;
       let Q := f ^ 2;
       Q ≠ 0 ∧ P Q ∧ R Q) := by sorry`)!;
    expect(v.conclusions).toHaveLength(1);
    expect(v.conclusions[0].hyps.map((h) => h.code)).toEqual([
      "let f := x + 1",
      "let Q := f ^ 2",
    ]);
    expect(v.conclusions[0].sub?.map((c) => c.code)).toEqual(["Q ≠ 0", "P Q", "R Q"]);
  });

  it("keeps splitting when lets and governed telescopes alternate", () => {
    const v = structureStatementView(`theorem layered :
      ∃ c : ℝ, 0 < c ∧
      let B := c + 1
      ∀ L : ℝ, B ≤ L →
        let C := L + 1
        0 < C ∧ P C ∧ Q C := by sorry`)!;
    const scoped = v.conclusions[0].sub?.[1];
    expect(scoped?.hyps.map((h) => h.code)).toEqual([
      "let B := c + 1",
      "∀ L : ℝ",
      "B ≤ L",
      "let C := L + 1",
    ]);
    expect(scoped?.sub?.map((c) => c.code)).toEqual(["0 < C", "P C", "Q C"]);
  });

  it("splits conjunctions after a big-operator binder comma", () => {
    const v = structureStatementView(`theorem overlap :
      ∀ M : Model, ∀ r : ℕ, 1 ≤ r →
        (∑ i, overlap M i r) = total M r ∧
        total M r ≤ bound M r ∧
        bound M r ≤ sharp M r := by sorry`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual(["∀ M : Model", "∀ r : ℕ", "1 ≤ r"]);
    expect(v.conclusions.map((c) => c.code)).toEqual([
      "(∑ i, overlap M i r) = total M r",
      "total M r ≤ bound M r",
      "bound M r ≤ sharp M r",
    ]);
  });

  it("gives every card exactly one of code | sub", () => {
    const v = structureStatementView("theorem thm : A ∧ (∀ n : ℕ, 0 < n → B n ∧ C n) ∧ D := by sorry")!;
    const check = (c: ConclusionCard) => {
      expect(Number(c.code !== undefined) + Number(c.sub !== undefined)).toBe(1);
      (c.sub ?? []).forEach(check);
    };
    v.conclusions.forEach(check);
  });

  it("gives a non-conjunction goal a single card", () => {
    const v = structureStatementView("theorem thm (a : ℕ) : a ≤ a + 1 := by omega")!;
    expect(v.conclusions).toEqual([{ hyps: [], code: "a ≤ a + 1" }]);
  });

  it("omits the view rather than emitting an unparseable binder", () => {
    expect(structureStatementView("theorem thm () : True := trivial")).toBeNull();
    expect(structureStatementView("def notATheorem : ℕ := 0")).toBeNull();
    expect(structureStatementView("theorem thm (a : ℕ)")).toBeNull(); // no conclusion
  });

  // The load-bearing invariant: whatever is rendered must reproduce the source.
  it("never drops content — every emitted view rebuilds its source verbatim", () => {
    const sources = [
      "theorem thm (n : ℕ) (hn : 0 < n) : A n ∧ (∀ k : ℕ, k ≤ n → B n k) ∧ C n := by sorry",
      "theorem thm : ∀ n : ℕ, 0 < n → P n ∧ Q n := by sorry",
      "theorem thm : A → B ∧ C := by sorry",
      "theorem thm {α : Type*} [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α := by sorry",
      "lemma lem : ∃ f : ℕ → ℕ, f 0 = 0 ∧ f 1 = 1 := by sorry",
    ];
    const squash = (s: string) => s.replace(/\s+/g, "");
    const renderCard = (c: ConclusionCard): string =>
      c.hyps.map((h) => h.code).join("") +
      (c.intro ?? "") +
      (c.code ?? "") +
      (c.sub ?? []).map(renderCard).join("");
    for (const src of sources) {
      const v = structureStatementView(src)!;
      expect(v, src).not.toBeNull();
      const rendered = squash(
        v.sharedHyps.map((h) => h.code).join("") + v.conclusions.map(renderCard).join(""),
      );
      // Everything after the declaration's own name and before the proof: the
      // binder telescope plus the goal, which is exactly what the view renders.
      const signature = squash(
        src.slice(0, src.search(/\s:=/)).replace(/^\s*(theorem|lemma)\s+\S+/, ""),
      );
      // Every identifier-bearing character of the signature must survive into
      // the view (only the ∀/→/∧/paren scaffolding is allowed to be dropped).
      for (const tok of signature.match(/[A-Za-z_][A-Za-z0-9_.']*/g) ?? []) {
        expect(rendered, `${src} lost ${tok}`).toContain(tok);
      }
    }
  });

  it("structures the component views of theorem-kind declarations too", () => {
    const helper = decl(
      "helper_bound",
      5,
      "theorem helper_bound (n : ℕ) : lightCells n ≤ n ∧ heavyCells n ≤ n := by sorry",
      ["Demo.lightCells", "Demo.heavyCells"],
      [],
      "theorem",
    );
    const main = decl(
      "main_bound",
      6,
      "theorem main_bound (n : ℕ) : helper_bound n = helper_bound n := by sorry",
      ["Demo.helper_bound"],
      [],
      "theorem",
    );
    const e: PaperLeanEntry = { obj_id: "t", env: "theoremv", paper_label: "Theorem 1", lean: { decl: "Demo.main_bound", decl_kind: "theorem" } };
    const out = run([e], { t: { decl: "Demo.main_bound", file: "f", line: 6, statement: main.source } }, [
      ...LIB,
      helper,
      main,
    ]);
    const v = out.views("t").helper_bound;
    expect(v.cls).toBe("lean_only");
    const shared = out.declSources[v.key!];
    expect(shared.structured!.conclusions.map((c) => c.code)).toEqual([
      "lightCells n ≤ n",
      "heavyCells n ≤ n",
    ]);
    // The row is the statement, not the proof — a verbatim prefix of the source.
    expect(shared.statement).toBe(
      "theorem helper_bound (n : ℕ) : lightCells n ≤ n ∧ heavyCells n ≤ n",
    );
    expect(helper.source.startsWith(shared.statement)).toBe(true);
    // A `def` component carries no structured view — its body is its statement.
    expect(out.declSources["Demo.heavyCells"].structured).toBeUndefined();
    expect(out.declSources["Demo.heavyCells"].statement).toBe(HEAVY_CELLS.source);
  });
});

describe("verification status and completeness", () => {
  // A theorem's proof is trimmed out of what the drawer shows, so a literal
  // `sorry` in it is invisible there — the flag has to come from the index.
  it("carries a declaration's sorry status through from the index", () => {
    const shaky = decl("shaky", 5, "theorem shaky : True := by sorry", [], [], "theorem", true);
    const main = decl(
      "uses_shaky",
      6,
      "theorem uses_shaky (n : ℕ) : shaky = shaky := by simp",
      ["Demo.shaky"],
      [],
      "theorem",
    );
    const e: PaperLeanEntry = { obj_id: "t", env: "theoremv", paper_label: "Theorem 1", lean: { decl: "Demo.uses_shaky", decl_kind: "theorem" } };
    const out = run([e], { t: { decl: "Demo.uses_shaky", file: "f", line: 6, statement: main.source } }, [shaky, main]);
    expect(out.declSources["Demo.shaky"].usesSorry).toBe(true);
    expect(out.declSources["Demo.shaky"].statement).not.toContain("sorry"); // proof trimmed away
    expect(out.declSources["Demo.uses_shaky"].usesSorry).toBe(false); // recorded, and clean
    // The statement is not verified, however clean its own proof looks.
    expect(out.snippets.t.closureHasSorry).toBe(true);
  });

  it("leaves the flag off when nothing in the closure is shaky", () => {
    const out = run([DEF9, DEF7], {
      "def:hybrid-estimator-handle": DEF9_SNIPPET,
      "def:sample-splits": DEF7_SNIPPET,
    });
    expect(out.snippets["def:hybrid-estimator-handle"].closureHasSorry).toBeUndefined();
    expect(out.snippets["def:hybrid-estimator-handle"].closureSorryUnknown).toBeUndefined();
    expect(Object.values(out.declSources).every((d) => d.usesSorry === false)).toBe(true);
  });

  // An index that does not record the status is not evidence of a clean proof.
  // Collapsing a missing field to `false` is exactly how an unverified helper
  // would come to wear a tick it never earned.
  it("keeps `unknown` distinct from `proved` when the index omits the field", () => {
    const raw = [
      {
        name: "Demo.main",
        kind: "theorem",
        file: "f",
        line: 1,
        source: "theorem main : helperA = helperB := by simp",
        refs: ["Demo.helperA", "Demo.helperB"],
        proofRefs: [],
        usesSorry: false,
      },
      // no `usesSorry` at all — an older or partial index
      { name: "Demo.helperA", kind: "def", file: "f", line: 2, source: "def helperA : ℕ := 0", refs: [], proofRefs: [] },
      // present but not a boolean — equally unknown
      {
        name: "Demo.helperB",
        kind: "def",
        file: "f",
        line: 3,
        source: "def helperB : ℕ := 0",
        refs: [],
        proofRefs: [],
        usesSorry: "no",
      },
    ];
    const e: PaperLeanEntry = { obj_id: "t", env: "theoremv", paper_label: "Theorem 1", lean: { decl: "Demo.main", decl_kind: "theorem" } };
    const out = run([e], { t: { decl: "Demo.main", file: "f", line: 1, statement: raw[0].source } }, raw);
    expect(out.declSources["Demo.helperA"].usesSorry).toBeUndefined();
    expect(out.declSources["Demo.helperB"].usesSorry).toBeUndefined();
    expect(out.declSources["Demo.main"].usesSorry).toBe(false); // recorded
    expect(out.snippets.t.closureSorryUnknown).toBe(2);
    expect(out.snippets.t.closureHasSorry).toBeUndefined(); // unknown is not a `sorry`
  });

  it("counts only unrecorded helpers, not recorded-clean ones", () => {
    const out = run([DEF9, DEF7], {
      "def:hybrid-estimator-handle": DEF9_SNIPPET,
      "def:sample-splits": DEF7_SNIPPET,
    });
    expect(out.snippets["def:hybrid-estimator-handle"].closureSorryUnknown).toBeUndefined();
  });

  // A drawer cut off at the depth cap is exactly the incompleteness this module
  // exists to fix, so it must be reported rather than silently shown.
  it("reports how many declarations the depth cap left unexplored", () => {
    const chain = (i: number, next: string | null) =>
      decl(`a${i}`, i, `def a${i} : ℕ := ${next ? `${next} + 1` : "0"}`, [], next ? [`Demo.${next}`] : []);
    const lib = [0, 1, 2, 3, 4, 5, 6, 7, 8].map((i) => chain(i, i < 8 ? `a${i + 1}` : null));
    const e: PaperLeanEntry = { obj_id: "d", env: "definitionv", paper_label: "Definition 1", lean: { decl: "Demo.a0" } };
    const out = run([e], { d: { decl: "Demo.a0", file: "f", line: 0, statement: lib[0].source } }, lib);
    expect(out.snippets.d.componentViews!.map((v) => v.decl)).toEqual([
      "a0", "a1", "a2", "a3", "a4", "a5", "a6",
    ]);
    expect(out.snippets.d.closureTruncated).toBe(1); // a7 was next
  });

  it("leaves the truncation note off when the closure is complete", () => {
    const out = run([DEF7], { "def:sample-splits": DEF7_SNIPPET });
    expect(out.snippets["def:sample-splits"].closureTruncated).toBeUndefined();
  });
});

// A closure helper the artifact pairs with this statement's prose is part of
// the statement, so it belongs among the components rather than under
// "Lean only — not stated in the paper".
// A result the paper ASSUMES from the literature is neither its own machinery
// nor a result stated elsewhere in it, and calling it "Lean only" suggests
// formalized infrastructure rather than an input the theorem rests on.
describe("cited external results", () => {
  const ZENG = decl(
    "ZengLower",
    500,
    "/-- Assumed one-arm minimax lower bound. -/\nstructure ZengLower (epsilon : ℝ) : Prop where\n  bound : 0 < epsilon",
    [],
    [],
    "structure",
  );
  const THM = decl(
    "rests_on_zeng",
    501,
    "theorem rests_on_zeng (epsilon : ℝ) (hZeng : ZengLower epsilon) (he : 0 < epsilon) :\n    0 < epsilon := by exact he",
    ["Demo.ZengLower"],
    [],
    "theorem",
  );
  const CITED_ENTRY: PaperLeanEntry = {
    obj_id: "lem:zeng",
    env: "citedv",
    paper_label: "Cited Result 1",
    lean: { decl: "Demo.ZengLower", decl_kind: "structure" },
    status: "matched",
  };
  const THM_ENTRY: PaperLeanEntry = {
    obj_id: "thm:rests",
    env: "theoremv",
    paper_label: "Theorem 1",
    lean: { decl: "Demo.rests_on_zeng", decl_kind: "theorem" },
    status: "matched",
  };
  const SNIPS = {
    "thm:rests": { decl: "Demo.rests_on_zeng", file: "f", line: 501, statement: THM.source },
    "lem:zeng": { decl: "Demo.ZengLower", file: "f", line: 500, statement: ZENG.source },
  };
  const go = (env: string) =>
    run([{ ...CITED_ENTRY, env }, THM_ENTRY], SNIPS, [...LIB, ZENG, THM]);

  it("classifies a citedv anchor as `cited`, with its panel and its source", () => {
    const out = go("citedv");
    const v = out.views("thm:rests").ZengLower;
    expect(v.cls).toBe("cited");
    expect(v.paperObjId).toBe("lem:zeng");
    expect(v.paperLabel).toBe("Cited Result 1");
    // Inlined, not a bare chip: the reader must see what is being assumed.
    expect(out.declSources[v.key!].statement).toContain("structure ZengLower");
  });

  it("does not recurse through a cited result", () => {
    // `ZengLower` mentions nothing further here; the point is it is a stop.
    const out = go("citedv");
    const names = (out.snippets["thm:rests"].componentViews ?? []).map((v) => v.decl);
    expect(names).toContain("ZengLower");
  });

  it("leaves auxiliary and symbol entries classified as before", () => {
    for (const env of ["auxiliary", "symbol"]) {
      const v = go(env).views("thm:rests").ZengLower;
      expect(v.cls, env).toBe("lean_only");
      expect(v.paperObjId, env).toBeUndefined();
    }
  });

  it("chips a hypothesis assuming a cited result, and only that one", () => {
    const rows = go("citedv").snippets["thm:rests"].structured!.sharedHyps;
    const byName = (n: string) => rows.find((r) => r.code.includes(n))!;
    expect(byName("hZeng").chip).toBe("cited");
    expect(byName("he").chip).toBe("hyp"); // an ordinary side condition
    expect(byName("epsilon :").chip).toBe("decl"); // a plain parameter
  });

  it("chips nothing when the paper cites nothing", () => {
    const rows = go("auxiliary").snippets["thm:rests"].structured!.sharedHyps;
    expect(rows.map((r) => r.chip)).not.toContain("cited");
    expect(rows.find((r) => r.code.includes("hZeng"))!.chip).toBe("hyp");
  });

  it("chips cited hypotheses inside component structured views too", () => {
    const out = go("citedv");
    const shared = out.declSources["Demo.rests_on_zeng"];
    expect(shared.structured!.sharedHyps.find((h) => h.code.includes("hZeng"))!.chip).toBe("cited");
  });
});

// A closure helper the block DISPLAYS is part of the statement, so it belongs
// among the components rather than under "Lean only — not stated in the paper".
describe("promotion of display-linked closure pieces", () => {
  const DEF9_ENTRY: PaperLeanEntry = {
    obj_id: "def:hybrid-estimator-handle",
    env: "definitionv",
    paper_label: "Definition 9",
    lean: null,
    status: "matched",
  };
  const go = (displayLinks: NlBlock["displayLinks"] | null) =>
    run(
      [DEF9_ENTRY, DEF7],
      { "def:hybrid-estimator-handle": DEF9_SNIPPET, "def:sample-splits": DEF7_SNIPPET },
      LIB,
      displayLinks ? { "def:hybrid-estimator-handle": block({ displayLinks }) } : null,
    );

  // `data-xl-decl` on the prose alone points one way. The display segment's own
  // token is carried by the component too, so hovering either side lights the
  // other — the UI's word-matching does the rest.
  it("puts the display segment's token on the component, both sides", () => {
    const v = go([{ segment: "d1", decl: "heavyContribution" }]).views("def:hybrid-estimator-handle")
      .heavyContribution;
    expect(v.xl).toBe("def:hybrid-estimator-handle#d1");
  });

  it("carries a token even where the component is not promoted", () => {
    // `splitCellCount` is stated at its own block, so it stays a `paper` chip —
    // but the crosslink must still light it.
    const v = go([{ segment: "d1", decl: "splitCellCount" }]).views("def:hybrid-estimator-handle").splitCellCount;
    expect(v.cls).toBe("paper");
    expect(v.xl).toBe("def:hybrid-estimator-handle#d1");
  });

  it("lets one component carry the tokens of several display formulas", () => {
    const v = go([
      { segment: "d1", decl: "heavyContribution" },
      { segment: "d2", decl: "heavyContribution" },
    ]).views("def:hybrid-estimator-handle").heavyContribution;
    expect(v.xl).toBe("def:hybrid-estimator-handle#d1 def:hybrid-estimator-handle#d2");
  });

  it("gives a presentation-only formula no Lean-side token", () => {
    const views = go([{ segment: "d1", presentationOnly: true }]).views("def:hybrid-estimator-handle");
    expect(Object.values(views).every((v) => v.xl === undefined)).toBe(true);
  });

  it("promotes a lean_only view a displayLink names", () => {
    const before = go(null).views("def:hybrid-estimator-handle");
    expect(before.heavyContribution.cls).toBe("lean_only");

    const after = go([{ segment: "d1", decl: "heavyContribution" }]).views("def:hybrid-estimator-handle");
    expect(after.heavyContribution.cls).toBe("env");
    expect(after.heavyContribution.depth).toBe(before.heavyContribution.depth); // ordering untouched
    expect(after.lightContribution.cls).toBe("lean_only"); // neighbours unaffected
  });

  it("accepts a fully-qualified decl name too", () => {
    const out = go([{ segment: "d1", decl: "Demo.heavyContribution" }]);
    expect(out.views("def:hybrid-estimator-handle").heavyContribution.cls).toBe("env");
  });

  // A definition can be displayed in a block's prose without appearing in any
  // statement the closure walks, so the view is minted rather than the link lost.
  it("mints a view for a displayed decl the closure never reached", () => {
    const before = go(null).views("def:hybrid-estimator-handle");
    expect(before.splitIndices).toBeUndefined(); // outside this block's closure

    const out = go([{ segment: "d1", decl: "splitIndices" }]);
    const v = out.views("def:hybrid-estimator-handle").splitIndices;
    expect(v.cls).toBe("env");
    expect(v.depth).toBe(1);
    expect(v.xl).toBe("def:hybrid-estimator-handle#d1"); // two-sided, as for any other
    // Its source is interned like any other component's.
    expect(out.declSources[v.key!].statement).toContain("def splitIndices");
    expect(out.linkProblems).toEqual([]);
  });

  it("keeps the views sorted after minting one", () => {
    const views = go([{ segment: "d1", decl: "splitIndices" }]).snippets["def:hybrid-estimator-handle"]
      .componentViews!;
    for (let i = 1; i < views.length; i++) {
      expect(views[i - 1].depth <= views[i].depth, `${views[i - 1].decl} before ${views[i].decl}`).toBe(true);
    }
  });

  // A formula can show several constants at once; they share the segment's one
  // token, so the formula lights all their cards and any card lights it.
  it("puts one segment's token on every decl the formula shows", () => {
    const out = go([
      { segment: "d1", decl: "heavyContribution" },
      { segment: "d1", decl: "lightContribution" },
    ]);
    const views = out.views("def:hybrid-estimator-handle");
    expect(views.heavyContribution.xl).toBe("def:hybrid-estimator-handle#d1");
    expect(views.lightContribution.xl).toBe("def:hybrid-estimator-handle#d1");
    expect(views.heavyContribution.cls).toBe("env");
    expect(views.lightContribution.cls).toBe("env");
  });

  // `env` means "↔ a formula in this statement". The legacy component list
  // attaches pieces without that being true of each: a reader saw `Obs` labelled
  // as a formula in a statement whose prose contains no such formula. Unlinked,
  // it is just another declaration the drawer shows — how it came to be attached
  // is pipeline provenance, not something a reader needs a class for.
  it("demotes an attached component no formula here links to", () => {
    const views = go([{ segment: "d1", decl: "heavyContribution" }]).views("def:hybrid-estimator-handle");
    expect(views.Obs.cls).toBe("lean_only"); // attached, but nothing links it
    expect(views.Obs.xl).toBeUndefined();
    expect(views.heavyContribution.cls).toBe("env"); // earned
    // The classes that do not depend on link evidence are untouched.
    expect(views.splitCellCount.cls).toBe("paper");
  });

  // A legacy component is a depth-0 seed, so it leads the unlinked section on
  // the ordinary depth-then-source ordering — no special case needed.
  it("leaves a demoted component leading the unlinked section", () => {
    const views = go([{ segment: "d1", decl: "empiricalRatioCell" }]).snippets[
      "def:hybrid-estimator-handle"
    ].componentViews!;
    const unlinked = views.filter((v) => !v.xl && v.cls !== "anchor");
    expect(unlinked[0].decl).toBe("Obs"); // depth 0, ahead of every closure pull
    expect(unlinked[0].depth).toBe(0);
    expect(unlinked.map((v) => v.depth)).toEqual([...unlinked.map((v) => v.depth)].sort((a, b) => a - b));
  });

  // Demoting on no evidence would over-claim in the other direction: it would
  // assert the paper states none of it, on exactly as little grounds.
  it("keeps the legacy labelling when the bundle has no artifact to earn it against", () => {
    const views = go(null).views("def:hybrid-estimator-handle");
    expect(views.Obs.cls).toBe("env");
  });

  // A reader scanning the block top to bottom meets the cards in that order.
  describe("paper-order sorting", () => {
    const seg = (id: string, start: number) => ({
      id,
      kind: "text" as const,
      start,
      end: start + 1,
      openPath: [],
    });
    const ordered = (links: NlBlock["displayLinks"]) =>
      run(
        [DEF9_ENTRY, DEF7],
        { "def:hybrid-estimator-handle": DEF9_SNIPPET, "def:sample-splits": DEF7_SNIPPET },
        LIB,
        {
          "def:hybrid-estimator-handle": block({
            segments: [seg("d1", 50), seg("d2", 10), seg("d3", 30)],
            displayLinks: links,
          }),
        },
      ).snippets["def:hybrid-estimator-handle"].componentViews!;

    it("orders linked cards by where their formula appears in the prose", () => {
      const views = ordered([
        { segment: "d1", decl: "heavyContribution" },
        { segment: "d2", decl: "lightContribution" },
        { segment: "d3", decl: "empiricalRatioCell" },
      ]);
      const linked = views.filter((v) => v.xl).map((v) => v.decl);
      // d2 (offset 10) then d3 (30) then d1 (50) — not closure depth order.
      expect(linked).toEqual(["lightContribution", "empiricalRatioCell", "heavyContribution"]);
    });

    it("puts every linked card before the token-less ones", () => {
      const views = ordered([{ segment: "d1", decl: "empiricalRatioCell" }]);
      const firstUnlinked = views.findIndex((v) => !v.xl && v.cls !== "anchor");
      const lastLinked = views.map((v) => Boolean(v.xl)).lastIndexOf(true);
      expect(lastLinked).toBeLessThan(firstUnlinked);
    });

    it("keeps the anchor first whatever links to it", () => {
      const out = run(
        [{ ...DEF9_ENTRY, obj_id: "def:hyb", lean: { decl: "Demo.hybridEstimator", decl_kind: "def" } }],
        { "def:hyb": { decl: "Demo.hybridEstimator", file: "f", line: 90, statement: HYBRID.source } },
        LIB,
        {
          "def:hyb": block({
            segments: [seg("d1", 90)],
            displayLinks: [{ segment: "d1", decl: "heavyContribution" }],
          }),
        },
      );
      const views = out.snippets["def:hyb"].componentViews!;
      expect(views[0].cls).toBe("anchor");
      expect(views[1].decl).toBe("heavyContribution");
    });
  });

  // A formula may show an UPSTREAM declaration — one the paper builds on but
  // does not define. It has no index entry and no source in the bundle, only an
  // `extRef`, so a paper-entries-only lookup threw away a perfectly good link.
  describe("upstream declarations", () => {
    const CAUSALEAN = { n: "Causalean.Stat.hellingerSqDensity", m: "Causalean.Stat.Minimax.HellingerAffinity" };
    const MATHLIB = { n: "MeasureTheory.integral_add", m: "Mathlib.MeasureTheory.Integral.Bochner" };
    const withExt = { ...HYBRID, extRefs: [CAUSALEAN, MATHLIB] };
    const lib = LIB.map((d) => (d.name === HYBRID.name ? withExt : d));
    const go2 = (links: NlBlock["displayLinks"]) =>
      run(
        [DEF9_ENTRY, DEF7],
        { "def:hybrid-estimator-handle": DEF9_SNIPPET, "def:sample-splits": DEF7_SNIPPET },
        lib,
        { "def:hybrid-estimator-handle": block({ displayLinks: links }) },
      );

    it("resolves an extRef instead of dropping the link", () => {
      const r = resolveDisplayLinks(
        { "def:hybrid-estimator-handle": block({ displayLinks: [{ segment: "d1", decl: CAUSALEAN.n }] }) },
        lib,
      );
      expect(r.problems).toEqual([]);
      expect(r.blocks["def:hybrid-estimator-handle"].displayLinks[0].decl).toBe(CAUSALEAN.n);
    });

    it("mints a source-less card that still carries the segment token", () => {
      const out = go2([{ segment: "d1", decl: CAUSALEAN.n }]);
      const v = out.views("def:hybrid-estimator-handle").hellingerSqDensity;
      expect(v.external).toBe(true);
      expect(v.cls).toBe("env"); // a formula HERE states it
      expect(v.fullName).toBe(CAUSALEAN.n);
      expect(v.module).toBe(CAUSALEAN.m);
      expect(v.xl).toBe("def:hybrid-estimator-handle#d1"); // two-sided, as for any other
      // No source in the bundle, so nothing is interned or inlined for it.
      expect(v.key).toBeUndefined();
      expect(v.statement).toBeUndefined();
      expect(out.declSources[CAUSALEAN.n]).toBeUndefined();
      expect(out.linkProblems).toEqual([]);
    });

    // A Causalean declaration HAS a page in this explorer, but its path needs
    // the full library index, which a bundle does not carry — so the UI
    // resolves it through /library/names.json by full name.
    it("leaves a Causalean external without a docUrl, for names.json to resolve", () => {
      expect(go2([{ segment: "d1", decl: CAUSALEAN.n }]).views("def:hybrid-estimator-handle")
        .hellingerSqDensity.docUrl).toBeUndefined();
    });

    it("gives a Mathlib external an absolute docs URL", () => {
      const v = go2([{ segment: "d1", decl: MATHLIB.n }]).views("def:hybrid-estimator-handle").integral_add;
      expect(v.docUrl).toBe(
        "https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html#MeasureTheory.integral_add",
      );
    });

    it("shares one card when two formulas show the same upstream decl", () => {
      const out = go2([
        { segment: "d1", decl: CAUSALEAN.n },
        { segment: "d2", decl: CAUSALEAN.n },
      ]);
      const matching = (out.snippets["def:hybrid-estimator-handle"].componentViews ?? []).filter(
        (v) => v.fullName === CAUSALEAN.n,
      );
      expect(matching).toHaveLength(1);
      expect(matching[0].xl).toBe("def:hybrid-estimator-handle#d1 def:hybrid-estimator-handle#d2");
    });

    // Its verification is the upstream library's business.
    it("does not count an upstream decl against this paper's verification", () => {
      const s = go2([{ segment: "d1", decl: CAUSALEAN.n }]).snippets["def:hybrid-estimator-handle"];
      expect(s.closureSorryUnknown).toBeUndefined();
      expect(s.closureHasSorry).toBeUndefined();
    });

    it("still drops a decl that is neither an entry nor an extRef", () => {
      const out = go2([{ segment: "d1", decl: "Nowhere.at.all" }]);
      expect(out.linkProblems).toEqual([
        {
          objId: "def:hybrid-estimator-handle",
          reason:
            'displayLink names "Nowhere.at.all", which is neither a declaration of this paper nor an upstream reference of it',
        },
      ]);
    });
  });

  // Both halves of a crosslink must be built from the SAME surviving links, or
  // the prose keeps a token whose Lean counterpart was never minted — a span
  // that lights nothing, which reads as a broken link rather than an absent one.
  describe("resolveDisplayLinks", () => {
    const blocks = () => ({
      "def:hybrid-estimator-handle": block({
        displayLinks: [
          { segment: "d1", decl: "NotAThingInThisPaper" },
          { segment: "d2", decl: "Demo.heavyContribution" },
          { segment: "d3", presentationOnly: true },
        ],
      }),
    });

    it("drops only the unresolvable link, and reports it", () => {
      const r = resolveDisplayLinks(blocks(), LIB);
      const kept = r.blocks["def:hybrid-estimator-handle"].displayLinks;
      expect(kept.map((d) => d.segment)).toEqual(["d2", "d3"]);
      expect(r.problems).toEqual([
        {
          objId: "def:hybrid-estimator-handle",
          reason: 'displayLink names "NotAThingInThisPaper", which is neither a declaration of this paper nor an upstream reference of it',
        },
      ]);
    });

    it("keeps a fully-qualified decl verbatim, and rejects a bare short name (the producer guarantees FQ; the consumer must not be looser)", () => {
      const kept = resolveDisplayLinks(blocks(), LIB).blocks["def:hybrid-estimator-handle"].displayLinks;
      expect(kept[0].decl).toBe("Demo.heavyContribution");
      const short = { t: block({ displayLinks: [{ segment: "d1", decl: "heavyContribution" }] }) };
      const r = resolveDisplayLinks(short, LIB);
      expect(r.blocks.t.displayLinks).toEqual([]);
      expect(r.problems[0].reason).toContain("heavyContribution");
    });

    it("leaves a block alone when every link resolves", () => {
      const only = { t: block({ displayLinks: [{ segment: "d1", decl: "Demo.heavyContribution" }] }) };
      expect(resolveDisplayLinks(only, LIB).problems).toEqual([]);
    });
  });

  // One unknown formula must not cost the block its other crosslinks.
  it("drops only the link when the decl is not a declaration of this paper", () => {
    const out = go([
      { segment: "d1", decl: "NotAThingInThisPaper" },
      { segment: "d2", decl: "heavyContribution" },
    ]);
    expect(Object.keys(out.views("def:hybrid-estimator-handle"))).not.toContain("NotAThingInThisPaper");
    expect(out.views("def:hybrid-estimator-handle").heavyContribution.xl).toBe(
      "def:hybrid-estimator-handle#d2",
    );
    expect(out.linkProblems).toEqual([
      {
        objId: "def:hybrid-estimator-handle",
        reason: 'displayLink names "NotAThingInThisPaper", which is neither a declaration of this paper nor an upstream reference of it',
      },
    ]);
  });

  it("promotes nothing for a presentation-only formula", () => {
    const out = go([{ segment: "d1", presentationOnly: true }]);
    expect(out.views("def:hybrid-estimator-handle").heavyContribution.cls).toBe("lean_only");
  });

  it("promotes nothing when the block has no displayLinks", () => {
    expect(go([]).views("def:hybrid-estimator-handle").heavyContribution.cls).toBe("lean_only");
  });

  // A `paper` view is stated at its OWN block; it stays a chip pointing there
  // even if a formula here shows it, or the reader would see it twice.
  it("never promotes a paper-class view", () => {
    const v = go([{ segment: "d1", decl: "splitCellCount" }]).views("def:hybrid-estimator-handle").splitCellCount;
    expect(v.cls).toBe("paper");
    expect(v.paperObjId).toBe("def:sample-splits");
  });

  it("never promotes the anchor view", () => {
    const e: PaperLeanEntry = {
      obj_id: "def:hyb",
      env: "definitionv",
      paper_label: "Definition 9",
      lean: { decl: "Demo.hybridEstimator", decl_kind: "def" },
    };
    const out = run(
      [e],
      { "def:hyb": { decl: "Demo.hybridEstimator", file: "Demo/Estimator.lean", line: 90, statement: HYBRID.source } },
      LIB,
      { "def:hyb": block({ displayLinks: [{ segment: "d1", decl: "hybridEstimator" }] }) },
    );
    expect(out.views("def:hyb").hybridEstimator.cls).toBe("anchor");
  });
});

// The artifact carries the structured statement the pipeline already parsed,
// with a stable id on every row. The site adopts it wholesale: re-deriving it
// here could only disagree with the ids the assignments refer to.
describe("artifact-supplied structure", () => {
  const THM = decl(
    "bounded",
    200,
    "theorem bounded (n : ℕ) (hn : 0 < n) : P n ∧ Q n := by sorry",
    [],
    [],
    "theorem",
  );
  const ENTRY: PaperLeanEntry = {
    obj_id: "thm:bounded",
    env: "theoremv",
    paper_label: "Theorem 1",
    lean: { decl: "Demo.bounded", decl_kind: "theorem" },
    status: "matched",
  };
  const SNIP: PaperLeanSnippet = { decl: "Demo.bounded", file: "f", line: 200, statement: THM.source };
  /** The pipeline's own view — deliberately worded unlike anything the site's
   *  parser would produce, so adopting it is visible. */
  const artifactView = (): NlBlock["structured"] => ({
    sharedHyps: [
      { chip: "decl", code: "(n : ℕ)", id: "h1" },
      { chip: "hyp", code: "(hn : 0 < n)", id: "h2" },
    ],
    conclusions: [
      { hyps: [], code: "P n", id: "c1" },
      { hyps: [], code: "Q n", id: "c2" },
    ],
  });
  const go = (over: Partial<NlBlock>) =>
    run([ENTRY], { "thm:bounded": SNIP }, [THM], { "thm:bounded": block({ structured: artifactView(), ...over }) });

  it("renders the artifact's rows, not its own parse of the source", () => {
    const s = go({}).snippets["thm:bounded"].structured!;
    expect(s.sharedHyps.map((h) => h.code)).toEqual(["(n : ℕ)", "(hn : 0 < n)"]);
    expect(s.sharedHyps.map((h) => h.id)).toEqual(["h1", "h2"]);
    expect(s.conclusions.map((c) => c.code)).toEqual(["P n", "Q n"]);
  });

  it("puts each assigned row's crosslink token on that row", () => {
    const s = go({ assignments: [{ row: "h2", segments: ["s1"] }, { row: "c1", segments: ["s2", "s3"] }] })
      .snippets["thm:bounded"].structured!;
    expect(s.sharedHyps[1].xl).toBe("thm:bounded#h2");
    expect(s.conclusions[0].xl).toBe("thm:bounded#c1"); // one token however many segments
    expect(s.sharedHyps[0].xl).toBeUndefined();
    expect(s.conclusions[1].xl).toBeUndefined();
  });

  // Not a matching failure — a finding. The Lean says it; the paper does not.
  it("marks an unstated row, and gives it no token", () => {
    const s = go({ assignments: [{ row: "c2", segments: [], unstated: true }] })
      .snippets["thm:bounded"].structured!;
    expect(s.conclusions[1].unstated).toBe(true);
    expect(s.conclusions[1].xl).toBeUndefined();
    expect(s.conclusions[0].unstated).toBeUndefined();
  });

  it("reaches rows nested inside conclusion cards", () => {
    const nested: NlBlock["structured"] = {
      sharedHyps: [],
      conclusions: [
        {
          hyps: [{ chip: "hyp", code: "0 < k", id: "nh" }],
          id: "outer",
          intro: "∃ k : ℕ,",
          sub: [{ hyps: [], code: "P k", id: "leaf" }],
        },
      ],
    };
    const out = run([ENTRY], { "thm:bounded": SNIP }, [THM], {
      "thm:bounded": block({
        structured: nested,
        assignments: [
          { row: "nh", segments: ["s1"] },
          { row: "outer", segments: ["s2"] },
          { row: "leaf", segments: ["s3"] },
        ],
      }),
    });
    const card = out.snippets["thm:bounded"].structured!.conclusions[0];
    expect(card.hyps[0].xl).toBe("thm:bounded#nh");
    expect(card.xl).toBe("thm:bounded#outer"); // the card's own row is its intro
    expect(card.sub![0].xl).toBe("thm:bounded#leaf");
  });

  // A purely branching card carries no id, so nothing addresses it — but its
  // children are addressed normally, and walking it must not trip over the gap.
  it("walks through an id-less branching card to reach its children", () => {
    const out = run([ENTRY], { "thm:bounded": SNIP }, [THM], {
      "thm:bounded": block({
        structured: branchingCard(),
        assignments: [{ row: "h1", segments: ["s1"] }, { row: "c1", segments: ["s2"] }],
      }),
    });
    const s = out.snippets["thm:bounded"].structured!;
    const branch = s.conclusions[0];
    expect(branch.id).toBeUndefined();
    expect(branch.xl).toBeUndefined();
    expect(branch.sub![0].xl).toBe("thm:bounded#c1");
    expect(branch.sub![1].xl).toBeUndefined();
    expect(s.sharedHyps[0].xl).toBe("thm:bounded#h1");
    expect(out.linkProblems).toEqual([]);
  });

  it("reports an assignment naming a row the tree does not contain", () => {
    const out = go({ assignments: [{ row: "ghost", segments: ["s1"] }] });
    expect(out.linkProblems).toEqual([
      {
        objId: "thm:bounded",
        reason: 'assignment names row "ghost", absent from the artifact\'s structured view',
      },
    ]);
  });

  // The site's parser is the fallback, and it produces no tokens: there is
  // nothing to link a row to without the artifact's segments.
  it("falls back to its own parse when the block has no structure", () => {
    const out = run([ENTRY], { "thm:bounded": SNIP }, [THM], {
      "thm:bounded": block({ structured: null }),
    });
    const s = out.snippets["thm:bounded"].structured!;
    expect(s.conclusions.map((c) => c.code)).toEqual(["P n", "Q n"]); // its own parse
    expect(s.sharedHyps.every((h) => h.id === undefined && h.xl === undefined)).toBe(true);
  });

  it("falls back to its own parse when the bundle has no artifact at all", () => {
    const s = run([ENTRY], { "thm:bounded": SNIP }, [THM]).snippets["thm:bounded"].structured!;
    expect(s.sharedHyps.map((h) => h.code)).toEqual(["(n : ℕ)", "(hn : 0 < n)"]);
    expect(JSON.stringify(s)).not.toContain('"xl"');
  });

  // Chipping a hypothesis that assumes a cited result depends on this bundle's
  // crosswalk, which the artifact author does not see — so the site still does
  // it, over the artifact's rows.
  it("still chips cited hypotheses on an artifact-supplied view", () => {
    const ZENG = decl("ZengLower", 500, "structure ZengLower : Prop where\n  bound : True", [], [], "structure");
    const cited: PaperLeanEntry = {
      obj_id: "lem:zeng",
      env: "citedv",
      paper_label: "Cited Result 1",
      lean: { decl: "Demo.ZengLower", decl_kind: "structure" },
    };
    const view: NlBlock["structured"] = {
      sharedHyps: [{ chip: "hyp", code: "(hZeng : ZengLower)", id: "h1" }],
      conclusions: [{ hyps: [], code: "True", id: "c1" }],
    };
    const out = run(
      [cited, ENTRY],
      { "thm:bounded": SNIP, "lem:zeng": { decl: "Demo.ZengLower", file: "f", line: 500, statement: ZENG.source } },
      [ZENG, THM],
      { "thm:bounded": block({ structured: view }) },
    );
    expect(out.snippets["thm:bounded"].structured!.sharedHyps[0].chip).toBe("cited");
  });
});



// ---------------------------------------------------------------------------
// Real-bundle smoke check. Skipped when the bundle isn't in this checkout (the
// public export ships only some papers), so it never turns the suite red for
// an absent artifact — but where the bundle IS present it pins the exact case
// that motivated this module against real pipeline output, not a fixture.
// ---------------------------------------------------------------------------

const REAL_DIR = join(bundleRoots()[0], "stat_discrete_ate_minimax_loggap_polynomial_upper_match");
const hasReal = existsSync(join(REAL_DIR, "paper_library_index.json"));

describe.skipIf(!hasReal)("real bundle: discrete-ATE minimax", () => {
  const read = (n: string) => JSON.parse(readFileSync(join(REAL_DIR, n), "utf8"));
  const enriched = enrichSnippets({
    entries: read("presentation_crosswalk.json").entries,
    snippets: read("lean_snippets.json").snippets,
    paperLibEntries: read("paper_library_index.json").entries,
  });

  const NS = "CausalSmith.Stat.DiscreteAteMinimaxLoggap.";

  it("gives Definition 9 the estimator pieces its body actually names", () => {
    const views = byDecl(enriched.snippets["def:hybrid-estimator-handle"].componentViews);
    // Before this module the drawer showed hybridEstimator, Obs and
    // splitCellCount only — the reader could not resolve
    // `heavyContribution sample + lightContribution sample`.
    for (const name of [
      "heavyContribution",
      "lightContribution",
      "heavyCells",
      "lightCells",
      "empiricalRatioCell",
    ]) {
      expect(views[name].cls, name).toBe("lean_only");
      expect(views[name].key, name).toBe(NS + name);
      expect(enriched.declSources[NS + name], name).toBeDefined();
    }
    expect(enriched.declSources[NS + "heavyContribution"].statement).toContain("heavyCells sample");

    // splitCellCount is Definition 7's anchor: a link, not a second copy.
    expect(views.splitCellCount.cls).toBe("paper");
    expect(views.splitCellCount.key).toBe(NS + "splitCellCount");
    expect(views.splitCellCount.paperObjId).toBe("def:sample-splits");
    expect(views.splitCellCount.paperLabel).toBe("Definition 7");
  });

  it("stores every referenced declaration exactly once", () => {
    const rows = Object.values(enriched.snippets).flatMap((s) => s.componentViews ?? []);
    const named = new Set(rows.map((v) => v.key).filter(Boolean) as string[]);
    expect(new Set(Object.keys(enriched.declSources))).toEqual(named);
    // The whole point: far more views than stored sources.
    expect(rows.length).toBeGreaterThan(named.size * 2);
    for (const v of rows) {
      if (v.key) expect(v.statement, v.decl).toBeUndefined();
      else expect(v.statement, v.decl).toBeDefined();
    }
  });

  it("structures the paper's headline theorems", () => {
    // Theorem 2's goal is a four-way conjunction, each clause with its own ∀/→
    // telescope; Theorem 1's is ∃-headed and stays one card.
    const t2 = enriched.snippets["thm:overlap-adaptive-universal-hybrid"].structured!;
    expect(t2.conclusions).toHaveLength(4);
    expect(t2.conclusions[0].code).toBe("HybridEstimatorComputable");
    expect(t2.conclusions[2].hyps.map((h) => h.code)).toEqual([
      "∀ epsilon : ℝ",
      "0 < epsilon",
      "epsilon ≤ 1 / 2",
      "∀ n d : ℕ",
      "0 < n",
      "0 < d",
    ]);

    const t1 = enriched.snippets["thm:sharp-minimax-fixed-interior"].structured!;
    // `hZeng : ZengOneArmMinimaxLower epsilon` is an ASSUMED external result,
    // not a side condition this paper proves, and is chipped as such.
    expect(t1.sharedHyps.map((h) => h.chip)).toEqual(["decl", "cited", "hyp", "hyp"]);
    expect(t1.sharedHyps[1].code).toContain("ZengOneArmMinimaxLower");
    expect(t1.conclusions).toHaveLength(1);
  });

  // The acceptance case for recursive fine-graining: clause (ii) of Theorem 2
  // is ∀/→-scoped, then ∃-scoped, then a three-way conjunction whose last
  // conjunct is itself ∀/→-scoped over three inequalities.
  it("fine-grains Theorem 2's clause (ii) all the way down", () => {
    const clause = enriched.snippets["thm:overlap-adaptive-universal-hybrid"].structured!.conclusions[1];
    expect(clause.hyps).toEqual([
      { chip: "decl", code: "∀ epsilon : ℝ" },
      { chip: "hyp", code: "0 < epsilon" },
      { chip: "hyp", code: "epsilon < 1 / 2" },
    ]);
    expect(clause.intro).toBe("∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,");
    expect(clause.code).toBeUndefined();
    expect(clause.sub).toHaveLength(3);
    expect(clause.sub![0].code).toBe("0 < C_epsilon");
    expect(clause.sub![1].code).toBe("0 < rho_epsilon");

    const inner = clause.sub![2];
    expect(inner.hyps.map((h) => h.code)).toEqual([
      "∀ n d : ℕ",
      "0 < n",
      "0 < d",
      "N_epsilon ≤ n",
      "(d : ℝ) ≤ rho_epsilon * n * Real.log n",
    ]);
    expect(inner.sub).toHaveLength(3);
    expect(inner.sub!.map((s) => s.code!.replace(/\s+/g, " "))).toEqual([
      "worstCaseMSE n d epsilon hybridEstimator ≤ C_epsilon * minimaxRate n d",
      "minimaxRisk n d epsilon ≤ worstCaseMSE n d epsilon (selectedEstimator C_epsilon epsilon)",
      "worstCaseMSE n d epsilon (selectedEstimator C_epsilon epsilon) ≤ max C_epsilon 4 * " +
        "(1 / (n : ℝ) + min (d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) ((1 / 2 - epsilon) ^ 2))",
    ]);
  });

  // A def's body is its statement and is kept whole; a theorem's proof is not,
  // so the table stores a verbatim PREFIX of the source — docstring and
  // signature through the goal — and never a rewrite of it.
  it("stores statements verbatim, with theorem proofs dropped", () => {
    const index = new Map<string, { kind: string; file: string; line: number; source: string }>(
      (read("paper_library_index.json").entries as {
        name: string;
        kind: string;
        file: string;
        line: number;
        source: string;
      }[]).map((e) => [e.name, e]),
    );
    let trimmed = 0;
    let whole = 0;
    for (const [key, row] of Object.entries(enriched.declSources)) {
      const orig = index.get(key);
      expect(orig, key).toBeDefined();
      expect(row.file, key).toBe(orig!.file);
      expect(row.line, key).toBe(orig!.line);
      if (orig!.kind === "theorem" || orig!.kind === "lemma") {
        expect(orig!.source.startsWith(row.statement), key).toBe(true);
        expect(row.statement, key).not.toMatch(/:=\s*by\b/);
        if (row.statement.length < orig!.source.length) trimmed++;
      } else {
        expect(row.statement, key).toBe(orig!.source);
        whole++;
      }
    }
    expect(trimmed).toBeGreaterThan(0);
    expect(whole).toBeGreaterThan(0);
  });
});
