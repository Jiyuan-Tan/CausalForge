import { describe, it, expect } from "vitest";
import { buildGoldPairs, fileToCluster, computeGoldIdf, coreGold } from "../../src/formalization/retrieval_eval/gold.js";

const FIXTURE_LIB = {
  commit: "test", toolchain: "x", modules: {}, sidecars: {},
  entries: [
    { name: "Causalean.PO.ID.Overlap", kind: "structure", module: "m", file: "Causalean/PO/ID/Overlap.lean", line: 1, statement: "...", doc: "Positivity.", refs: [], axioms: [], usesSorry: false },
    { name: "Causalean.PO.ID.foo", kind: "theorem", module: "m", file: "Causalean/PO/ID/Foo.lean", line: 1, statement: "...", doc: "Foo.", usesSorry: false, axioms: [],
      refs: ["Causalean.PO.ID.foo", "Causalean.PO.ID", "Causalean.PO.ID.Overlap", "Causalean.PO.ID.instGlue", "Mathlib.X"] },
    { name: "Causalean.PO.ID.instGlue", kind: "instance", module: "m", file: "Causalean/PO/ID/Foo.lean", line: 2, statement: "...", doc: "", usesSorry: false, axioms: [], refs: [] },
  ],
};

describe("buildGoldPairs", () => {
  it("drops self, namespace-ancestor, non-index (Mathlib), and instance refs", () => {
    const pairs = buildGoldPairs(FIXTURE_LIB as any);
    const foo = pairs.find((p) => p.theorem === "Causalean.PO.ID.foo")!;
    expect(foo.gold).toEqual(["Causalean.PO.ID.Overlap"]); // only the kept structure
  });
  it("emits no pair for a theorem with empty gold", () => {
    const lib = { ...FIXTURE_LIB, entries: [FIXTURE_LIB.entries[0]] };
    expect(buildGoldPairs(lib as any)).toEqual([]);
  });
  it("assigns the theorem's cluster from its file", () => {
    expect(fileToCluster("Causalean/PO/ID/Exact/ATE.lean")).toBe("exactid");
    expect(fileToCluster("Causalean/Stat/CLT/Foo.lean")).toBe("stat");
    expect(fileToCluster("Causalean/Unrooted/X.lean")).toBeNull();
  });
  it("computeGoldIdf: a ubiquitous decl gets lower IDF; coreGold drops it", () => {
    const pairs = [
      { theorem: "T1", cluster: null, gold: ["Carrier", "Rare"], doc: "", statement: "" },
      { theorem: "T2", cluster: null, gold: ["Carrier"], doc: "", statement: "" },
      { theorem: "T3", cluster: null, gold: ["Carrier"], doc: "", statement: "" },
    ] as any;
    const idf = computeGoldIdf(pairs);
    expect(idf.get("Carrier")!).toBeLessThan(idf.get("Rare")!);
    const floor = (idf.get("Carrier")! + idf.get("Rare")!) / 2;
    expect(coreGold(["Carrier", "Rare"], idf, floor)).toEqual(["Rare"]);
  });
});
