import { describe, it, expect } from "vitest";
import { SemanticTier, isEmbeddingsStale, embedQueries, buildAdjacency } from "../src/formalization/semantic_tier.js";

describe("embedQueries", () => {
  it("returns [] for empty input without invoking python", () => {
    expect(embedQueries([], "../..")).toEqual([]);
  });
});

function tier() {
  // 3 decls, 2-dim unit vectors; fileOf maps to clusters
  const names = ["A", "B", "C"];
  const vecs = new Float32Array([1, 0, /*A*/ 0.8, 0.6, /*B*/ 0, 1 /*C*/]);
  const fileOf = (n: string) => ({ A: "Causalean/Stat/a.lean", B: "Causalean/Stat/b.lean", C: "Causalean/PO/c.lean" }[n]!);
  return new SemanticTier(names, vecs, 2, fileOf);
}

describe("SemanticTier.topK", () => {
  it("ranks by cosine and applies the floor", () => {
    const r = tier().topK(new Float32Array([1, 0]), { k: 3, floor: 0.5, cluster: null, exclude: new Set() });
    expect(r.map((x) => x.name)).toEqual(["A", "B"]); // C cos=0 < floor
    expect(r[0].sim).toBeCloseTo(1);
  });
  it("excludes named decls and filters by cluster", () => {
    const r = tier().topK(new Float32Array([1, 0]), { k: 3, floor: 0, cluster: "stat", exclude: new Set(["A"]) });
    // A excluded by name. C is `Causalean/PO/c.lean`, and `Causalean/PO/` IS a declared root of
    // the stat cluster, so C belongs here — this previously expected ["B"] only because the
    // single-label filter awarded PO to panel and hid it from stat.
    expect(r.map((x) => x.name)).toEqual(["B", "C"]);
  });

  // Cluster substrate roots OVERLAP by design: `Causalean/PO/` is a root of panel, exactid AND
  // partialid. Cluster filtering must therefore test MEMBERSHIP in the requested cluster's roots
  // (as lexical retrieval does), not assign each file one winning cluster — a single-label
  // assignment hands every equal-length tie to whichever cluster is declared first and silently
  // drops the shared substrate from the others.
  it.each(["panel", "exactid", "partialid"] as const)(
    "keeps a shared Causalean/PO decl for cluster %s",
    (cluster) => {
      const t = new SemanticTier(["P"], new Float32Array([1, 0]), 2, () => "Causalean/PO/c.lean");
      const r = t.topK(new Float32Array([1, 0]), { k: 3, floor: 0, cluster, exclude: new Set() });
      expect(r.map((x) => x.name)).toEqual(["P"]);
    },
  );

  it("still rejects a decl outside the requested cluster's roots", () => {
    const t = new SemanticTier(["S"], new Float32Array([1, 0]), 2, () => "Causalean/Stat/s.lean");
    const r = t.topK(new Float32Array([1, 0]), { k: 3, floor: 0, cluster: "exactid", exclude: new Set() });
    expect(r).toEqual([]);
  });

  it("matches a `.lean`-suffixed root exactly, not as a directory prefix", () => {
    // exactid lists the FILE `Causalean/Graph/SWIG.lean` as a root.
    const hit = new SemanticTier(["G"], new Float32Array([1, 0]), 2, () => "Causalean/Graph/SWIG.lean");
    expect(hit.topK(new Float32Array([1, 0]), { k: 3, floor: 0, cluster: "exactid", exclude: new Set() })
      .map((x) => x.name)).toEqual(["G"]);
    const miss = new SemanticTier(["H"], new Float32Array([1, 0]), 2, () => "Causalean/Graph/SWIGOther.lean");
    expect(miss.topK(new Float32Array([1, 0]), { k: 3, floor: 0, cluster: "exactid", exclude: new Set() })).toEqual([]);
  });
});

describe("SemanticTier multi-view max-sim", () => {
  // Query q=[1,0].  base(nl): A=[1,0] cos1.0, B=[.5,.866] cos0.5.
  //                 extra(nbr): A=[0,1] cos0.0, B=[.9,.436] cos0.9.
  // Multi-view scoring takes the MAX cosine across views per decl.
  const s3 = Math.sqrt(3) / 2;
  const base = new Float32Array([1, 0, 0.5, s3]);
  const extra = new Float32Array([0, 1, 0.9, Math.sqrt(1 - 0.81)]);
  const q = new Float32Array([1, 0]);

  it("scores each decl by the max cosine across base and extra views", () => {
    const t = new SemanticTier(["A", "B"], base, 2, () => undefined, [extra]);
    const hits = t.topK(q, { k: 5, floor: -1, cluster: null, exclude: new Set() });
    expect(hits.find((h) => h.name === "B")!.sim).toBeCloseTo(0.9, 5); // extra view lifts B from 0.5
    expect(hits.find((h) => h.name === "A")!.sim).toBeCloseTo(1.0, 5); // base wins for A
  });

  it("with no extra views, uses base-only cosine", () => {
    const t = new SemanticTier(["A", "B"], base, 2, () => undefined);
    const hits = t.topK(q, { k: 5, floor: -1, cluster: null, exclude: new Set() });
    expect(hits.find((h) => h.name === "B")!.sim).toBeCloseTo(0.5, 5);
  });
});

describe("buildAdjacency (undirected refs neighbourhood, aligned to names order)", () => {
  it("adds both the forward ref edge and its reverse (used-by) edge", () => {
    const adj = buildAdjacency(["A", "B", "C"], [
      { name: "A", refs: ["B"] }, // A→B
      { name: "B", refs: [] },
      { name: "C", refs: ["A"] }, // C→A
    ]);
    expect(new Set(adj[0])).toEqual(new Set([1, 2])); // A ~ B (forward), A ~ C (reverse of C→A)
    expect(new Set(adj[1])).toEqual(new Set([0]));     // B ~ A (reverse of A→B)
    expect(new Set(adj[2])).toEqual(new Set([0]));     // C ~ A (forward)
  });

  it("ignores refs/decls not present in the names row order and self-loops", () => {
    const adj = buildAdjacency(["A", "B"], [
      { name: "A", refs: ["A", "Z"] }, // self-loop + unknown ref → both dropped
      { name: "Q", refs: ["B"] },       // decl absent from names → skipped
    ]);
    expect(adj[0]).toEqual([]);
    expect(adj[1]).toEqual([]);
  });
});

describe("SemanticTier one-hop graph propagation (Ch4)", () => {
  // q=[1,0].  A=[0.1,…] cos0.1 (word-poor target), B=[1,0] cos1.0 (its matched neighbor),
  // C=[0,1] cos0.0 (unrelated, no neighbors). Undirected refs adjacency A<->B.
  // score'(d) = sim(d) + λ·max_{n∈adj(d)} sim(n).  λ=0.5:
  //   A = 0.1 + 0.5·1.0 = 0.6 ,  B = 1.0 + 0.5·0.1 = 1.05 ,  C = 0.0 (no neighbors)
  const vecs = new Float32Array([0.1, Math.sqrt(1 - 0.01), /*A*/ 1, 0, /*B*/ 0, 1 /*C*/]);
  const adjacency = [[1], [0], []]; // A~B, B~A, C isolated
  const q = new Float32Array([1, 0]);
  const mk = () => new SemanticTier(["A", "B", "C"], vecs, 2, () => undefined, [], adjacency);

  it("boosts a low-sim decl adjacent to a high-sim neighbor", () => {
    const hits = mk().topK(q, { k: 5, floor: -1, cluster: null, exclude: new Set(), graphProp: 0.5 });
    expect(hits.find((h) => h.name === "A")!.sim).toBeCloseTo(0.6, 5); // 0.1 → 0.6 via neighbor B
    expect(hits.map((h) => h.name)).toEqual(["B", "A", "C"]);
  });

  it("leaves a neighbourless decl unchanged", () => {
    const hits = mk().topK(q, { k: 5, floor: -1, cluster: null, exclude: new Set(), graphProp: 0.5 });
    expect(hits.find((h) => h.name === "C")!.sim).toBeCloseTo(0.0, 5);
  });

  it("is a no-op when graphProp is 0 or unset", () => {
    const hits = mk().topK(q, { k: 5, floor: -1, cluster: null, exclude: new Set() });
    expect(hits.find((h) => h.name === "A")!.sim).toBeCloseTo(0.1, 5); // raw cosine, no boost
  });

  it("can lift a below-floor target above the floor via its neighbor", () => {
    // floor 0.3: raw A=0.1 would be dropped; propagated A=0.6 survives (the gap-rescue).
    const hits = mk().topK(q, { k: 5, floor: 0.3, cluster: null, exclude: new Set(), graphProp: 0.5 });
    expect(hits.map((h) => h.name)).toContain("A");
  });
});

it("isEmbeddingsStale: fresh when names+commit match, stale on drift", () => {
  expect(isEmbeddingsStale({ names: ["A", "B"], index_commit: "c1" }, { commit: "c1", names: ["A", "B"] })).toBe(false);
  expect(isEmbeddingsStale({ names: ["A", "B"], index_commit: "c1" }, { commit: "c2", names: ["A", "B"] })).toBe(true);
  expect(isEmbeddingsStale({ names: ["A"], index_commit: "c1" }, { commit: "c1", names: ["A", "B"] })).toBe(true);
});
