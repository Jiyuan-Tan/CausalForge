import { describe, it, expect } from "vitest";
import { blendSemantic, blendWeighted } from "../../src/formalization/reuse_retrieval.js";

const lex = (name: string, score: number) => ({
  name, statement: "", docFirstPara: "", module: "", file: "",
  tier1: false, usesSorry: false, score, matchedVia: "name" as const,
});

describe("blendSemantic (RRF fusion)", () => {
  it("injects a semantic-only hit tagged 'semantic' and preserves lexical metadata", () => {
    const out = blendSemantic([lex("L1", 9)], [{ name: "S1", sim: 0.8 }], 10);
    const names = out.map((c) => c.name);
    expect(names).toContain("S1");
    expect(out.find((c) => c.name === "S1")!.matchedVia).toBe("semantic");
    expect(out.find((c) => c.name === "L1")!.matchedVia).toBe("name"); // lexical Candidate kept
  });

  it("a decl in BOTH lists outranks one in only a single list (RRF is additive)", () => {
    const out = blendSemantic(
      [lex("both", 5), lex("lexOnly", 4)],
      [{ name: "both", sim: 0.9 }, { name: "semOnly", sim: 0.8 }],
      10,
    );
    expect(out[0].name).toBe("both"); // rank1 in both lists → 2/(k0+1) beats any single 1/(k0+1)
  });

  it("respects topK", () => {
    const out = blendSemantic([lex("L1", 9), lex("L2", 8)], [{ name: "S1", sim: 0.7 }], 2);
    expect(out).toHaveLength(2);
  });

  it("populates real metadata for a semantic-only hit via the resolver", () => {
    const resolve = (name: string) =>
      name === "S1"
        ? { statement: "S1 : True", docFirstPara: "the S1 fact", module: "Mod", file: "F.lean", tier1: true, usesSorry: false }
        : null;
    const out = blendSemantic([lex("L1", 9)], [{ name: "S1", sim: 0.8 }], 10, 60, resolve);
    const s1 = out.find((c) => c.name === "S1")!;
    expect(s1.matchedVia).toBe("semantic"); // still tagged as a semantic-only hit
    expect(s1.statement).toBe("S1 : True");
    expect(s1.docFirstPara).toBe("the S1 fact");
    expect(s1.module).toBe("Mod");
    expect(s1.file).toBe("F.lean");
    expect(s1.tier1).toBe(true);
  });

  it("falls back to empty metadata for a semantic-only hit the resolver cannot resolve", () => {
    const out = blendSemantic([lex("L1", 9)], [{ name: "S1", sim: 0.8 }], 10, 60, () => null);
    const s1 = out.find((c) => c.name === "S1")!;
    expect(s1.matchedVia).toBe("semantic");
    expect(s1.statement).toBe(""); // no throw, graceful empty
  });
});

describe("blendSemantic (confidence-aware fusion)", () => {
  // The bridgeable-stratum regression the eval revealed: a WRONG decl that has weak
  // lexical presence AND a strong dense hit gets an RRF boost that displaces the correct,
  // confident lexical top hit. Confidence-aware fusion must protect the confident hit.
  // Explicit confidentScore (6th arg) so these pin the mechanism regardless of the
  // production default (which is tuned for the current encoder, not this fixture's scores).
  const CONF = 8;
  it("does NOT let a dense-boosted wrong decl displace a confident lexical top hit", () => {
    const out = blendSemantic(
      [lex("correct", 12), lex("wrong", 5)],
      [{ name: "wrong", sim: 0.9 }, { name: "noise", sim: 0.8 }],
      10, 60, undefined, CONF,
    );
    expect(out[0].name).toBe("correct"); // under plain RRF this was "wrong"
  });

  // Gap stratum: lexical is weak (no confident hit), so dense should drive and a
  // dense-only correct hit can rank at the top.
  it("lets dense drive when lexical is weak (no confident hit)", () => {
    const out = blendSemantic(
      [lex("weakDoc", 4)],
      [{ name: "denseHit", sim: 0.9 }],
      10, 60, undefined, CONF,
    );
    expect(out[0].name).toBe("denseHit");
  });

  // Confident lexical head still leaves lower slots for dense to fill.
  it("keeps a confident lexical hit on top but still surfaces a dense-only hit below it", () => {
    const out = blendSemantic([lex("Lgood", 12)], [{ name: "Sextra", sim: 0.9 }], 10, 60, undefined, CONF);
    expect(out[0].name).toBe("Lgood");
    expect(out.map((c) => c.name)).toContain("Sextra");
  });
});

describe("blendWeighted (min-max-normalized weighted score sum)", () => {
  // Unlike RRF (rank-only), this preserves each channel's MAGNITUDE after min-max normalization —
  // the dense cosine's confidence (0.9 ≫ 0.5) survives. wLex=0.3, wDense=0.7.
  it("fuses normalized channel magnitudes; a dense-strong decl outranks a lex-strong one", () => {
    const out = blendWeighted([lex("X", 10), lex("Y", 5)], [{ name: "Y", sim: 0.9 }, { name: "Z", sim: 0.8 }], 10, 0.3, 0.7);
    // lexNorm: X=1,Y=0 ; simNorm: Y=1,Z=0 → X=0.3, Y=0.7, Z=0
    expect(out.map((c) => c.name)).toEqual(["Y", "X", "Z"]);
    expect(out[0].score).toBeCloseTo(0.7, 5);
  });

  it("tags a semantic-only hit and recovers its metadata via the resolver", () => {
    const resolve = (n: string) => (n === "Z" ? { statement: "Z:True", docFirstPara: "z", module: "M", file: "F.lean", tier1: false, usesSorry: false } : null);
    const out = blendWeighted([lex("X", 10)], [{ name: "Z", sim: 0.9 }], 10, 0.3, 0.7, resolve);
    const z = out.find((c) => c.name === "Z")!;
    expect(z.matchedVia).toBe("semantic");
    expect(z.statement).toBe("Z:True");
    expect(out.find((c) => c.name === "X")!.matchedVia).toBe("name"); // lexical metadata kept
  });

  it("treats an all-equal channel as fully credited (no divide-by-zero)", () => {
    // single lexical + single dense, disjoint names → each normalizes to 1 within its channel
    const out = blendWeighted([lex("X", 7)], [{ name: "Z", sim: 0.4 }], 10, 0.3, 0.7);
    expect(out.find((c) => c.name === "X")!.score).toBeCloseTo(0.3, 5);
    expect(out.find((c) => c.name === "Z")!.score).toBeCloseTo(0.7, 5);
  });

  it("respects topK", () => {
    const out = blendWeighted([lex("X", 10), lex("Y", 5)], [{ name: "Z", sim: 0.9 }], 2, 0.3, 0.7);
    expect(out).toHaveLength(2);
  });

  it("pins a confident lexical hit above a dense-strong decl (same protection as RRF)", () => {
    // Lconf clears the default confidence bar (40); Ddense has a near-perfect cosine.
    const out = blendWeighted(
      [lex("Lconf", 50), lex("Lweak", 3)],
      [{ name: "Ddense", sim: 0.99 }, { name: "Lweak", sim: 0.2 }],
      10, 0.3, 0.7,
    );
    expect(out[0].name).toBe("Lconf"); // pinned; dense magnitude cannot displace it
    expect(out.map((c) => c.name)).toContain("Ddense"); // still surfaced below
  });

  it("does not pin when no lexical hit clears the confidence bar", () => {
    const out = blendWeighted([lex("X", 10)], [{ name: "Z", sim: 0.9 }], 10, 0.3, 0.7);
    expect(out[0].name).toBe("Z"); // nothing pinned → dense magnitude drives
  });
});
