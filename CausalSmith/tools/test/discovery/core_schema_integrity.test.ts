// Schema holes found by static audit of the D-stage, 2026-07-20. Each was reachable in
// NORMAL operation -- no crash, no operator edit, no concurrency -- because the schema
// validated fields independently that downstream code treats as coupled.

import { describe, it, expect } from "vitest";
import { StatementSchema, CoreSchema } from "../../src/discovery/core/schema.js";

const stmt = (over: Record<string, unknown> = {}) => ({
  id: "lem:x", kind: "lemma", statement: "S", depends_on: [], status: "to-prove", ...over,
});

describe("a headline-shaped id must not carry kind lemma", () => {
  // Deliberately NARROW. Reachability keys on `kind`: non-lemma nodes are ROOTS and
  // unreachable kind:"lemma" nodes are PRUNED (stage0_working.ts:398). So the destructive
  // case is a headline-shaped id carrying kind "lemma" -- it is not a root, and once
  // unreferenced it is DELETED. Other mismatches merely mis-root a node, which is
  // recoverable, and outlawing them would break legitimate patterns.
  it("rejects a headline theorem mislabelled as a lemma", () => {
    const r = StatementSchema.safeParse(stmt({ id: "thm:headline", kind: "lemma" }));
    expect(r.success).toBe(false);
    if (!r.success) expect(JSON.stringify(r.error.issues)).toMatch(/must not have kind `lemma`/);
  });

  it("rejects prop: and oeq: mislabelled as lemmas too", () => {
    expect(StatementSchema.safeParse(stmt({ id: "prop:a", kind: "lemma" })).success).toBe(false);
    expect(StatementSchema.safeParse(stmt({ id: "oeq:a", kind: "lemma" })).success).toBe(false);
  });

  it("PERMITS the legitimate non-lemma mismatches a bijection would have outlawed", () => {
    // A conjectured headline posed at D-1 is a real fixture, and a lem: id promoted to a
    // theorem mis-roots but never deletes. An earlier, over-broad bijection outlawed both
    // and broke 33 existing tests.
    expect(StatementSchema.safeParse(stmt({ id: "thm:rate", kind: "conjecture" })).success).toBe(true);
    expect(StatementSchema.safeParse(stmt({ id: "lem:a", kind: "theorem" })).success).toBe(true);
    expect(StatementSchema.safeParse(stmt({ id: "prop:a", kind: "theorem" })).success).toBe(true);
  });

  it("accepts every matching pair", () => {
    for (const [id, kind] of [["thm:a", "theorem"], ["lem:a", "lemma"], ["prop:a", "proposition"],
                              ["oeq:a", "openendedquestion"], ["conj:a", "theorem"]] as const) {
      expect(StatementSchema.safeParse(stmt({ id, kind })).success, `${id}/${kind}`).toBe(true);
    }
  });
});

describe("a cited leaf may not rest on an OPEN question", () => {
  const cited = (dep: string) => stmt({
    id: "lem:c", kind: "lemma", status: "cited",
    source: { cite: "K", locator: "Thm 1" }, depends_on: [dep],
  });

  it("rejects cited -> oeq: and cited -> conj:", () => {
    // The original pattern listed only lem|thm|prop, so a cited node counted as settled
    // while its support was an unresolved open question.
    expect(StatementSchema.safeParse(cited("oeq:open")).success).toBe(false);
    expect(StatementSchema.safeParse(cited("conj:guess")).success).toBe(false);
  });

  it("still rejects cited -> lem:/thm:/prop: and still allows def:/ass:", () => {
    expect(StatementSchema.safeParse(cited("lem:other")).success).toBe(false);
    expect(StatementSchema.safeParse(cited("def:env")).success).toBe(true);
    expect(StatementSchema.safeParse(cited("ass:overlap")).success).toBe(true);
  });
});

describe("statement ids must be unique", () => {
  const core = (statements: unknown[]) => ({
    qid: "q", symbols: [], assumptions: [], definitions: [], statements,
    target_estimand: "tau", bibliography: [],
  });

  it("rejects two records under one id", () => {
    // Consumers key by id through Map/Set, so a duplicate resolves to ONE record while a
    // sibling path may edit the other -- a bundle can mutate one copy and render the other.
    const r = CoreSchema.safeParse(core([stmt({ statement: "A" }), stmt({ statement: "B" })]));
    expect(r.success).toBe(false);
    if (!r.success) expect(JSON.stringify(r.error.issues)).toMatch(/duplicate statement id\(s\): lem:x/);
  });

  it("accepts distinct ids", () => {
    expect(CoreSchema.safeParse(core([stmt({ id: "lem:a" }), stmt({ id: "lem:b" })])).success).toBe(true);
  });
});
