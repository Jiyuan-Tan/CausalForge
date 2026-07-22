import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { buildDagFromCore } from "../../src/discovery/core/dag.js";
import { coreNodeIds, StatementSchema, type Core } from "../../src/discovery/core/schema.js";

function loadFixture(): Core {
  const raw = readFileSync(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8");
  return JSON.parse(raw) as Core;
}

describe("buildDagFromCore — real stat fixture", () => {
  const core = loadFixture();
  const dag = buildDagFromCore(core);

  it("covers exactly the core node ids (assumptions ∪ definitions ∪ statements)", () => {
    expect(dag.nodes).toEqual(coreNodeIds(core));
  });

  it("classifies each node kind by its core shape", () => {
    for (const a of core.assumptions) expect(dag.kindOf.get(a.id)).toBe("assumption");
    for (const s of core.statements) expect(dag.kindOf.get(s.id)).toBe("statement");
    for (const d of core.definitions) {
      const want = d.by_member_properties !== undefined ? "definition-class" : "definition-construction";
      expect(dag.kindOf.get(d.id)).toBe(want);
    }
  });

  it("records class members and their owner back-pointer", () => {
    for (const d of core.definitions) {
      if (d.by_member_properties === undefined) continue;
      expect(dag.classMembers.get(d.id)).toEqual(d.by_member_properties);
      for (const m of d.by_member_properties) expect(dag.memberOwner.get(m)).toBeDefined();
    }
  });

  it("splits each statement's depends_on into assumption-like vs statement deps", () => {
    for (const s of core.statements) {
      const a = dag.assumptionDeps.get(s.id) ?? [];
      const st = dag.statementDeps.get(s.id) ?? [];
      expect(new Set([...a, ...st])).toEqual(new Set(s.depends_on));
      for (const d of st) expect(dag.kindOf.get(d)).toBe("statement");
      for (const d of a) expect(dag.kindOf.get(d)).not.toBe("statement");
    }
  });
});

describe("StatementSchema optional proof normalization", () => {
  it("normalizes a cited leaf's JSON null proof_tex to absence", () => {
    const statement = StatementSchema.parse({
      id: "lem:classical-result",
      kind: "lemma",
      statement: "A cited result.",
      depends_on: [],
      status: "cited",
      source: {
        cite: "Author2024",
        locator: "Theorem 1",
        attestation: { by: "d0-agent", note: "Checked against the source." },
      },
      proof_tex: null,
    });

    expect(statement.proof_tex).toBeUndefined();
    expect(Object.hasOwn(statement, "proof_tex")).toBe(true);
  });

  it("still rejects non-string non-null proof payloads", () => {
    expect(() => StatementSchema.parse({
      id: "lem:invalid-proof",
      kind: "lemma",
      statement: "An invalid result.",
      depends_on: [],
      status: "proved",
      proof_tex: 7,
    })).toThrow();
  });
});
