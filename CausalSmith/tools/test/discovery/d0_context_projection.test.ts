import { describe, expect, it } from "vitest";
import { CoreSchema, type Core } from "../../src/discovery/core/schema.js";
import {
  frozenCoreSnapshot,
  projectFrozenCore,
  serializeFrozenCoreSnapshot,
} from "../../src/discovery/solve/context_projection.js";

function fixture(): Core {
  return CoreSchema.parse({
    qid: "stat_projection",
    specialization: "v1",
    cluster: "stat",
    symbols: [
      { name: "x", type: "real" },
      { name: "y", type: "real" },
      { name: "z", type: "real", ref: "def:sibling" },
    ],
    assumptions: [
      { id: "ass:up", condition: "x is positive", free_symbols: ["x"], standard: { name: "positive", cite: "Ref" } },
      { id: "ass:down", condition: "y is finite", free_symbols: ["y"], standard: { name: "finite", cite: "Ref" } },
      { id: "ass:sibling", condition: "z is bounded", free_symbols: ["z"], standard: { name: "bounded", cite: "Ref" } },
    ],
    definitions: [
      { id: "def:up", name: "U", construction: "U=x", free_symbols: ["x"], inputs: ["x"] },
      { id: "def:sibling", name: "S", construction: "S=z", free_symbols: ["z"], by_member_properties: ["ass:sibling"] },
      { id: "def:omitted", name: "O", construction: "O=y", free_symbols: ["y"], inputs: ["y"] },
    ],
    statements: [
      {
        id: "lem:upstream", kind: "lemma", statement: "U is positive", free_symbols: ["x"],
        depends_on: ["ass:up", "def:up"], status: "proved", proof_tex: "Immediate.",
      },
      {
        id: "thm:target", kind: "theorem", statement: "The target holds", free_symbols: ["x"],
        depends_on: ["lem:upstream"], status: "to-prove", justification: "headline", gap: "gap", consumer: "reader",
      },
      {
        id: "prop:downstream", kind: "proposition", statement: "The target implies a y-result", free_symbols: ["y"],
        depends_on: ["thm:target", "ass:down"], status: "to-prove", justification: "use", gap: "gap", consumer: "reader",
      },
      {
        id: "thm:sibling", kind: "theorem", statement: "The sibling holds", free_symbols: ["z"],
        depends_on: ["def:sibling"], status: "to-prove", justification: "other", gap: "gap", consumer: "reader",
      },
    ],
    target_estimand: "theta",
    tldr: "Full-core prose retained only in the snapshot.",
    bibliography: [{ key: "Ref", citation: "Reference" }],
  });
}

describe("D0 frozen-core local projection", () => {
  it("inlines target upstream/downstream and referenced catalog closure", () => {
    const projected = projectFrozenCore(fixture(), new Set(["thm:target"]));
    expect(projected.manifest.mode).toBe("projected");
    expect(projected.inline.statements.map(({ id }) => id)).toEqual(["lem:upstream", "thm:target"]);
    expect(projected.manifest.affected_downstream_statement_ids).toEqual(["prop:downstream"]);
    expect(projected.inline.assumptions.map(({ id }) => id)).toEqual(["ass:up"]);
    expect(projected.inline.definitions.map(({ id }) => id)).toEqual(["def:up"]);
    expect(projected.inline.symbols.map(({ name }) => name)).toEqual(["x"]);
    expect(projected.manifest.omitted).toEqual({
      symbols: ["y", "z"],
      assumptions: ["ass:down", "ass:sibling"],
      definitions: ["def:sibling", "def:omitted"],
      statements: ["prop:downstream", "thm:sibling"],
    });
  });

  it("recovers a visibly used symbol when free_symbols is incomplete", () => {
    const core = fixture();
    const target = core.statements.find(({ id }) => id === "thm:target")!;
    target.statement = "The target involving y holds";
    target.free_symbols = ["x"];
    const projected = projectFrozenCore(core, new Set(["thm:target"]));
    expect(projected.inline.symbols.map(({ name }) => name)).toEqual(["x", "y"]);
    expect(projected.inline.symbols.find(({ name }) => name === "y")).toBeDefined();
    expect(projected.manifest.omitted.symbols).toEqual(["z"]);
  });

  it("inlines catalog nodes cited only literally in TeX bodies", () => {
    const core = fixture();
    const target = core.statements.find(({ id }) => id === "thm:target")!;
    // Not in depends_on, free_symbols, or any symbol ref — a bare textual citation.
    target.statement = "The target holds by the construction in def:omitted";
    const projected = projectFrozenCore(core, new Set(["thm:target"]));
    expect(projected.inline.definitions.find(({ id }) => id === "def:omitted")).toBeDefined();
  });

  it("makes a stable snapshot hash while retaining selectively readable full fields", () => {
    const core = fixture();
    const first = serializeFrozenCoreSnapshot(core);
    const second = serializeFrozenCoreSnapshot(core);
    expect(first).toEqual(second);
    expect(first.sha256).toMatch(/^[a-f0-9]{64}$/);
    const snapshot = frozenCoreSnapshot(core) as any;
    expect(snapshot.tldr).toContain("retained only in the snapshot");
    expect(snapshot.bibliography).toEqual([{ key: "Ref", citation: "Reference" }]);
    expect(snapshot.statements[0].proof_tex).toBe("Immediate.");
    expect(snapshot.statements[0].revision).toMatch(/^rev:[a-f0-9]{64}$/);
  });
});
