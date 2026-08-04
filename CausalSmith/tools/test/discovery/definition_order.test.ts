import { describe, expect, it } from "vitest";
import { topologicallyOrderDefinitions } from "../../src/discovery/core/definition_order.js";
import type { CoreDefinition } from "../../src/discovery/core/schema.js";

const definition = (id: string, construction: string, inputs?: string[]): CoreDefinition => ({
  id,
  name: id,
  construction,
  ...(inputs ? { inputs } : {}),
});

describe("topologicallyOrderDefinitions", () => {
  it("moves an appended prerequisite before existing consumers without changing payloads", () => {
    const consumer = definition("def:region", "Laws in def:constrained-model.", ["def:constrained-model"]);
    const unrelated = definition("def:unrelated", "U");
    const prerequisite = definition("def:constrained-model", "M");
    const input = [consumer, unrelated, prerequisite];
    const ordered = topologicallyOrderDefinitions(input);
    expect(ordered.map((item) => item.id)).toEqual([
      "def:unrelated", "def:constrained-model", "def:region",
    ]);
    expect(new Set(ordered)).toEqual(new Set(input));
  });

  it("detects literal construction references and preserves ties", () => {
    const input = [
      definition("def:a", "Uses def:c."),
      definition("def:b", "B"),
      definition("def:c", "C"),
    ];
    expect(topologicallyOrderDefinitions(input).map((item) => item.id))
      .toEqual(["def:b", "def:c", "def:a"]);
  });

  it("fails closed on duplicate or cyclic definitions", () => {
    const cyclic = [
      definition("def:a", "A", ["def:b"]),
      definition("def:b", "B", ["def:a"]),
    ];
    expect(() => topologicallyOrderDefinitions(cyclic)).toThrow(/cyclic/);
    const duplicate = [definition("def:a", "A"), definition("def:a", "A2")];
    expect(() => topologicallyOrderDefinitions(duplicate)).toThrow(/duplicate/);
  });
});
