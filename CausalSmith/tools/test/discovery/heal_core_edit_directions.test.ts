import { describe, expect, it } from "vitest";
import { healCoreEditDirections } from "../../src/discovery/solve/dispatch.js";

describe("D0 ingestion — core-edit direction is derived from kind", () => {
  it("fills an omitted direction and leaves a present one untouched", () => {
    const body = {
      proposed_core_edits: [
        { kind: "symbol-delete", name: "q", reason: "unused" },
        { kind: "definition-replace", id: "def:x", proposed: {}, reason: "fix" },
        { kind: "assumption-delete", id: "ass:a", reason: "r", direction: "correct" },
      ],
    };
    healCoreEditDirections(body);
    expect(body.proposed_core_edits.map((e) => e.direction)).toEqual([
      "delete-obsolete", "correct", "correct",
    ]);
  });
  it("ignores bodies without a core-edit array", () => {
    expect(() => healCoreEditDirections({ proofs: [] })).not.toThrow();
    expect(() => healCoreEditDirections(null)).not.toThrow();
  });
});
