import { describe, it, expect } from "vitest";
import { reachableFrom, dependentsOf } from "../../src/discovery/core/graph_walk.js";
import type { Core } from "../../src/discovery/core/schema.js";

function coreOf(edges: Record<string, string[]>): Core {
  return {
    title: "t",
    assumptions: [],
    definitions: [],
    bibliography: [],
    statements: Object.entries(edges).map(([id, depends_on]) => ({
      id,
      kind: "lemma",
      status: "proved",
      statement: "s",
      depends_on,
    })),
  } as unknown as Core;
}

describe("reachableFrom", () => {
  it("includes the roots and follows edges transitively", () => {
    const g: Record<string, string[]> = { a: ["b"], b: ["c"], c: [] };
    expect([...reachableFrom(["a"], (id) => g[id] ?? [])].sort()).toEqual(["a", "b", "c"]);
  });

  it("terminates on a cycle instead of hanging", () => {
    // A hand-authored proto edit can introduce a cycle; a guardless walk turns that
    // into a hung pipeline rather than a diagnosable error.
    const g: Record<string, string[]> = { a: ["b"], b: ["a"] };
    expect([...reachableFrom(["a"], (id) => g[id] ?? [])].sort()).toEqual(["a", "b"]);
  });

  it("tolerates edges to unknown ids", () => {
    expect([...reachableFrom(["a"], () => ["ghost"])].sort()).toEqual(["a", "ghost"]);
  });
});

describe("dependentsOf", () => {
  it("returns the transitive consumers of an assumption", () => {
    const core = coreOf({
      "lem:direct": ["ass:x"],
      "thm:indirect": ["lem:direct"],
      "lem:unrelated": ["ass:y"],
    });
    expect([...dependentsOf(core, ["ass:x"])].sort()).toEqual(["lem:direct", "thm:indirect"]);
  });

  it("excludes the targets themselves", () => {
    // An assumption is not a proof that needs redoing.
    const core = coreOf({ "lem:a": ["ass:x"] });
    expect(dependentsOf(core, ["ass:x"]).has("ass:x")).toBe(false);
  });

  it("includes a target that some other statement genuinely reaches", () => {
    const core = coreOf({ "lem:a": ["ass:x"], "thm:b": ["lem:a"] });
    expect([...dependentsOf(core, ["ass:x", "lem:a"])].sort()).toEqual(["thm:b"]);
  });

  it("returns empty when nothing consumes the target", () => {
    const core = coreOf({ "lem:a": ["ass:other"] });
    expect([...dependentsOf(core, ["ass:x"])]).toEqual([]);
  });

  it("terminates on a dependency cycle", () => {
    const core = coreOf({ "lem:a": ["ass:x", "lem:b"], "lem:b": ["lem:a"] });
    expect([...dependentsOf(core, ["ass:x"])].sort()).toEqual(["lem:a", "lem:b"]);
  });
});
