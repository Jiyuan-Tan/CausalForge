import { describe, expect, it } from "vitest";
import { remapResolvedDependencies, retargetDeletedDependency } from "../../src/discovery/core/oeq_edges.js";

describe("Q→T and delete-replacement edge rules", () => {
  it("an answer's own citation of its question inherits the question's edges; chains map once", () => {
    const replacement = new Map([["oeq:q1", "thm:t1"], ["oeq:q2", "thm:t2"]]);
    const qdeps = (id: string) => ({ "oeq:q2": ["oeq:q1", "def:a"], "oeq:q1": ["ass:b"] } as Record<string, string[]>)[id];
    expect(remapResolvedDependencies("thm:t2", ["oeq:q2", "def:a"], replacement, qdeps)).toEqual(["thm:t1", "def:a"]);
    expect(remapResolvedDependencies("thm:consumer", ["oeq:q2"], replacement, qdeps)).toEqual(["thm:t2"]);
    expect(remapResolvedDependencies("thm:t1", ["oeq:q1", "thm:t1"], replacement, qdeps)).toEqual(["ass:b"]);
  });
  it("a replacement citing the node it supersedes drops the edge instead of a self-edge", () => {
    expect(retargetDeletedDependency("lem:new", ["lem:old", "ass:a"], "lem:old", "lem:new")).toEqual(["ass:a"]);
    expect(retargetDeletedDependency("thm:main", ["lem:old", "lem:new"], "lem:old", "lem:new")).toEqual(["lem:new"]);
    expect(retargetDeletedDependency("thm:main", ["lem:old", "ass:a"], "lem:old", undefined)).toEqual(["ass:a"]);
  });
});
