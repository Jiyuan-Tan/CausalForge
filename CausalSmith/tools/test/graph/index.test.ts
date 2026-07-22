import { describe, it, expect } from "vitest";
import * as graph from "../../src/graph/index.js";

describe("public API", () => {
  it("re-exports the core surface", () => {
    for (const name of [
      "createEmptyGraph", "graphPath", "loadGraph", "saveGraph",
      "addNode", "addEdge", "addAssumption", "setLean", "setProof", "markPassed", "setNodeReview",
      "extractFromLean", "validate", "dirtyFrontier", "toMarkdown", "toDot", "statementHash",
    ]) {
      expect(typeof (graph as Record<string, unknown>)[name]).toBe("function");
    }
  });
});
