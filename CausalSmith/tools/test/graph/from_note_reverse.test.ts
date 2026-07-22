import { describe, it, expect } from "vitest";
import { nodeIdToObjId, objIdToNodeId } from "../../src/graph/from_note.js";

describe("nodeIdToObjId", () => {
  it("inverts objIdToNodeId for P/L/T/A/S incl. suffixes", () => {
    for (const obj of ["T-1", "P-10", "L-7", "A-2", "S-1", "P-1b", "L-0a"]) {
      expect(nodeIdToObjId(objIdToNodeId(obj))).toBe(obj);
    }
  });
  it("passes through unprefixed ids", () => {
    expect(nodeIdToObjId("setup")).toBe("setup");
    expect(nodeIdToObjId("aux_overlapBound")).toBe("aux_overlapBound");
  });
});
