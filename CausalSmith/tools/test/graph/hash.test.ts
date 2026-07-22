import { describe, it, expect } from "vitest";
import { statementHash } from "../../src/graph/hash.js";

describe("statementHash", () => {
  it("is whitespace-insensitive", () => {
    expect(statementHash("theorem  t1 :\n  A → B")).toBe(statementHash("theorem t1 : A → B"));
  });
  it("differs when content differs", () => {
    expect(statementHash("A → B")).not.toBe(statementHash("A → C"));
  });
  it("is a stable hex digest", () => {
    expect(statementHash("A → B")).toMatch(/^[0-9a-f]{40}$/);
  });
});
