import { describe, it, expect } from "vitest";
import { countTestCases } from "../src/shared/test_coverage.js";

describe("countTestCases", () => {
  it("counts plain it/test calls and modifier chains once each", () => {
    expect(countTestCases(`
      it("a", () => {});
      test("b", () => {});
      it.only("c", () => {});
      it.each([[1], [2]])("d %i", () => {});
    `)).toBe(4);
  });

  it("excludes skipped and todo cases so skipping registers as coverage loss", () => {
    expect(countTestCases(`
      it("live", () => {});
      it.skip("parked", () => {});
      test.todo("later");
      it.skip.each([[1]])("never %i", () => {});
    `)).toBe(1);
  });

  it("ignores test-like text in comments, strings, and template literals", () => {
    expect(countTestCases(`
      // it("commented out", () => {});
      /* test("block comment", () => {}); */
      const s = 'it("in a string", () => {})';
      const t = \`
      it("in a template literal", () => {})
      \`;
      it("real", () => {});
    `)).toBe(1);
  });

  it("excludes tests inside describe.skip/describe.todo so parking a suite registers as loss", () => {
    expect(countTestCases(`
      describe.skip("parked suite", () => {
        it("a", () => {});
        describe("nested", () => { it("b", () => {}); });
      });
      describe("live", () => { it("c", () => {}); });
    `)).toBe(1);
  });

  it("does not count describe blocks or unrelated identifiers", () => {
    expect(countTestCases(`
      describe("group", () => { it("real", () => {}); });
      submit("form", () => {});
      profit("x", () => {});
    `)).toBe(1);
  });
});
