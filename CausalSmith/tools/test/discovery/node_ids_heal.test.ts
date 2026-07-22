import { describe, it, expect } from "vitest";
import { healStatementId, STATEMENT_ID_KINDS } from "../../src/discovery/core/node_ids.js";
import { StatementSchema } from "../../src/discovery/core/schema.js";

describe("healStatementId", () => {
  it("heals an oeq id — the prefix the old inline copy omitted", () => {
    // StatementSchema ACCEPTS `oeq:`, so before this was canonicalized a bad-cased
    // oeq id was the one case that reached schema validation unhealed and aborted
    // an otherwise-clean discharge.
    expect(healStatementId("oeq:Bounded-Count Diameter")).toBe("oeq:bounded-count-diameter");
  });

  const KIND_FOR_PREFIX: Record<string, string> = {
    thm: "theorem", lem: "lemma", prop: "proposition",
    oeq: "openendedquestion", conj: "conjecture",
  };

  it("covers every prefix the statement schema accepts", () => {
    for (const kind of STATEMENT_ID_KINDS) {
      const healed = healStatementId(`${kind}:Foo Bar`);
      expect(healed).toBe(`${kind}:foo-bar`);
      expect(() =>
        // Kind must match the prefix: a thm:/prop:/oeq: node carrying kind "lemma" is
        // rejected, because orphan-pruning keys on kind and would silently delete it.
        StatementSchema.parse({ id: healed, kind: KIND_FOR_PREFIX[kind], statement: "s", status: "to-prove" }),
      ).not.toThrow();
    }
  });

  it("lowercases the prefix and collapses illegal runs", () => {
    expect(healStatementId("Lem:Ghat_envelope  valid")).toBe("lem:ghat-envelope-valid");
  });

  it("trims leading and trailing separators", () => {
    expect(healStatementId("thm:__alpha__")).toBe("thm:alpha");
  });

  it("returns null for a non-statement prefix, so assumptions and definitions are untouched", () => {
    expect(healStatementId("ass:iid-row")).toBeNull();
    expect(healStatementId("def:functionals")).toBeNull();
    expect(healStatementId("nonsense")).toBeNull();
  });

  it("is a no-op on an already-legal id", () => {
    expect(healStatementId("thm:gaussian-frontier")).toBe("thm:gaussian-frontier");
  });
});
