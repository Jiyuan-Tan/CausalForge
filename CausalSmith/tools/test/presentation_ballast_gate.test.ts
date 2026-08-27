import { describe, expect, it } from "vitest";
import { unconsumedStatementNodes } from "../src/presentation/graph_view.js";

/** Minimal graph shape: only the fields unconsumedStatementNodes touches. */
const node = (id: string, over: Record<string, unknown> = {}) => ({
  id,
  kind: "theorem",
  provenance: "from-note",
  nl: { frozen: true, statement: `statement of ${id}` },
  proof: { state: "complete" },
  ...over,
});

const graph = (nodes: unknown[], edges: unknown[] = []) => ({ nodes, edges }) as never;

describe("unconsumedStatementNodes (P2 ballast gate detector)", () => {
  it("flags a frozen theorem nothing consumes", () => {
    const g = graph([node("thm:headline"), node("prop:ballast")]);
    expect(unconsumedStatementNodes(g).map((n: { id: string }) => n.id).sort()).toEqual([
      "prop:ballast",
      "thm:headline",
    ]);
  });

  it("a proof-uses or statement-uses in-edge counts as consumption", () => {
    const g = graph(
      [node("thm:main"), node("lem:used"), node("lem:stated")],
      [
        { kind: "proof-uses", from: "thm:main", to: "lem:used" },
        { kind: "statement-uses", from: "thm:main", to: "lem:stated" },
      ],
    );
    expect(unconsumedStatementNodes(g).map((n: { id: string }) => n.id)).toEqual(["thm:main"]);
  });

  it("a textual mention in another node's statement/proof counts as consumption", () => {
    const g = graph([
      node("thm:main", { proof: { state: "complete", tex: "by lem:helper and algebra" } }),
      node("lem:helper"),
    ]);
    expect(unconsumedStatementNodes(g).map((n: { id: string }) => n.id)).toEqual(["thm:main"]);
  });

  it("setup-node prose cannot launder ballast (two-category incident)", () => {
    const g = graph([
      node("prop:ballast"),
      node("S2", {
        kind: "setup",
        nl: { frozen: true, statement: "…where prop:ballast VERIFIES the conditions directly" },
      }),
    ]);
    expect(unconsumedStatementNodes(g).map((n: { id: string }) => n.id)).toEqual(["prop:ballast"]);
  });

  it("a witness definition consumed only by ballast rides along; an acknowledged headline rescues its defs", () => {
    const g = graph(
      [node("prop:ballast"), node("def:witness", { kind: "definition" })],
      [{ kind: "proof-uses", from: "prop:ballast", to: "def:witness" }],
    );
    expect(unconsumedStatementNodes(g).map((n: { id: string }) => n.id).sort()).toEqual([
      "def:witness",
      "prop:ballast",
    ]);
    // acknowledged as a legitimate headline → its definition is not ballast
    expect(
      unconsumedStatementNodes(g, new Set(["prop:ballast"])).map((n: { id: string }) => n.id),
    ).toEqual(["prop:ballast"]);
  });

  it("boundary-aware matching: a longer id's mention does not consume its prefix id", () => {
    const g = graph([
      node("thm:frontier-upper"),
      node("thm:main", { proof: { state: "complete", tex: "extends thm:frontier-upper-all-d" } }),
      node("thm:frontier-upper-all-d"),
    ]);
    const ids = unconsumedStatementNodes(g).map((n: { id: string }) => n.id);
    expect(ids).toContain("thm:frontier-upper"); // NOT rescued by the -all-d mention
    expect(ids).not.toContain("thm:frontier-upper-all-d"); // genuinely mentioned
  });

  it("a lemma consumed only by a flagged headline is still consumed (no spine cascade)", () => {
    const g = graph(
      [node("thm:headline"), node("lem:spine")],
      [{ kind: "proof-uses", from: "thm:headline", to: "lem:spine" }],
    );
    expect(unconsumedStatementNodes(g).map((n: { id: string }) => n.id)).toEqual(["thm:headline"]);
  });

  it("exempts non-frozen, non-theorem-family, and non-from-note nodes", () => {
    const g = graph([
      node("thm:demoted", { nl: { frozen: false, statement: "s" } }),
      node("ass:overlap", { kind: "assumption" }),
      node("def:model", { kind: "definition" }),
      node("lem:aux", { provenance: "auxiliary" }),
    ]);
    expect(unconsumedStatementNodes(g)).toEqual([]);
  });
});
