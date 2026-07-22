// Cross-paper references vs. citations.
//
// The D0 consistency gate exists to catch laundering-by-citation: a proof that
// INVOKES a helper the solver never EMITTED reads as "fully proved" while hiding an
// unproven step. It found those by scanning prose for `lem:`/`thm:` ids.
//
// That scan could not tell a CITATION (`lem:foo` — "this core proves it, I invoke
// it") from a MENTION (`other_paper/lem:foo` — "another paper proved it"). A node
// crediting the source of a generic step it RE-PROVED here was reported as citing an
// un-emitted member; the gate invalidated its proof and the theorems depending on it
// aborted the solve. Naming where an idea came from is not a hole in your proof.
//
// The two properties below must hold TOGETHER — dropping the second would "fix" the
// false positive by disabling the anti-laundering check it exists to perform.

import { readFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";
import { findDanglingCitations } from "../../src/discovery/stages/d0_working.js";
import { checkProseConsistency } from "../../src/discovery/core/prose_consistency.js";
import { extractNodeRefs, extractCitationRefs } from "../../src/discovery/core/node_ids.js";
import type { Core } from "../../src/discovery/core/schema.js";

/** A core holding one proved statement plus whatever ids are already members. */
function coreWith(
  node: { id: string; statement?: string; proof_tex?: string; external_refs?: string[] },
  members: string[] = [],
): Core {
  return {
    statements: [
      { kind: "lemma", status: "proved", depends_on: [], ...node },
      ...members.map((id) => ({
        id,
        kind: "lemma" as const,
        status: "proved" as const,
        statement: "member",
        depends_on: [],
      })),
    ],
    definitions: [],
    assumptions: [],
  } as unknown as Core;
}

describe("findDanglingCitations — cross-paper references", () => {
  it("does not report a `<paper>/<node>` reference as a dangling citation", () => {
    const core = coreWith({
      id: "lem:comparator",
      statement:
        "The in-repository template stat_cot_observational_efficiency/lem:vanishing-variance-studentization " +
        "has the following generic content.",
      proof_tex: "Proved here independently.",
    });
    expect(findDanglingCitations(core)).toEqual([]);
  });

  it("handles the LaTeX-escaped underscores a qid carries in prose", () => {
    const core = coreWith({
      id: "lem:comparator",
      statement: String.raw`The template \texttt{stat\_cot\_observational\_efficiency/lem:vanishing-variance-studentization} is generic.`,
      proof_tex: "Proved here.",
    });
    expect(findDanglingCitations(core)).toEqual([]);
  });

  it("STILL reports a bare un-emitted id — the anti-laundering check is intact", () => {
    // The whole point of the gate. A citation to a lemma nobody proved IS a hole.
    const core = coreWith({
      id: "lem:consumer",
      statement: "Auxiliary.",
      proof_tex: "By lem:never-emitted the bound follows.",
    });
    expect(findDanglingCitations(core)).toEqual([
      { node: "lem:consumer", ref: "lem:never-emitted" },
    ]);
  });

  it("accepts a bare mention that the node declares in external_refs", () => {
    const core = coreWith({
      id: "lem:comparator",
      statement: "Compare with lem:vanishing-variance-studentization of the sibling run.",
      proof_tex: "Proved here.",
      external_refs: ["stat_cot_observational_efficiency/lem:vanishing-variance-studentization"],
    });
    expect(findDanglingCitations(core)).toEqual([]);
  });

  it("resolves a qualified path naming a node THIS core does contain", () => {
    const core = coreWith(
      { id: "lem:a", statement: "See this_paper/lem:known.", proof_tex: "By lem:known." },
      ["lem:known"],
    );
    expect(findDanglingCitations(core)).toEqual([]);
  });
});

describe("the prose lint reads ids the same way the gate does", () => {
  // The gate fix alone was incomplete: `prose_consistency.ts` held a FIFTH private copy
  // of the id regex and repeated the misread in `related_work`. Positioning prose names
  // other papers by construction, so it meets qualified references MORE often than the
  // gate does. Same input, same answer — that is the point of one shared extractor.
  const proseCore = (related: string, external?: string[]): Core =>
    ({
      statements: [
        {
          id: "thm:main",
          kind: "theorem",
          status: "proved",
          statement: "Main.",
          depends_on: [],
          ...(external ? { external_refs: external } : {}),
        },
      ],
      definitions: [],
      assumptions: [],
      related_work: related,
    }) as unknown as Core;

  it("does not flag a `<paper>/<node>` reference in positioning prose", () => {
    const w = checkProseConsistency(
      proseCore("Compare with stat_cot_observational_efficiency/lem:vanishing-variance-studentization."),
    );
    expect(w.filter((x) => x.code === "PROSE-DANGLING-REF")).toEqual([]);
  });

  it("does not flag a bare id the core declares in external_refs", () => {
    const w = checkProseConsistency(
      proseCore("Compare with lem:vanishing-variance-studentization.", [
        "stat_cot_observational_efficiency/lem:vanishing-variance-studentization",
      ]),
    );
    expect(w.filter((x) => x.code === "PROSE-DANGLING-REF")).toEqual([]);
  });

  it("STILL flags a genuinely stale id left by a rename", () => {
    const w = checkProseConsistency(proseCore("As shown in thm:renamed-away, the bound holds."));
    expect(w.filter((x) => x.code === "PROSE-DANGLING-REF")).toHaveLength(1);
  });
});

describe("in-repository prior art is the ACCEPTED BANK, not an active run", () => {
  // An active run is unreviewed, unbanked, and free to change or be discarded. Asking a
  // note to position itself against one anchors its novelty claim to something that may
  // never hold — and it was a comparator against an active run that produced the
  // cross-paper reference the gate then misread.
  it("scopes the D0.5 novelty comparison to doc/research/_bank/accepted/", async () => {
    const review = (
      await readFile(new URL("../../src/discovery/prompts/D0.5/stage0_5_review.txt", import.meta.url), "utf8")
    ).replace(/\s+/g, " ");

    expect(review).toContain("doc/research/_bank/accepted/");
    expect(review).toContain("Never raise a comparator finding naming an active run");
    expect(review).toContain("BANKED in-repository prior work");
  });

  it("tells the D0 solver to declare a cross-paper mention instead of citing it", async () => {
    const solve = (
      await readFile(new URL("../../src/discovery/prompts/D0/stage0_solve.txt", import.meta.url), "utf8")
    ).replace(/\s+/g, " ");

    expect(solve).toContain("external_refs");
    expect(solve).toContain("Do NOT put the other paper's id in `depends_on`");
  });
});

describe("the two extractors keep opposite semantics", () => {
  const prose = "cites lem:bare and mentions other_paper/lem:qualified";

  it("citation extraction excludes the qualified reference", () => {
    expect(extractCitationRefs(prose)).toEqual(["lem:bare"]);
  });

  it("reachability extraction still sees BOTH — it may never lose an inbound edge", () => {
    // `gate.ts`'s aliveness closure and `pruneOrphanLemmas` DELETE a node whose last
    // inbound prose edge disappears. If this extractor ever narrowed to match the
    // citation one, a node referenced only in qualified form would be pruned — a live
    // -node deletion, the failure mode core/node_ids.ts is written to prevent.
    expect(extractNodeRefs(prose)).toEqual(["lem:bare", "lem:qualified"]);
  });
});
