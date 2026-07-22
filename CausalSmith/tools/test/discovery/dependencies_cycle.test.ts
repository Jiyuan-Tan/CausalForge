import { describe, it, expect } from "vitest";
import { wireStatementProofDependencies } from "../../src/discovery/core/dependencies.js";
import type { Core } from "../../src/discovery/core/schema.js";

/** Two lemmas whose prose MENTIONS the other — a rhetorical reference, not a dependency. */
function mutualMentions(): Core {
  return {
    title: "t",
    assumptions: [],
    definitions: [],
    bibliography: [],
    statements: [
      { id: "lem:a", kind: "lemma", status: "proved", statement: "S", depends_on: [], proof_tex: "By the dual of lem:b." },
      { id: "lem:b", kind: "lemma", status: "proved", statement: "S", depends_on: [], proof_tex: "By the dual of lem:a." },
    ],
  } as unknown as Core;
}

const cyclic = (c: Core): boolean => {
  const by = new Map(c.statements.map((s) => [s.id, s.depends_on ?? []]));
  return !!by.get("lem:a")?.includes("lem:b") && !!by.get("lem:b")?.includes("lem:a");
};

describe("wireStatementProofDependencies — cycle guard", () => {
  it("refuses to wire a mutual prose mention into a dependency cycle", () => {
    const core = mutualMentions();
    wireStatementProofDependencies(core);
    expect(cyclic(core)).toBe(false);
  });

  it("is idempotent, so wiring both before and after OEQ replacement is safe", () => {
    // stage0_solve calls this at TWO points. It previously used an inline copy without
    // the cycle guard at the first point, which created a cycle the second call could
    // not undo (it only declines to ADD one) — surfacing as a phantom G4 gate failure.
    const core = mutualMentions();
    wireStatementProofDependencies(core);
    const first = core.statements.map((s) => [...(s.depends_on ?? [])].sort());
    wireStatementProofDependencies(core);
    expect(core.statements.map((s) => [...(s.depends_on ?? [])].sort())).toEqual(first);
    expect(cyclic(core)).toBe(false);
  });

  it("still wires a genuine one-way citation", () => {
    const core = mutualMentions();
    core.statements[1].proof_tex = "Standalone argument.";
    wireStatementProofDependencies(core);
    expect(core.statements[0].depends_on).toContain("lem:b");
    expect(core.statements[1].depends_on ?? []).not.toContain("lem:a");
  });

  it("wires a literal id in the formal claim even when the proof omits it", () => {
    const core = mutualMentions();
    core.statements[0].statement = String.raw`The conditions in \texttt{lem:b} imply the result.`;
    core.statements[0].proof_tex = "Standalone argument.";
    core.statements[1].proof_tex = "Standalone argument.";

    wireStatementProofDependencies(core);

    expect(core.statements[0].depends_on).toContain("lem:b");
  });
});
