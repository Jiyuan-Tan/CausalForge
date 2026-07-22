import { describe, it, expect } from "vitest";
import { findDanglingCitations } from "../../src/discovery/stages/d0_working.js";
import type { Core } from "../../src/discovery/core/schema.js";

/** The post-resolution core: the OEQ has been REPLACED by its answer theorem, whose
 *  proof still names the question it settles. */
function resolvedCore(): Core {
  return {
    title: "t",
    assumptions: [],
    definitions: [],
    bibliography: [],
    statements: [
      {
        id: "thm:bounded-count-diameter-obstruction",
        kind: "theorem",
        status: "proved",
        statement: "S",
        depends_on: [],
        proof_tex: "This settles oeq:bounded-count-diameter in the negative.",
      },
    ],
  } as unknown as Core;
}

describe("findDanglingCitations — resolved OEQs", () => {
  it("reports the answered OEQ as dangling when it is not declared known", () => {
    // Establishes the test is not vacuous: without the resolution map, this IS a hit.
    expect(findDanglingCitations(resolvedCore())).toEqual([
      { node: "thm:bounded-count-diameter-obstruction", ref: "oeq:bounded-count-diameter" },
    ]);
  });

  it("does NOT report it once the resolution map is supplied", () => {
    // A resolved OEQ is answered, not missing. Reporting it drove the auto-heal to issue
    // an unsatisfiable directive ("emit the cited helper as a defined member"), which the
    // solver could only obey by re-authoring a D-1-frozen node — which the
    // silent-alteration guard then refused. The run deadlocked and re-resuming
    // reproduced it.
    expect(
      findDanglingCitations(resolvedCore(), { alsoKnown: ["oeq:bounded-count-diameter"] }),
    ).toEqual([]);
  });

  it("matches case-insensitively, as citation extraction lowercases refs", () => {
    expect(
      findDanglingCitations(resolvedCore(), { alsoKnown: ["OEQ:Bounded-Count-Diameter"] }),
    ).toEqual([]);
  });

  it("still reports a genuinely undefined helper alongside a resolved OEQ", () => {
    // The exemption must not blanket-suppress the gate it is narrowing.
    const core = resolvedCore();
    core.statements[0].proof_tex = "By lem:never-emitted, this settles oeq:bounded-count-diameter.";
    expect(
      findDanglingCitations(core, { alsoKnown: ["oeq:bounded-count-diameter"] }),
    ).toEqual([{ node: "thm:bounded-count-diameter-obstruction", ref: "lem:never-emitted" }]);
  });

  it("is unchanged when no resolutions exist", () => {
    const core = resolvedCore();
    core.statements[0].proof_tex = "By lem:never-emitted.";
    expect(findDanglingCitations(core, { alsoKnown: [] })).toEqual([
      { node: "thm:bounded-count-diameter-obstruction", ref: "lem:never-emitted" },
    ]);
  });
});
