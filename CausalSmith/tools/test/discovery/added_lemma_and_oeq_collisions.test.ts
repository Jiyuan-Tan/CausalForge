// Two silent-drop sites found by the D-stage static audit, 2026-07-20. Both wrote or
// discarded content with no diagnostic, so the orchestrator could not see it happen.

import { describe, it, expect } from "vitest";
import { CoreSchema } from "../../src/discovery/core/schema.js";

describe("an OEQ answer collision would produce a duplicate statement id", () => {
  it("CoreSchema now rejects the core that the unguarded push would have written", () => {
    // Two resolutions naming the same answer theorem pushed twice. Every consumer keys
    // by id, so one record wins silently while `recordProof` overwrites the single
    // working entry -- the second answer vanishes with no error.
    const thm = (statement: string) => ({
      id: "thm:answer", kind: "theorem", statement, depends_on: [],
      status: "proved", proof_tex: "QED.",
    });
    const core = {
      qid: "q", symbols: [], assumptions: [], definitions: [],
      statements: [thm("answer to A"), thm("answer to B")],
      target_estimand: "tau", bibliography: [],
    };
    const r = CoreSchema.safeParse(core);
    expect(r.success).toBe(false);
    if (!r.success) expect(JSON.stringify(r.error.issues)).toMatch(/duplicate statement id\(s\): thm:answer/);
  });
});

describe("an added helper reusing an id for a DIFFERENT claim", () => {
  // The unguarded path discarded the new node silently while the proof citing that id had
  // already been recorded meaning the NEW claim -- leaving the proof resting on a
  // statement it never argued. The guard withholds it and names it instead.
  it("a core holding one claim per id still validates", () => {
    const core = {
      qid: "q", symbols: [], assumptions: [], definitions: [],
      statements: [{
        id: "lem:x", kind: "lemma", statement: "claim A", depends_on: [],
        status: "proved", proof_tex: "P",
      }],
      target_estimand: "tau", bibliography: [],
    };
    expect(CoreSchema.safeParse(core).success).toBe(true);
  });
});
