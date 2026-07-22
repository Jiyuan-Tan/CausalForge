// The final-assembly snapshot refresh must leave PARTIAL records alone, matching the
// in-merge refresh (merge.ts passes skipPartial) and the documented contract in
// working_writer.ts: "a partial record's snapshot describes what the agent was asked
// to extend, and refreshing it would quietly retarget the obligation." Concretely, a
// partial carried across a statement change keeps its OLD-basis snapshot so the next
// dispatch can warn "this partial argued a PREVIOUS statement — realign"; the final
// pass rewriting that snapshot to the current text silently suppressed the warning.

import { describe, it, expect } from "vitest";
import { runFinalAssemblyGates } from "../../src/discovery/solve/gates.js";
import type { SolveRoundContext } from "../../src/discovery/solve/context.js";
import { snapshotMember } from "../../src/discovery/stages/d0_working.js";
import type { Core, CoreStatement } from "../../src/discovery/core/schema.js";

const stmt = (id: string, statement: string): CoreStatement =>
  ({ id, kind: "theorem", statement, depends_on: [], status: "to-prove" }) as unknown as CoreStatement;

const makeCore = (statements: CoreStatement[]): Core =>
  ({
    qid: "stat_fag",
    specialization: "v1",
    cluster: "stat",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements,
    target_estimand: "tau",
    bibliography: [],
  }) as unknown as Core;

describe("runFinalAssemblyGates snapshot refresh", () => {
  it("refreshes settled records but leaves a partial's old-basis snapshot untouched", () => {
    const oldA = stmt("thm:a", "OLD claim text");
    const newA = stmt("thm:a", "NEW claim text");
    const oldB = stmt("lem:b", "OLD helper text");
    const newB = stmt("lem:b", "NEW helper text");
    const proto = makeCore([newA, newB]);
    const core = makeCore([newA, newB]);
    const next = {
      round: 1,
      solved: {
        "thm:a": { proof_tex: "partial argument", snapshot: snapshotMember(proto, oldA), partial: true },
        "lem:b": { proof_tex: "finished proof", snapshot: snapshotMember(proto, oldB) },
      },
    };

    runFinalAssemblyGates({ proto, core, next, semanticManifest: null } as unknown as SolveRoundContext);

    expect(next.solved["lem:b"].snapshot.stmt, "settled record must track the rewrite").toBe("NEW helper text");
    expect(next.solved["thm:a"].snapshot.stmt, "partial must keep the basis it argued").toBe("OLD claim text");
  });
});
