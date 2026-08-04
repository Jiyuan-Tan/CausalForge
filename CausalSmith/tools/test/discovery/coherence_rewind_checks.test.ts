// The 2026-07 cross-stage rewind audit's contradiction classes, RE-POINTED at the
// Phase-1 store consolidation (2026-07-30 migration plan): the checks that used
// to DETECT these states after the fact are retired, because the published core
// is now `assembleCore(proto, working)` and the states are unrepresentable or
// auto-resolved. The fixtures stay derived from the same production artifacts
// as the original detector tests:
//  - proved-not-partial: the REAL terminal state of the banked run
//    doc/research/_bank/downgraded/exp_saturation_skew_threshold_v1 — core.json
//    published `oeq:full-branch-optimizer-map` as `proved` while d0_working.json
//    carried `partial:true` over DIFFERENT bytes, and the run banked with the
//    contradiction. Under the render, the record's partiality DERIVES the
//    published status, so the contradiction cannot be written.
//  - resolved-OEQ retirement: the REAL healthy resolution shape of
//    doc/research/active/stat_reversekl_two_coverage
//    (`oeq:full-feasible-frontier` → `thm:full-feasible-frontier-answer`).

import { describe, it, expect } from "vitest";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { normalizeWorkingState } from "../../src/discovery/stages/d0_working.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

// ── proved-not-partial: trimmed from exp_saturation_skew_threshold_v1 ────────────────

const SATURATION_OEQ = {
  id: "oeq:full-branch-optimizer-map",
  kind: "openendedquestion",
  status: "to-prove",
  statement:
    "Certified delivered content plus the remaining atlas-compression question. For every exact algebraic or symbolic parameter point theta=(pbar, V_1, V_3, V_4) ...",
  depends_on: ["thm:global-certificate"],
};

const SATURATION_SIBLING = {
  id: "thm:global-certificate",
  kind: "theorem",
  status: "to-prove",
  statement: "The global certificate holds.",
  depends_on: [],
};

function saturationProto(): Core {
  return {
    qid: "exp_saturation_skew_threshold",
    specialization: "v1",
    cluster: "experimentation",
    symbols: [], assumptions: [], definitions: [],
    statements: [SATURATION_SIBLING, SATURATION_OEQ],
    bibliography: [],
    target_estimand: "tau",
  } as unknown as Core;
}

function saturationWorking(): WorkingState {
  const snap = (stmt: string) => ({ stmt, depends_on: [], defs: {}, assumptions: {} });
  return {
    round: 9,
    solved: {
      "thm:global-certificate": {
        proof_tex: "Certified by the discharged DAG.",
        snapshot: snap(SATURATION_SIBLING.statement),
      },
      // The real cursor record: partial, over different bytes than the old
      // published core claimed to have proved.
      "oeq:full-branch-optimizer-map": {
        proof_tex:
          "For every theta=(pbar,V_1,V_3,V_4) with 0<=pbar<=1, thm:constructive-optimal-design-algorithm returns ...",
        snapshot: snap("Certified delivered content plus the remaining atlas-compression question. Over ..."),
        partial: true,
      },
    },
    resolved_oeqs: {},
  } as unknown as WorkingState;
}

describe("proved-not-partial is unrepresentable in the render", () => {
  it("the real banked contradiction cannot be published: partial record ⇒ open node", () => {
    const out = assembleCore(saturationProto(), saturationWorking());
    const node = out.statements.find((s) => s.id === "oeq:full-branch-optimizer-map")!;
    // The old core.json said `proved`; the render derives from the record.
    expect(node.status).toBe("to-prove");
    // The best-partial bytes ride along as prior progress, from the CURSOR —
    // the store the next round actually carries.
    expect(node.proof_tex).toContain("thm:constructive-optimal-design-algorithm");
  });

  it("the finished sibling still publishes `proved` from its full record", () => {
    const out = assembleCore(saturationProto(), saturationWorking());
    expect(out.statements.find((s) => s.id === "thm:global-certificate")!.status).toBe("proved");
  });
});

// ── resolved-OEQ retirement: derived from stat_reversekl_two_coverage ────────────────

const ANSWER = {
  id: "thm:full-feasible-frontier-answer",
  kind: "theorem",
  status: "proved",
  statement:
    "Fix \\(d\\ge4\\), \\(\\eta>0\\), and a public experiment \\(\\mathfrak E\\). Nonemptiness of \\(\\mathcal M_{...}\\) characterizes the feasible pairs ...",
  depends_on: [],
  proof_tex: "Combine the shell certificate with the index-insufficiency theorem.",
};

const SOURCE_ID = "oeq:full-feasible-frontier";

function frontierStores(): { proto: Core; after: WorkingState } {
  const proto = {
    qid: "stat_reversekl_two_coverage",
    specialization: "linear_exact_shell",
    cluster: "stat",
    symbols: [], assumptions: [], definitions: [],
    // The frozen proto still holds the question — that is exactly why the old
    // check existed: assembly had to filter it, and one path forgot.
    statements: [
      {
        id: SOURCE_ID,
        kind: "openendedquestion",
        status: "to-prove",
        statement:
          "For the fixed public experiment \\(\\mathfrak E\\), characterize which pairs in the varying-design feasible region are attainable ...",
        depends_on: [],
      },
    ],
    bibliography: [],
    target_estimand: "tau",
  } as unknown as Core;
  const after = {
    round: 12,
    solved: {
      [ANSWER.id]: {
        proof_tex: ANSWER.proof_tex,
        snapshot: { stmt: ANSWER.statement, depends_on: [], defs: {}, assumptions: {} },
        node: ANSWER,
        owner: SOURCE_ID,
      },
    },
    resolved_oeqs: {
      [SOURCE_ID]: {
        theorem_id: ANSWER.id,
        source_fingerprint: JSON.stringify({
          kind: "openendedquestion",
          statement:
            "For the fixed public experiment \\(\\mathfrak E\\), characterize which pairs in the varying-design feasible region are attainable ...",
          depends_on: [],
        }),
      },
    },
  } as unknown as WorkingState;
  return { proto, after };
}

describe("resolved-OEQ retirement is structural in the render", () => {
  it("an answered question can never appear as a live core node — the render filters it", () => {
    const { proto, after } = frontierStores();
    const out = assembleCore(proto, after);
    expect(out.statements.some((s) => s.id === SOURCE_ID)).toBe(false);
    expect(out.statements.some((s) => s.id === ANSWER.id)).toBe(true);
  });

  it("a surviving source RECORD is auto-resolved at the write boundary", () => {
    const { after } = frontierStores();
    after.solved[SOURCE_ID] = {
      proof_tex: "stale bytes",
      snapshot: { stmt: "the question text", depends_on: [], defs: {}, assumptions: {} },
    } as unknown as WorkingState["solved"][string];
    normalizeWorkingState(after);
    expect(after.solved[SOURCE_ID]).toBeUndefined();
    expect(after.solved[ANSWER.id]).toBeDefined();
  });
});
