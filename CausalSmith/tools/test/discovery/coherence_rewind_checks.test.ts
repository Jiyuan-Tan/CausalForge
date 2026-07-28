// Cross-store coherence checks added after the 2026-07 cross-stage rewind audit.
//
// FIXTURES ARE DERIVED FROM PRODUCTION ARTIFACTS, not authored from belief (the previous
// attempt's tests passed while testing nothing because their fixtures were invented):
//  - the proved-not-partial case is the REAL terminal state of the banked run
//    doc/research/_bank/downgraded/exp_saturation_skew_threshold_v1 — core.json publishes
//    `oeq:full-branch-optimizer-map` as `status:"proved"` (with proof bytes) while
//    d0_working.json carries `partial:true` over DIFFERENT bytes; the run banked with the
//    contradiction because the discharge gate counts only `to-prove`.
//  - the resolved-OEQ cases start from the REAL healthy resolution in
//    doc/research/active/stat_reversekl_two_coverage (`oeq:full-feasible-frontier` →
//    `thm:full-feasible-frontier-answer`: source absent from core.statements AND from
//    solved) and mutate exactly the one property under test.
// A corpus scan over all 36 real (core.json, d0_working.json) pairs under
// doc/research/{active,_bank} showed ZERO hits for the two OEQ checks and exactly the
// one genuine hit above for proved-not-partial.

import { describe, it, expect } from "vitest";
import { checkRoundInvariants } from "../../src/discovery/core/coherence.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

const codes = (v: ReturnType<typeof checkRoundInvariants>): string[] => v.map((x) => x.code);

// ── proved-not-partial: trimmed from exp_saturation_skew_threshold_v1 ────────────────

const SATURATION_NODE = {
  id: "oeq:full-branch-optimizer-map",
  kind: "openendedquestion",
  status: "proved",
  statement:
    "Certified delivered content plus the remaining atlas-compression question. For every exact algebraic or symbolic parameter point theta=(pbar, V_1, V_3, V_4) ...",
  depends_on: ["thm:global-certificate"],
  proof_tex:
    "Proof. Fix an exact algebraic or symbolic parameter point theta=(pbar,V_1,V_3,V_4) with 0<=pbar<=1. ...",
};

const SATURATION_SIBLING = {
  id: "thm:global-certificate",
  kind: "theorem",
  status: "proved",
  statement: "The global certificate holds.",
  depends_on: [],
  proof_tex: "Certified by the discharged DAG.",
};

function saturationCore(): Core {
  return {
    qid: "exp_saturation_skew_threshold",
    specialization: "v1",
    cluster: "experimentation",
    symbols: [], assumptions: [], definitions: [],
    statements: [SATURATION_SIBLING, SATURATION_NODE],
    bibliography: [],
  } as unknown as Core;
}

function saturationWorking(): WorkingState {
  const snap = (stmt: string) => ({ stmt, depends_on: [], defs: {}, assumptions: {} });
  return {
    round: 9,
    solved: {
      "thm:global-certificate": {
        proof_tex: SATURATION_SIBLING.proof_tex,
        snapshot: snap(SATURATION_SIBLING.statement),
      },
      // The real cursor record: partial, over DIFFERENT bytes than the published core.
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

describe("proved-not-partial", () => {
  it("flags the real banked contradiction: core publishes `proved` over a partial cursor record", () => {
    const core = saturationCore();
    const after = saturationWorking();
    const got = checkRoundInvariants({ proto: core, core, after });
    const hit = got.find((v) => v.code === "proved-not-partial");
    expect(hit).toBeDefined();
    expect(hit!.ids).toEqual(["oeq:full-branch-optimizer-map"]);
  });

  it("stays silent on `cited` + partial — the deliberate awaiting-revalidation state", () => {
    const core = saturationCore();
    // A cited leaf awaiting revalidation is carried as partial debt ON PURPOSE
    // (solve/context.ts frozen-member carry); it must not warn.
    (core.statements[1] as { status: string; source?: unknown; proof_tex?: string }).status = "cited";
    (core.statements[1] as { status: string; source?: unknown; proof_tex?: string }).proof_tex = undefined;
    (core.statements[1] as { status: string; source?: unknown }).source = { locator: "Theorem 1" };
    const after = saturationWorking();
    expect(codes(checkRoundInvariants({ proto: core, core, after }))).not.toContain("proved-not-partial");
  });

  it("stays silent when the cursor agrees the node is finished", () => {
    const core = saturationCore();
    const after = saturationWorking();
    const rec = after.solved["oeq:full-branch-optimizer-map"];
    delete (rec as { partial?: boolean }).partial;
    rec.proof_tex = SATURATION_NODE.proof_tex;
    expect(codes(checkRoundInvariants({ proto: core, core, after }))).not.toContain("proved-not-partial");
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

/** The healthy shape, as on disk in the live run: the answered source is absent from
 *  BOTH core.statements and solved; the answer theorem lives in both. */
function frontierStores(): { core: Core; after: WorkingState } {
  const core = {
    qid: "stat_reversekl_two_coverage",
    specialization: "linear_exact_shell",
    cluster: "stat",
    symbols: [], assumptions: [], definitions: [],
    statements: [ANSWER],
    bibliography: [],
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
          depends_on: ["def:exact-shell", "thm:feasible-index-region"],
        }),
      },
    },
  } as unknown as WorkingState;
  return { core, after };
}

describe("resolved-OEQ retirement", () => {
  it("stays silent on the healthy on-disk shape (source retired from both stores)", () => {
    const { core, after } = frontierStores();
    const got = codes(checkRoundInvariants({ proto: core, core, after }));
    expect(got).not.toContain("oeq-source-retired");
    expect(got).not.toContain("oeq-source-record-retired");
  });

  it("flags an answered question still published as a live core node — regardless of its `kind`", () => {
    const { core, after } = frontierStores();
    // Minimal mutation: the source survives in the assembled core (a mis-kinded node on
    // the source id would slip a kind-keyed repair; the check keys on the id).
    core.statements.push({
      id: SOURCE_ID,
      kind: "theorem",
      status: "to-prove",
      statement: "For the fixed public experiment, characterize the attainable pairs ...",
      depends_on: [],
    } as unknown as Core["statements"][number]);
    const hit = checkRoundInvariants({ proto: core, core, after }).find((v) => v.code === "oeq-source-retired");
    expect(hit).toBeDefined();
    expect(hit!.ids).toEqual([SOURCE_ID]);
  });

  it("flags an answered question that still has a working record under its source id", () => {
    const { core, after } = frontierStores();
    after.solved[SOURCE_ID] = {
      proof_tex: "stale bytes",
      snapshot: { stmt: "the question text", depends_on: [], defs: {}, assumptions: {} },
    } as unknown as WorkingState["solved"][string];
    const hit = checkRoundInvariants({ proto: core, core, after }).find((v) => v.code === "oeq-source-record-retired");
    expect(hit).toBeDefined();
    expect(hit!.ids).toEqual([SOURCE_ID]);
  });
});
