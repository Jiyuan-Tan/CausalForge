import { describe, it, expect } from "vitest";
import {
  gradeReviewerOutput,
  mergeOutputs,
  normalizeReviewerObjId,
  resolveVerdictIds,
} from "../../src/formalization/proof_reviewer.js";

// A node legitimately has TWO names: its graph `id` (`lem:admissible-swaps-preserve-direction`)
// and its `obj_id` (`L-1`). `nodeIdToObjId` only rewrites short ids like `l1`→`L-1`, so a
// descriptive id passes through unchanged into `expectedObjIds` — while the reviewer may answer
// under EITHER name. Keying `seen` on the returned name and checking it against the expected name
// therefore DROPS a real `matched` and synthesizes `drift / "missing reviewer verdict"` over it.
// That is a coin-flip blocker: the same review passes or fails on which alias the model happened
// to use.
const CANON = "lem:admissible-swaps-preserve-direction";
const ALIASES = new Map<string, string>([
  [CANON, CANON],
  ["L-1", CANON],
]);

describe("reviewer verdict grading resolves node id ↔ obj_id aliases", () => {
  it("a `matched` answered under the obj_id alias is NOT dropped and NOT overwritten by a synthetic drift", () => {
    const out = {
      status: "ok",
      statement_verdicts: [{ obj_id: "L-1", verdict: "matched", note: "faithful" }],
      assumption_verdicts: [],
      substrate_gates: [],
      escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.blocking).toEqual([]);                                  // no invented drift
    expect(graded.rows).toHaveLength(1);                                  // not both a pass AND a drift
    expect(graded.rows[0]).toMatchObject({ obj_id: CANON, verdict: "equivalent" });
  });

  it("a `matched` answered under the canonical id still works (no regression)", () => {
    const out = {
      status: "ok",
      statement_verdicts: [{ obj_id: CANON, verdict: "matched" }],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows[0]).toMatchObject({ obj_id: CANON, verdict: "equivalent" });
  });

  it("a genuine reviewer DROPOUT is still caught — silence must never read as a pass", () => {
    const out = {
      status: "ok",
      statement_verdicts: [], assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.blocking).toEqual([CANON]);
    expect(graded.rows[0]).toMatchObject({ obj_id: CANON, verdict: "drift", note: "missing reviewer verdict" });
  });

  it("a real `drift` answered under the alias still blocks (the fix must not launder a failure)", () => {
    const out = {
      status: "ok",
      statement_verdicts: [{ obj_id: "L-1", verdict: "drift", note: "statement weakened" }],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.blocking).toEqual([CANON]);
  });

  it("normalizes an alias followed by a Lean declaration name before canonicalizing", () => {
    const out = {
      status: "ok",
      statement_verdicts: [{ obj_id: "L-1 SomeLeanDecl", verdict: "matched" }],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows[0].obj_id).toBe(CANON);
  });
});

describe("reviewer object-id normalization preserves TeX symbol ids", () => {
  const HEAVY_LIGHT = "sym:\\(\\widehat{\\mathcal H}_n,\\widehat{\\mathcal L}_n\\)";
  const RISK = "sym:\\(\\mathsf R_{n,d,\\epsilon}\\)";

  it("preserves internal TeX whitespace and commas", () => {
    expect(normalizeReviewerObjId(HEAVY_LIGHT)).toBe(HEAVY_LIGHT);
    expect(normalizeReviewerObjId(RISK)).toBe(RISK);
  });

  it("uses the longest expected id when a reviewer appends prose", () => {
    expect(normalizeReviewerObjId(`${HEAVY_LIGHT} realized by heavyCells`, [HEAVY_LIGHT])).toBe(HEAVY_LIGHT);
  });

  it("does not synthesize a missing verdict for a matched symbol with TeX spaces", () => {
    const out = {
      status: "ok",
      statement_verdicts: [{ obj_id: RISK, verdict: "matched", note: "faithful" }],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [RISK]);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows).toHaveLength(1);
    expect(graded.rows[0].obj_id).toBe(RISK);
  });

  it("preserves a keyed-object symbol id with spaces and commas", () => {
    const out = {
      status: "ok",
      statement_verdicts: { [HEAVY_LIGHT]: { verdict: "untagged", note: "tag heavyCells" } },
      assumption_verdicts: {}, substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [HEAVY_LIGHT]);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows.map((row) => row.obj_id)).toEqual([HEAVY_LIGHT]);
  });

  it("parses a bare-string symbol verdict without truncating the TeX id", () => {
    const out = {
      status: "ok",
      statement_verdicts: [`${RISK}: matched — exact risk definition`],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    expect(gradeReviewerOutput(out as never, [RISK]).blocking).toEqual([]);
  });

  it("never forwards an unexpected truncated pseudo-id to F2", () => {
    const truncated = "sym:\\(\\widehat{\\mathcal";
    const out = {
      status: "flagged",
      statement_verdicts: [{ obj_id: truncated, verdict: "drift", note: "missing" }],
      assumption_verdicts: [], substrate_gates: [],
      escalate: { kind: "scaffold-mismatch", obj_id: truncated, reason: "missing" },
    };
    const graded = gradeReviewerOutput(out as never, [HEAVY_LIGHT]);
    expect(graded.blocking).toEqual([HEAVY_LIGHT]);
    expect(graded.rows.map((row) => row.obj_id)).toEqual([HEAVY_LIGHT]);
    expect(graded.escalate?.obj_id).toBeUndefined();
  });

  it.each(["incorrect", "invalid", "unsound", "inconsistent", "not ok"])(
    "treats the negative token '%s' as blocking",
    (verdict) => {
      const out = {
        status: "flagged",
        statement_verdicts: [{ obj_id: RISK, verdict }],
        assumption_verdicts: [], substrate_gates: [], escalate: null,
      };
      expect(gradeReviewerOutput(out as never, [RISK]).blocking).toEqual([RISK]);
    },
  );

  it.each(["misaligned", "inaccurate", "not exact", "not preserved", "does not match"])(
    "fails closed on negated or negative-prefixed positive vocabulary: '%s'",
    (verdict) => {
      const out = {
        status: "flagged",
        statement_verdicts: [{ obj_id: RISK, verdict }],
        assumption_verdicts: [], substrate_gates: [], escalate: null,
      };
      expect(gradeReviewerOutput(out as never, [RISK]).blocking).toEqual([RISK]);
    },
  );

  it.each([
    "faithful but drifted",
    "faithful but drifting",
    "faithful but overclaims",
    "faithful but mismatches",
    "faithful but weakens the theorem",
    "faithful but conditionalized",
    "aligned however incorrect",
    "matched yet partial",
  ])(
    "fails closed when a contrastive clause retracts a leading pass: '%s'",
    (verdict) => {
      const out = {
        status: "flagged",
        statement_verdicts: [{ obj_id: RISK, verdict }],
        assumption_verdicts: [], substrate_gates: [], escalate: null,
      };
      expect(gradeReviewerOutput(out as never, [RISK]).blocking).toEqual([RISK]);
    },
  );

  it("deduplicates conflicting aliases negative-first", () => {
    const out = {
      status: "flagged",
      statement_verdicts: [
        { obj_id: CANON, verdict: "matched", note: "peer A" },
        { obj_id: "L-1", verdict: "drift", note: "peer B" },
      ],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.rows).toHaveLength(1);
    expect(graded.blocking).toEqual([CANON]);
    expect(graded.rows[0].verdict).toBe("drift");
  });
});

// REGRESSION (2026-07-21 audit): `mergeOutputs` is a plain reducer with NO expected-id list, so a
// prose-STRING verdict ("def:rate-bound: matched — …" — a documented live model-output shape) that
// reaches it unresolved is shredded to `{verdict: <whole string>}` with no obj_id, irreversibly.
// The merged row then grades as a synthetic "missing reviewer verdict" drift over a real matched —
// a spurious blocker on a healthy run. `resolveVerdictIds` must run at the PARSE boundary, before
// any merge. Typed-core ids (`def:`/`thm:`) and `sym:` ids are the affected classes (the legacy
// OBJ_ID_RE only rescues `L-1`/`P-9`-style short ids).
describe("prose-string verdicts survive the merge boundary (resolveVerdictIds)", () => {
  it("a typed-core id prose verdict keeps its obj_id through mergeOutputs + grading", () => {
    const raw = {
      status: "ok",
      statement_verdicts: ["def:rate-bound: matched — the Lean def is faithful"],
    };
    const resolved = resolveVerdictIds(raw as never, ["def:rate-bound"]);
    const merged = mergeOutputs(resolved, { status: "ok" } as never);
    const graded = gradeReviewerOutput(merged, ["def:rate-bound"]);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows[0]).toMatchObject({ obj_id: "def:rate-bound", verdict: "equivalent" });
  });

  it("a sym: id prose verdict likewise survives the merge", () => {
    const raw = { status: "ok", statement_verdicts: ["sym:e_P: matched — cluster pins (0,1)"] };
    const resolved = resolveVerdictIds(raw as never, ["sym:e_P"]);
    const merged = mergeOutputs(resolved, { status: "ok" } as never);
    const graded = gradeReviewerOutput(merged, ["sym:e_P"]);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows[0]).toMatchObject({ obj_id: "sym:e_P", verdict: "equivalent" });
  });
});
