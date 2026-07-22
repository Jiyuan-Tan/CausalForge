// A cross-unit id collision must COST THE COLLIDING IDS, not the whole round.
//
// Two independent solve units can mint the SAME NEW helper id with different content.
// Ownership tables cannot prevent this class: they assign owners for ids that ALREADY
// EXIST, and a lemma invented mid-round by two units at once has no owner to assign.
//
// The guard used to throw, aborting the round and discarding every unit's work.
// stat_cot_observational_efficiency 2026-07-19 lost a round that way when
// `oeq:degeneracy-adaptive-inference` and `thm:degeneracy-frontier-and-spectral-obstruction`
// both minted `lem:isonormal-hilbert-schmidt-calibration` — taking three unrelated repairs
// down with it. The same guard had already cost ~1.4h on a prose mismatch in an earlier run.
//
// The original concern behind the throw is still correct and still enforced: taking EITHER
// payload would make the assembled core depend on dispatch order. So all variants are
// dropped — never one picked — and the rest of the round survives.

import { describe, it, expect } from "vitest";
import {
  collectConflictingSolveEmissions,
  dropConflictingSolveEmissions,
  formatSolveEmissionConflicts,
} from "../../src/discovery/solve/ownership.js";
import type { SolveUnitOutput } from "../../src/discovery/solve/schemas.js";

const lemma = (id: string, statement: string): never =>
  ({ id, kind: "lemma", status: "proved", statement, depends_on: [], proof_tex: `proof of ${statement}` }) as never;

const unit = (over: Partial<SolveUnitOutput> = {}): SolveUnitOutput => ({
  proofs: [], resolved_oeqs: [], added_lemmas: [], proposed_statement_changes: [],
  proposed_definition_changes: [], proposed_assumptions: [], proposed_core_edits: [],
  open_obligations: [], ...over,
});

const COLLIDING = "lem:isonormal-hilbert-schmidt-calibration";

describe("cross-unit id collision degrades the round instead of destroying it", () => {
  const outputs = [
    unit({ added_lemmas: [lemma(COLLIDING, "compression version"), lemma("lem:kept-a", "unrelated A")] }),
    unit({ added_lemmas: [lemma(COLLIDING, "eigenvalue version"), lemma("lem:kept-b", "unrelated B")] }),
  ];
  const labels = ["thm:degeneracy-frontier-and-spectral-obstruction", "oeq:degeneracy-adaptive-inference"];

  it("reports the collision instead of throwing", () => {
    const conflicts = collectConflictingSolveEmissions(outputs, labels);
    expect(conflicts).toHaveLength(1);
    expect(conflicts[0].id).toBe(COLLIDING);
    expect(conflicts[0].units, "must name BOTH emitting units for the directive").toEqual(labels);
  });

  it("withholds EVERY variant — picking one would make the core dispatch-order dependent", () => {
    const conflicts = collectConflictingSolveEmissions(outputs, labels);
    const kept = dropConflictingSolveEmissions(outputs, conflicts);
    expect(kept.flatMap((o) => o.added_lemmas.map((l) => l.id))).not.toContain(COLLIDING);
  });

  it("KEEPS the unrelated work — this is the whole point", () => {
    const conflicts = collectConflictingSolveEmissions(outputs, labels);
    const kept = dropConflictingSolveEmissions(outputs, conflicts);
    // Previously these were discarded along with the collision.
    expect(kept.flatMap((o) => o.added_lemmas.map((l) => l.id))).toEqual(["lem:kept-a", "lem:kept-b"]);
  });

  it("does not fire when both units emit IDENTICAL content", () => {
    const same = [
      unit({ added_lemmas: [lemma(COLLIDING, "same")] }),
      unit({ added_lemmas: [lemma(COLLIDING, "same")] }),
    ];
    expect(collectConflictingSolveEmissions(same, labels)).toEqual([]);
    // and nothing is dropped
    expect(dropConflictingSolveEmissions(same, []).flatMap((o) => o.added_lemmas.map((l) => l.id)))
      .toEqual([COLLIDING, COLLIDING]);
  });

  it("the diagnostic tells the orchestrator what to actually do", () => {
    const msg = formatSolveEmissionConflicts(collectConflictingSolveEmissions(outputs, labels));
    expect(msg).toMatch(/withheld/);
    expect(msg, "must name a canonical owner as the repair").toMatch(/canonical owner/);
    expect(msg).toContain(COLLIDING);
    expect(msg, "must name both units").toContain("oeq:degeneracy-adaptive-inference");
  });
});

describe("unit attribution is order-robust", () => {
  // `wasSameUnit` inspects only the LAST recorded emitter, so interleavings decide
  // whether a duplicate is classified intra-unit (fatal) or cross-unit (withheld).
  it("A then B different => cross-unit, reported not thrown", () => {
    const outs = [unit({ added_lemmas: [lemma("lem:x", "v1")] }), unit({ added_lemmas: [lemma("lem:x", "v2")] })];
    expect(collectConflictingSolveEmissions(outs, ["A", "B"])[0].units).toEqual(["A", "B"]);
  });

  it("A emits two DIFFERENT payloads in its own output => throws (intra-unit)", () => {
    const outs = [unit({ added_lemmas: [lemma("lem:x", "v1"), lemma("lem:x", "v2")] })];
    expect(() => collectConflictingSolveEmissions(outs, ["A"])).toThrow(/conflicting duplicate statement/i);
  });

  it("A twice IDENTICAL then B different => cross-unit, still not thrown", () => {
    // The identical intra-unit repeat must not be mistaken for self-contradiction, and
    // must not mask the genuine A-vs-B collision that follows it.
    const outs = [
      unit({ added_lemmas: [lemma("lem:x", "same"), lemma("lem:x", "same")] }),
      unit({ added_lemmas: [lemma("lem:x", "different")] }),
    ];
    const conflicts = collectConflictingSolveEmissions(outs, ["A", "B"]);
    expect(conflicts).toHaveLength(1);
    expect(conflicts[0].units).toEqual(["A", "A", "B"]);
    expect(dropConflictingSolveEmissions(outs, conflicts).flatMap((o) => o.added_lemmas)).toEqual([]);
  });

  it("three units, only the differing pair collides", () => {
    const outs = [
      unit({ added_lemmas: [lemma("lem:x", "same")] }),
      unit({ added_lemmas: [lemma("lem:x", "same"), lemma("lem:y", "keep")] }),
      unit({ added_lemmas: [lemma("lem:x", "other")] }),
    ];
    const conflicts = collectConflictingSolveEmissions(outs, ["A", "B", "C"]);
    expect(conflicts.map((c) => c.id)).toEqual(["lem:x"]);
    expect(dropConflictingSolveEmissions(outs, conflicts).flatMap((o) => o.added_lemmas.map((l) => l.id)))
      .toEqual(["lem:y"]);
  });
});
