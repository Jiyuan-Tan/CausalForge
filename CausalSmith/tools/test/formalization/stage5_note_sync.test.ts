import { describe, it, expect } from "vitest";
import { unsyncedLoadBearingAssumptions } from "../../src/formalization/stage5.js";
import type { AddedAssumption, StateJson } from "../../src/types.js";

const state = (added: AddedAssumption[]): StateJson =>
  ({ added_assumptions: added }) as unknown as StateJson;

const premise = (label: string, classification = "substrate-gate"): AddedAssumption =>
  ({ label, statement: `the ${label} bound holds`, classification }) as AddedAssumption;

describe("unsyncedLoadBearingAssumptions", () => {
  it("flags a load-bearing premise whose label is absent from the note", () => {
    const out = unsyncedLoadBearingAssumptions(state([premise("A1")]), "## Load-bearing hypotheses\n(none)\n");
    expect(out.map((a) => a.label)).toEqual(["A1"]);
  });

  it("accepts a premise whose label appears in the note", () => {
    const out = unsyncedLoadBearingAssumptions(state([premise("A1")]), "- **A1**: the A1 bound holds\n");
    expect(out).toEqual([]);
  });

  // The check exists to catch a premise the note never mentions. A SUBSTRING test makes `A1`
  // satisfied by an unrelated `A10` row, silently suppressing the warning for a genuinely
  // missing premise — the one case it was written to catch.
  it("does not accept a label that only occurs inside a longer label", () => {
    const note = "- **A10**: an unrelated premise\n- **A11**: another\n";
    const out = unsyncedLoadBearingAssumptions(state([premise("A1")]), note);
    expect(out.map((a) => a.label)).toEqual(["A1"]);
  });

  it("still matches a label that is punctuation-delimited rather than space-delimited", () => {
    for (const note of ["(A1)", "**A1**:", "`A1`,", "[A1]", "A1.", "hypothesis A1;"]) {
      expect(unsyncedLoadBearingAssumptions(state([premise("A1")]), note)).toEqual([]);
    }
  });

  it("ignores regularity-bookkeeping premises (not load-bearing)", () => {
    const out = unsyncedLoadBearingAssumptions(
      state([premise("A2", "regularity-bookkeeping")]),
      "no mention here",
    );
    expect(out).toEqual([]);
  });

  it("treats an empty note as syncing nothing", () => {
    const out = unsyncedLoadBearingAssumptions(state([premise("A1"), premise("A2")]), "");
    expect(out.map((a) => a.label)).toEqual(["A1", "A2"]);
  });
});
