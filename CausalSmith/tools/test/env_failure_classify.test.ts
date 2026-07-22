import { describe, expect, it } from "vitest";
import { handoffSignalsEnvFailure } from "../src/discovery/stages/neg1_2.js";

// A producer that fails to START its local execution (codex write sandbox could
// not spawn) still emits a well-formed handoff with `status: "needs-pivot"`.
// Routing that to a real pivot spuriously burns a HEALTHY angle — observed when
// angle 0 (REVISE@field) was abandoned on a single `spawn setup refresh`. These
// tests pin the classifier that separates an environment failure (retry/abort,
// angle preserved) from a genuine mathematical pivot (angle is dead).

describe("handoffSignalsEnvFailure", () => {
  it("flags the real codex sandbox-startup handoff as an environment failure", () => {
    // Verbatim shape of the v3 handoff that triggered the spurious pivot.
    const handoff = {
      status: "needs-pivot",
      blocking_reason:
        "Could not safely patch the existing proposal in place because all local " +
        "file-access execution backends failed before process start with " +
        "`windows sandbox: spawn setup refresh`, and no MCP file resources were exposed.",
      named_literature_checklist: [],
    };
    expect(handoffSignalsEnvFailure(handoff)).toBe(true);
  });

  it("flags startup failures named only in the SC self-review lines", () => {
    const handoff = {
      status: "needs-pivot",
      soundness_self_review: [
        "SC1: FAIL -- local execution tools failed before process start (windows sandbox: spawn setup refresh)",
        "consistency-pass: FAIL -- unable to inspect the existing TeX",
      ],
    };
    expect(handoffSignalsEnvFailure(handoff)).toBe(true);
  });

  it("does NOT flag a genuine mathematical needs-pivot", () => {
    const handoff = {
      status: "needs-pivot",
      blocking_reason:
        "The kernel reduces to a definitional unfold; no in-place revise can make the " +
        "focal object non-trivial, so the angle should be abandoned and pivoted.",
      soundness_self_review: ["SC11: FAIL -- proof route is a tautological iff"],
    };
    expect(handoffSignalsEnvFailure(handoff)).toBe(false);
  });

  it("does NOT flag a clean completed handoff", () => {
    const handoff = { status: "completed", literature_checklist: [{ author: "X", relevant_to: "Y" }] };
    expect(handoffSignalsEnvFailure(handoff)).toBe(false);
  });

  it("does NOT misfire on prose that merely mentions reading the proposal", () => {
    const handoff = {
      status: "needs-pivot",
      blocking_reason: "After reading §9 I could not find a sound construction for the exhibit.",
    };
    expect(handoffSignalsEnvFailure(handoff)).toBe(false);
  });
});
