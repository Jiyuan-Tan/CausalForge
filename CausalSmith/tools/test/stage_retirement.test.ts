import { describe, expect, it } from "vitest";

import { STAGE_HALT_IDS, STAGE_ORDER, resolveStageHaltId } from "../src/constants.js";
import { nextStage } from "../src/pipeline.js";
import { stateSchema } from "../src/state.js";

describe("retired F3.7 stage", () => {
  it("is absent from the execution sequence and halt surface", () => {
    expect(STAGE_ORDER).not.toContain("3.7");
    expect(STAGE_HALT_IDS).not.toContain("F3.7");
    expect(resolveStageHaltId("F3.7")).toBeNull();
    expect(resolveStageHaltId("3.7")).toBeNull();
    expect(nextStage("3.5")).toBe("4");
  });

  it("migrates an in-flight old F3.7 state to resume at F4", () => {
    const parsed = stateSchema.parse({
      stage_completed: "3.7",
      lean_subdir: "CausalSmith/Stat",
      pending_sorries: [],
      design_decisions: {},
      flags: { local_fix_from_4d: false, missing_architecture: false },
    });

    expect(parsed.stage_completed).toBe("3.5");
  });
});
