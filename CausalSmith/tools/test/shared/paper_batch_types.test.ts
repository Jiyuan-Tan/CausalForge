import { describe, it, expect } from "vitest";
import type { PaperBatch, TheoremEntry } from "../../src/shared/paper_batch_types.js";

describe("paper_batch_types", () => {
  it("PaperBatch carries insight_id + ordered theorems", () => {
    const batch: PaperBatch = {
      insight_id: "ins1",
      shared_setup: "Let X be ...",
      theorems: [
        {
          theorem_local_id: "t1",
          statement: "If A then B.",
          proof_sketch: "Apply L.",
        },
      ],
    };
    expect(batch.insight_id).toBe("ins1");
    expect(batch.theorems[0].theorem_local_id).toBe("t1");
  });

  it("TheoremEntry tracks per-theorem stage progress and status", () => {
    const e: TheoremEntry = {
      theorem_local_id: "t1",
      origin_theorem_id: "ins1_t1",
      statement: "If A then B.",
      proof_sketch: "Apply L.",
      status: "pending",
      stage_completed: null,
      lean_file_relpath: null,
    };
    expect(e.status).toBe("pending");
    expect(e.stage_completed).toBeNull();
  });

  it("TheoremEntry accepts optional bt_id after Stage 5 close", () => {
    const e: TheoremEntry = {
      theorem_local_id: "t1",
      origin_theorem_id: "ins1_t1",
      statement: "If A then B.",
      proof_sketch: null,
      status: "completed",
      stage_completed: "5",
      lean_file_relpath: "Theorem_t1.lean",
      bt_id: "ins1_t1_v1",
    };
    expect(e.bt_id).toBe("ins1_t1_v1");
  });
});
