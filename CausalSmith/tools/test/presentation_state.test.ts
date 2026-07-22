import { describe, it, expect } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { loadPaperState, savePaperState, freshPaperState } from "../src/presentation/state.js";

describe("paper state", () => {
  it("round-trips and resumes", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-"));
    const s = freshPaperState("stat_ate_overlap_decay", "v1");
    s.stage_completed = "P1";
    s.checkpoint_pending = "outline";
    await savePaperState(dir, s);
    const back = await loadPaperState(dir, "stat_ate_overlap_decay", "v1");
    expect(back).not.toBeNull();
    expect(back!.stage_completed).toBe("P1");
    expect(back!.checkpoint_pending).toBe("outline");
    await rm(dir, { recursive: true, force: true });
  });

  it("returns null when no state exists", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-"));
    expect(await loadPaperState(dir, "x", "v1")).toBeNull();
    await rm(dir, { recursive: true, force: true });
  });

  it("loads legacy three-round rewind state with a fresh two-pass holistic counter", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-legacy-"));
    await writeFile(join(dir, "q_v1_paper_state.json"), JSON.stringify({
      qid: "q",
      spec: "v1",
      stage_completed: "P5",
      checkpoint_pending: null,
      pinned_commit: null,
      revision_round: 3,
      p5_healing_rounds: 3,
      p5_last_fingerprints: ["old"],
      p5_last_score: 6.2,
      hard_gate_failures: [],
      notes: [],
    }));
    const state = await loadPaperState(dir, "q", "v1");
    expect(state!.p5_revision_passes).toBe(0);
    expect(state!.p5_last_fingerprints).toEqual(["old"]);
    await rm(dir, { recursive: true, force: true });
  });
});
