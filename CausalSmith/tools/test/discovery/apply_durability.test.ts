// Durability of the apply commit, from the D-stage static audit 2026-07-20.
//
// Both defects here corrupt PERSISTED state silently -- the class you cannot detect
// afterwards -- which is why they were worth fixing despite low per-apply probability.
// Crashes are not hypothetical in this system: a D0 round exited 1 on 2026-07-19, and
// codex workers are killed at exit 137 under contention.

import { describe, it, expect } from "vitest";
import { readFile, writeFile } from "node:fs/promises";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { saveWorkingState, loadWorkingState } from "../../src/discovery/stages/d0_working.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { createDStageHarness } from "./d_stage_harness.js";

const PROTO = {
  qid: "stat_dur", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [{
    id: "thm:main", kind: "theorem", statement: "LIVE CLAIM",
    depends_on: ["ass:overlap"], status: "to-prove",
    justification: "j", gap: "g", consumer: "c",
  }],
  target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

const change = { id: "thm:main", current: "LIVE CLAIM", proposed: "NEW CLAIM", reason: "r", direction: "narrow" };

// NOT COVERED BY AN AUTOMATED TEST: the compare-and-swap itself.
//
// It fires only when the proto changes BETWEEN this apply's initial read and its rename.
// Reproducing that window deterministically needs a hook inside applyProposedChanges, and
// a test-only seam in production code is not worth it. An interleaved attempt was written
// and DELETED: the competing write consistently landed outside the window, so it passed or
// failed for reasons unrelated to the guard -- a test that does not exercise its subject is
// worse than none, because it reads as coverage.
//
// The CAS is therefore verified by inspection only (stage0_apply.ts: single read at the
// top, re-read and compare immediately before the rename, throw without mutating). Treat
// it as unproven. The ordering guarantee below IS covered.

describe("the adjudicated bundle is consumed only after the proto lands", () => {
  it("a successful apply still consumes the proposals", async () => {
    // The fix must not leave a consumed bundle behind for the next round to re-read.
    const h = await createDStageHarness({ qid: "stat_dur", specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), {
        round: 1, solved: {}, resolved_oeqs: {},
        proposals: { statements: [change], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
      } as never);
      await applyProposedChanges({ ctx: h.ctx() });

      const proto = JSON.parse(await readFile(protoCoreJsonPath(h.ctx()), "utf8"));
      expect(proto.statements[0].statement, "the change must land in the proto").toBe("NEW CLAIM");
      // CONSUMED = present but EMPTY, not absent. An absent `proposals` means "legacy run"
      // to readRoundProposals and re-enables the per-kind mirror fallback, so deleting the
      // field would let an already-applied bundle resurrect from the mirrors if the run
      // stopped before they were cleared.
      const w = await loadWorkingState(h.ctx());
      const p = (w as { proposals?: Record<string, unknown[]> }).proposals;
      expect(p, "the marker must remain PRESENT so the legacy fallback stays suppressed").toBeDefined();
      expect(Object.values(p!).every((v) => Array.isArray(v) && v.length === 0),
        "every channel must be empty — the bundle is consumed").toBe(true);

      // and the authoritative reader must now report nothing, not fall back to mirrors
      const { readRoundProposals } = await import("../../src/discovery/solve/proposals.js");
      const round = await readRoundProposals(h.ctx(), w);
      expect(round.statements).toEqual([]);
      expect(round.coreEdits).toEqual([]);
    } finally { await h.dispose(); }
  }, 30000);
});
