// Persist-time proof archiving: the ONE choke point where displaced proof bytes are
// preserved. `saveWorkingState` diffs the new cursor against the on-disk previous one;
// any (id, proof_tex) that existed before and is gone or byte-changed after is copied
// to the cold archive before the write. Call-site discipline is exactly what leaked
// bytes before (statement changes, OEQ drops, auto-heals each had their own delete);
// a store-boundary diff catches every current path and every future one.

import { describe, it, expect } from "vitest";
import { mkdtemp, mkdir, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  saveWorkingState,
  workingPath,
  type WorkingState,
} from "../../src/discovery/stages/d0_working.js";
import { readProofArchiveIndex } from "../../src/discovery/proof_archive.js";
import type { PipelineContext } from "../../src/types.js";

async function makeCtx(): Promise<{ ctx: PipelineContext; dispose: () => Promise<void> }> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "wsarchive-"));
  const ctx: PipelineContext = { repoRoot, qid: "stat_ws", specialization: "v1", dryRun: false, resume: false };
  await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
  return { ctx, dispose: async () => { await rm(repoRoot, { recursive: true, force: true }); } };
}

const SNAP = { stmt: "s", defs: {}, assumptions: {} };
const state = (round: number, solved: WorkingState["solved"], proposals?: WorkingState["proposals"]): WorkingState =>
  ({ round, solved, ...(proposals ? { proposals } : {}) }) as WorkingState;

describe("saveWorkingState archives displaced proof bytes", () => {
  it("archives an overwritten proof and a deleted record; identical bytes archive nothing", async () => {
    const { ctx, dispose } = await makeCtx();
    try {
      await saveWorkingState(ctx, state(1, {
        "thm:a": { proof_tex: "proof A v1", snapshot: SNAP },
        "oeq:q": { proof_tex: "answer draft", snapshot: SNAP },
      }));
      expect(await readProofArchiveIndex(path.dirname(workingPath(ctx))), "first write displaces nothing").toEqual([]);

      // Round 2: thm:a overwritten, oeq:q deleted (the OEQ-resolution shape).
      await saveWorkingState(ctx, state(2, {
        "thm:a": { proof_tex: "proof A v2", snapshot: SNAP },
      }));
      let index = await readProofArchiveIndex(path.dirname(workingPath(ctx)));
      expect(index.map((e) => [e.node_id, e.reason]).sort()).toEqual([
        ["oeq:q", "dropped/round-2"],
        ["thm:a", "displaced/round-2"],
      ]);

      // Re-saving the same content archives nothing new.
      await saveWorkingState(ctx, state(2, {
        "thm:a": { proof_tex: "proof A v2", snapshot: SNAP },
      }));
      index = await readProofArchiveIndex(path.dirname(workingPath(ctx)));
      expect(index).toHaveLength(2);
    } finally { await dispose(); }
  });

  it("archives a cleared provisional proposal payload, but not one promoted into solved", async () => {
    const { ctx, dispose } = await makeCtx();
    try {
      await saveWorkingState(ctx, state(1, {}, {
        statements: [], definitions: [], assumptions: [], coreEdits: [],
        proofs: [
          { id: "thm:kept", proof_tex: "will be promoted" },
          { id: "thm:lost", proof_tex: "will be cleared" },
        ],
      }));
      // Apply promotes thm:kept into solved and clears the round's proposals.
      await saveWorkingState(ctx, state(1, {
        "thm:kept": { proof_tex: "will be promoted", snapshot: SNAP },
      }));
      const index = await readProofArchiveIndex(path.dirname(workingPath(ctx)));
      expect(index.map((e) => e.node_id), "promoted bytes still live in hot state — not displaced").toEqual(["thm:lost"]);
      expect(index[0].reason).toBe("proposal-cleared/round-1");
    } finally { await dispose(); }
  });
});
