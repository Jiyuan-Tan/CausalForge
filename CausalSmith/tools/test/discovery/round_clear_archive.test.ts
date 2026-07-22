// `clearRoundOutputs` deletes the round's raw solve payloads — which are the ONLY home
// of collision-withheld, unmatched-id, and duplicate-reproof proof bytes (they never
// reach the working cursor). The sweep must copy those bytes to the cold archive before
// the files go.

import { describe, it, expect } from "vitest";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { clearRoundOutputs } from "../../src/discovery/stages/d0_apply.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { readProofArchiveIndex } from "../../src/discovery/proof_archive.js";
import type { PipelineContext } from "../../src/types.js";

describe("clearRoundOutputs archives solve payload proof bytes before deletion", () => {
  it("sweeps proofs, added lemmas, OEQ answers, and obligation partials from solve_*.json", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "roundclear-"));
    const ctx: PipelineContext = { repoRoot, qid: "stat_rc", specialization: "v1", dryRun: false, resume: false };
    const dir = path.dirname(coreJsonPath(ctx));
    await mkdir(dir, { recursive: true });
    try {
      await writeFile(path.join(dir, "solve_thm_main.json"), JSON.stringify({
        proofs: [{ id: "thm:main", proof_tex: "direct proof bytes" }],
        added_lemmas: [{ id: "lem:h", kind: "lemma", statement: "s", depends_on: [], status: "proved", proof_tex: "withheld duplicate bytes" }],
        resolved_oeqs: [{ source_id: "oeq:q", theorem: { id: "thm:ans", kind: "theorem", statement: "a", depends_on: [], status: "proved", proof_tex: "answer bytes" } }],
        open_obligations: [{ node_id: "thm:hard", why: "w", partial_result: "partial bytes" }],
      }), "utf8");
      await writeFile(path.join(dir, "proposed_proofs.json"), JSON.stringify(
        [{ id: "thm:prov", proof_tex: "legacy provisional bytes" }],
      ), "utf8");

      await clearRoundOutputs(ctx);

      expect(existsSync(path.join(dir, "solve_thm_main.json"))).toBe(false);
      expect(existsSync(path.join(dir, "proposed_proofs.json"))).toBe(false);
      const index = await readProofArchiveIndex(dir);
      const byNode = new Map(index.map((e) => [e.node_id, e.reason]));
      expect([...byNode.keys()].sort()).toEqual(["lem:h", "thm:ans", "thm:hard", "thm:main", "thm:prov"]);
      expect(new Set(byNode.values())).toEqual(new Set(["round-cleared"]));
    } finally { await rm(repoRoot, { recursive: true, force: true }); }
  });

  it("sweeps withheld_content.json so a stale pre-apply diagnostic cannot present as current", async () => {
    // The withheld-content marker is a per-round diagnostic (commit.ts writes it when a
    // round withholds colliding payloads). Leaving it behind after the orchestrator's
    // apply made the PREVIOUS round's conflicts look like a live defect to whoever (agent
    // or operator) inspects the run directory next.
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "roundclear-"));
    const ctx: PipelineContext = { repoRoot, qid: "stat_rc", specialization: "v1", dryRun: false, resume: false };
    const dir = path.dirname(coreJsonPath(ctx));
    await mkdir(dir, { recursive: true });
    try {
      await writeFile(path.join(dir, "withheld_content.json"), JSON.stringify({
        emission_conflicts: [{ category: "statement", id: "lem:x" }],
        added_lemma_collisions: [], oeq_answer_collisions: [], unmatched_proof_ids: [],
      }), "utf8");

      await clearRoundOutputs(ctx);

      expect(existsSync(path.join(dir, "withheld_content.json"))).toBe(false);
    } finally { await rm(repoRoot, { recursive: true, force: true }); }
  });

  it("does NOT archive bytes that still live in the working cursor", async () => {
    // "Archived" must mean "left hot state". A committed proof mirrored in solve_*.json
    // is hot, and a false archive row would later suppress (via (bytes, node) dedup)
    // the record of a REAL displacement of the same bytes.
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "roundclear-"));
    const ctx: PipelineContext = { repoRoot, qid: "stat_rc", specialization: "v1", dryRun: false, resume: false };
    const dir = path.dirname(coreJsonPath(ctx));
    await mkdir(dir, { recursive: true });
    try {
      await writeFile(path.join(dir, "d0_working.json"), JSON.stringify({
        round: 1,
        solved: { "thm:main": { proof_tex: "committed proof bytes", snapshot: { stmt: "s", defs: {}, assumptions: {} } } },
      }), "utf8");
      await writeFile(path.join(dir, "solve_thm_main.json"), JSON.stringify({
        proofs: [{ id: "thm:main", proof_tex: "committed proof bytes" }],
        added_lemmas: [{ id: "lem:h", kind: "lemma", statement: "s", depends_on: [], status: "proved", proof_tex: "withheld bytes" }],
      }), "utf8");

      await clearRoundOutputs(ctx);

      const index = await readProofArchiveIndex(dir);
      expect(index.map((e) => e.node_id), "only the bytes leaving hot state are archived").toEqual(["lem:h"]);
    } finally { await rm(repoRoot, { recursive: true, force: true }); }
  });

  it("archives an unparseable solve file wholesale instead of dropping it", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "roundclear-"));
    const ctx: PipelineContext = { repoRoot, qid: "stat_rc", specialization: "v1", dryRun: false, resume: false };
    const dir = path.dirname(coreJsonPath(ctx));
    await mkdir(dir, { recursive: true });
    try {
      await writeFile(path.join(dir, "solve_torn.json"), '{"proofs": [{"id": "thm:x", "proof_tex": "torn', "utf8");
      await clearRoundOutputs(ctx);
      const index = await readProofArchiveIndex(dir);
      expect(index).toHaveLength(1);
      expect(index[0].node_id).toBe("file:solve_torn.json");
      expect(index[0].reason).toBe("round-cleared-unparsed");
    } finally { await rm(repoRoot, { recursive: true, force: true }); }
  });
});
