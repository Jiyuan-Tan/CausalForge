// Proposal-store contracts.
//
// The round's proposals used to be five sibling `proposed_*.json` files with nothing
// tying them together, so each consumer read its own subset: `d0_apply_change` read
// four of five and never the proofs, the D0.5 reviewers read none, and the closure
// gate had to reconstruct the union (and got it wrong). They now live in
// `d0_working.json` and are reached ONLY through `solve/proposals.ts`; the legacy
// files are fully retired (2026-07-20) — a leftover one fails LOUD with a
// migration pointer instead of being read.

import { mkdtemp, rm, mkdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import {
  readRoundProposals,
  emptyProposals,
  hasProposals,
  proposalIds,
} from "../../src/discovery/solve/proposals.js";
import { artifactPath } from "../../src/paths.js";

// Local mirror of the RETIRED per-kind filenames (production no longer exports
// them; these tests exercise the leftover-file detection).
const LEGACY_NAME = {
  statements: "proposed_statement_changes.json",
  proofs: "proposed_proofs.json",
  coreEdits: "proposed_core_edits.json",
} as const;
function legacyProposalPath(ctx: PipelineContext, kind: keyof typeof LEGACY_NAME): string {
  const name = LEGACY_NAME[kind];
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", name, [`${ctx.qid}_${name}`]);
}
import { coreEditTarget } from "../../src/discovery/stages/d0_apply.js";
import type { PipelineContext } from "../../src/types.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

const dirs: string[] = [];
async function ctxIn(): Promise<PipelineContext> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "proposals-"));
  dirs.push(repoRoot);
  const ctx: PipelineContext = { repoRoot, qid: "q", specialization: "v1", dryRun: false, resume: true };
  await mkdir(path.dirname(legacyProposalPath(ctx, "statements")), { recursive: true });
  return ctx;
}
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((d) => rm(d, { recursive: true, force: true })));
});

const working = (proposals?: WorkingState["proposals"]): WorkingState =>
  ({ round: 1, solved: {}, ...(proposals ? { proposals } : {}) }) as WorkingState;

describe("readRoundProposals", () => {
  it("takes the working state as authoritative, ignoring stale files", async () => {
    const ctx = await ctxIn();
    // A stale mirror from an earlier round must never win over the live payload.
    await writeFile(
      legacyProposalPath(ctx, "statements"),
      JSON.stringify([{ id: "thm:stale", proposed: "old" }]),
      "utf8",
    );
    const p = await readRoundProposals(ctx, working({
      statements: [{ id: "thm:live", proposed: "new" }],
      definitions: [], assumptions: [], coreEdits: [], proofs: [],
    }));
    expect(p.statements).toEqual([{ id: "thm:live", proposed: "new" }]);
  });

  it("fails LOUD with a migration pointer for a run that predates the fold", async () => {
    const ctx = await ctxIn();
    await writeFile(legacyProposalPath(ctx, "statements"), JSON.stringify([{ id: "thm:a", proposed: "x" }]), "utf8");
    await writeFile(legacyProposalPath(ctx, "proofs"), JSON.stringify([{ id: "thm:a", proof_tex: "QED." }]), "utf8");
    await expect(readRoundProposals(ctx, working())).rejects.toThrow(/migrate_dstage_stores/);
  });

  it("carries the PROOFS alongside the changes — the subset apply used to drop", async () => {
    const ctx = await ctxIn();
    const p = await readRoundProposals(ctx, working({
      statements: [{ id: "thm:a", proposed: "narrowed" }],
      definitions: [], assumptions: [], coreEdits: [],
      proofs: [{ id: "thm:a", proof_tex: "proof of the NARROWED claim" }],
    }));
    // The proof written FOR the proposed change travels with it.
    expect(p.statements[0]).toMatchObject({ id: "thm:a" });
    expect(p.proofs[0].proof_tex).toContain("NARROWED");
  });

  it("returns an empty payload when there is neither store nor file", async () => {
    const p = await readRoundProposals(await ctxIn(), null);
    expect(hasProposals(p)).toBe(false);
    expect(p).toEqual(emptyProposals());
  });

  it("refuses even a corrupt legacy leftover rather than reading it as 'no proposals'", async () => {
    // Silently reading {} as empty would adjudicate an empty bundle and clear the round.
    const ctx = await ctxIn();
    await writeFile(legacyProposalPath(ctx, "coreEdits"), "{ not json", "utf8");
    await expect(readRoundProposals(ctx, working())).rejects.toThrow(/migrate_dstage_stores/);
  });
});

describe("proposalIds", () => {
  it("covers every kind, so the closure gate cannot omit one", async () => {
    const p = await readRoundProposals(await ctxIn(), working({
      statements: [{ id: "thm:a", proposed: "x" }],
      definitions: [{ id: "def:d", proposed: "y" }],
      assumptions: [{ id: "ass:a", condition: "c" }],
      coreEdits: [{ kind: "symbol-add", name: "S", proposed: { name: "S" }, direction: "correct" }],
      proofs: [{ id: "lem:p", proof_tex: "QED." }],
    }));
    expect(proposalIds(p, coreEditTarget)).toEqual(
      new Set(["thm:a", "def:d", "ass:a", "sym:S", "lem:p"]),
    );
  });
});
