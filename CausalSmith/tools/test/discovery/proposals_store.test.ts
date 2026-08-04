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
  pinWhitespaceEquivalentCurrent,
  proposalIds,
} from "../../src/discovery/solve/proposals.js";
import { artifactPath } from "../../src/paths.js";
import { definitionRevision, statementRevision } from "../../src/discovery/core/revision.js";

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

describe("pinWhitespaceEquivalentCurrent", () => {
  it("repins only whitespace-equivalent guards to authoritative durable bytes", () => {
    const durable = "Claim introduction.\n\\[\n x = 1.\n\\]\nConclusion.";
    const compressed = "Claim introduction. \\[ x = 1. \\] Conclusion.";
    expect(pinWhitespaceEquivalentCurrent({ id: "thm:a", current: compressed }, durable)).toEqual({
      id: "thm:a", current: durable,
    });

    const stale = { id: "thm:a", current: "A substantively older claim." };
    const warnings: string[] = [];
    expect(pinWhitespaceEquivalentCurrent(stale, durable, [], (m) => warnings.push(m))).toBe(stale);
    expect(warnings).toEqual([expect.stringMatching(/left unpinned/)]);
    expect(pinWhitespaceEquivalentCurrent(
      { id: "def:d", current: "U   =\n a", proposed: "U = a + b" },
      "U = a",
    )).toEqual({ id: "def:d", current: "U = a", proposed: "U = a + b" });
  });

  it("repins a non-whitespace serialization mismatch only from a matching revision", () => {
    const durable = 'The H"older condition holds.';
    const revision = statementRevision({
      id: "thm:a", kind: "theorem", statement: durable, status: "to-prove",
    });
    expect(pinWhitespaceEquivalentCurrent(
      { id: "thm:a", current: String.raw`The H\"older condition holds.`, based_on_revision: revision },
      durable,
      [revision],
    )).toEqual({ id: "thm:a", current: durable, based_on_revision: revision });
    // An unknown revision hash is a single-change defect: the guard stays
    // untouched (apply's exact guard skips it) instead of aborting the round.
    const garbled = { id: "thm:a", current: durable, based_on_revision: `rev:${"0".repeat(64)}` };
    const staleRevisionWarnings: string[] = [];
    expect(pinWhitespaceEquivalentCurrent(garbled, durable, [revision], (m) => staleRevisionWarnings.push(m)))
      .toBe(garbled);
    expect(staleRevisionWarnings).toEqual([expect.stringMatching(/matches no current view/)]);
    // A valid revision proves the displayed view, so a substantively drifted
    // echo is repinned — but the tripwire stays visible.
    const echoWarnings: string[] = [];
    expect(pinWhitespaceEquivalentCurrent(
      { id: "thm:a", current: "A completely misread claim.", based_on_revision: revision },
      durable,
      [revision],
      (m) => echoWarnings.push(m),
    )).toEqual({ id: "thm:a", current: durable, based_on_revision: revision });
    expect(echoWarnings).toEqual([expect.stringMatching(/differs beyond whitespace/)]);

    const definition = { id: "def:d", construction: "U = a", name: "D" } as const;
    const defRevision = definitionRevision(definition);
    expect(pinWhitespaceEquivalentCurrent(
      { id: "def:d", current: "U=a", based_on_revision: defRevision },
      definition.construction,
      [defRevision],
    ).current).toBe("U = a");
  });

  it("leaves paragraph-boundary changes unpinned for apply-time refusal", () => {
    const stale = { id: "thm:a", current: "First paragraph. Second paragraph." };
    const warnings: string[] = [];
    expect(pinWhitespaceEquivalentCurrent(stale, "First paragraph.\n\nSecond paragraph.", [], (m) => warnings.push(m)))
      .toBe(stale);
    expect(warnings).toEqual([expect.stringMatching(/left unpinned/)]);
  });

  it("never normalizes when TeX makes whitespace semantic", () => {
    const expectUnpinned = <T extends { current?: string }>(change: T, durable: string): void => {
      const warnings: string[] = [];
      expect(pinWhitespaceEquivalentCurrent(change, durable, [], (m) => warnings.push(m))).toBe(change);
      expect(warnings).toEqual([expect.stringMatching(/left unpinned/)]);
    };
    expectUnpinned({ id: "thm:comment", current: "Claim% old" }, "Claim%\nold");
    expectUnpinned({ id: "thm:verb", current: String.raw`Use \verb|a  b|.` }, String.raw`Use \verb|a b|.`);
    expectUnpinned(
      { id: "thm:env", current: "\\begin{verbatim}\na  b\n\\end{verbatim}" },
      "\\begin{verbatim}\na b\n\\end{verbatim}",
    );
    for (const [id, current, durable] of [
      ["begin-space", "\\begin {verbatim}\na  b\n\\end {verbatim}", "\\begin {verbatim}\na b\n\\end {verbatim}"],
      ["verbatim-out", "\\begin{VerbatimOut}{x}\na  b\n\\end{VerbatimOut}", "\\begin{VerbatimOut}{x}\na b\n\\end{VerbatimOut}"],
      ["lstinline", String.raw`Use \lstinline|a  b|.`, String.raw`Use \lstinline|a b|.`],
      ["mintinline", String.raw`Use \mintinline{text}|a  b|.`, String.raw`Use \mintinline{text}|a b|.`],
      ["obeyspaces", "\\obeyspaces a  b", "\\obeyspaces a b"],
      ["obeylines", "\\obeylines a\n b", "\\obeylines a b"],
    ] as const) {
      expectUnpinned({ id: `thm:${id}`, current }, durable);
    }

    const exactComment = { id: "thm:exact", current: "Claim%\nold" };
    expect(pinWhitespaceEquivalentCurrent(exactComment, exactComment.current)).toBe(exactComment);
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
