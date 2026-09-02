import { describe, it, expect, beforeAll, beforeEach, afterAll, vi } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, readdir, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import os from "node:os";
import path from "node:path";
import {
  runStage0Solve,
  assertClaimChangingStatementReplacementsArePaired,
  groupToProveByComponent,
  planStagedSolveDispatch,
  normalizeEmptySolveUnitContainers,
  repairSolveUnitLatexSerialization,
  selectDirectiveEmissionOwnerLabel,
  selectSemanticTargetOwners,
  collectConflictingSolveEmissions,
  projectOutputsToWriteCapabilities,
  selectLiveDurableProofOwners,
} from "../../src/discovery/stages/d0_solve.js";
import { runStage0Typed, partitionProposedChanges, findingKeys } from "../../src/discovery/stages/d0.js";
import { applyProposedChanges, discardAllProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { SolveUnitOutputSchema } from "../../src/discovery/solve/schemas.js";
import { proposalReviewPacketPath } from "../../src/discovery/discovery_paths.js";
import { readProofArchiveIndex } from "../../src/discovery/proof_archive.js";
import {
  assertMandateIntegrity,
  makeRequiredCoreEditMandate,
  makeRequiredCoreEditMandateCancellation,
  RequiredCoreEditMandateCancellationSchema,
  resolveRequiredCoreEditMandates,
} from "../../src/discovery/solve/mandates.js";
import { solveReuseReceiptsDir } from "../../src/discovery/solve/dispatch.js";
import { pruneOrphanStatementNotes } from "../../src/discovery/solve/merge.js";

/** Seed proposal kinds onto the SOLE carrier (`d0_working.json:proposals`),
 *  merging with any working state a test already wrote. */
async function seedWorkingProposals(
  ctx: PipelineContext,
  kinds: Partial<{ statements: unknown[]; definitions: unknown[]; assumptions: unknown[]; coreEdits: unknown[]; proofs: unknown[] }>,
): Promise<void> {
  const wp = workingPath(ctx);
  let working: Record<string, unknown> = { round: 1, solved: {} };
  if (existsSync(wp)) working = JSON.parse(await readFile(wp, "utf8"));
  const prior = (working.proposals ?? {}) as Record<string, unknown[]>;
  working.proposals = {
    statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [],
    ...prior,
    ...kinds,
  };
  await saveWorkingState(ctx, working as never);
  const persisted = await loadWorkingState(ctx);
  const carriesReviewedBundle = Object.values(kinds).some((entries) => (entries?.length ?? 0) > 0);
  if (carriesReviewedBundle && persisted?.proposals !== undefined) {
    const proto = CoreSchema.parse(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")));
    persisted.proposals.basis_revision = coreRevision(CoreSchema.parse(assembleCore(proto, persisted)));
    await saveWorkingState(ctx, persisted);
  }
}

/** The surfaced payload on the carrier (empty object when no working state). */
async function readSurfacedProposals(ctx: PipelineContext): Promise<Record<string, any[]>> {
  const wp = workingPath(ctx);
  if (!existsSync(wp)) return {};
  return (JSON.parse(await readFile(wp, "utf8")).proposals ?? {}) as Record<string, any[]>;
}
import {
  appendEscalationLog,
  computeValidNodes,
  escalationLogPath,
  loadWorkingState,
  readEscalationLog,
  saveWorkingState,
  snapshotMember,
  symbolBasis,
  workingPath,
  pruneOrphanLemmas,
} from "../../src/discovery/stages/d0_working.js";
import { canonicalLeanSubdir, promptPath, statePath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { CoreStatement } from "../../src/discovery/core/schema.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { coreRevision, definitionRevision } from "../../src/discovery/core/revision.js";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import { oeqSourceFingerprint } from "../../src/discovery/solve/oeq_source.js";

const QID = "stat_solvetest";
const SPEC = "v1";

it("normalizes only a literally empty prose update to omission", () => {
  const empty: Record<string, unknown> = { prose_updates: {}, proofs: [] };
  normalizeEmptySolveUnitContainers(empty);
  expect(empty).toEqual({ proofs: [] });

  const populated: Record<string, unknown> = { prose_updates: { tldr: "changed" } };
  normalizeEmptySolveUnitContainers(populated);
  expect(populated).toEqual({ prose_updates: { tldr: "changed" } });
});

it("canonicalizes under-escaped LaTeX throughout a solve-unit payload", () => {
  const body = {
    proposed_statement_changes: [{
      current: "See \\(\t" + "exttt{def:env}\\).",
      proposed: "Use \\(\t" + "ext{canonical}\\).",
    }],
    prose_updates: { tldr: "ordinary\ttab" },
  };
  repairSolveUnitLatexSerialization(body);
  expect(body.proposed_statement_changes[0].current).toBe(String.raw`See \(\texttt{def:env}\).`);
  expect(body.proposed_statement_changes[0].proposed).toBe(String.raw`Use \(\text{canonical}\).`);
  // Authored control characters are forbidden in pipeline text: a tab before a
  // letter is a lost TeX backslash and is restored (a wrong restore is visible
  // TeX garbage; the pre-repair alternative was silent corruption).
  expect(body.prose_updates.tldr).toBe(String.raw`ordinary\ttab`);
});

it("rejects an unpaired claim-changing statement replacement before merge", () => {
  const current = PROTO.statements[0] as CoreStatement;
  const proposed = `${current.statement} on the certified region`;
  const output = SolveUnitOutputSchema.parse({
    proofs: [{ id: current.id, proof_tex: "Proof of the proposed claim.", argues_proposed: true }],
    proposed_core_edits: [{
      kind: "statement-replace",
      id: current.id,
      proposed: { ...current, statement: proposed, free_symbols: [] },
      reason: "repair the claim",
      direction: "correct",
    }],
  });
  expect(() => assertClaimChangingStatementReplacementsArePaired(output, PROTO.statements as CoreStatement[]))
    .toThrow(/claim-changing statement-replace thm:main.*exactly one paired/i);
});

it("rejects argues_proposed proof bytes without a complete claim transaction", () => {
  const current = PROTO.statements[0] as CoreStatement;
  const output = SolveUnitOutputSchema.parse({
    proofs: [{ id: current.id, proof_tex: "Proof of a different claim.", argues_proposed: true }],
  });
  expect(() => assertClaimChangingStatementReplacementsArePaired(output, PROTO.statements as CoreStatement[]))
    .toThrow(/argues_proposed=true.*exactly one changed statement and post-image/i);
});

it("rejects empty obligation evidence and divergent duplicate dispositions", () => {
  expect(SolveUnitOutputSchema.safeParse({
    open_obligations: [{
      node_id: "oeq:tightness",
      what_is_open: "",
      obstruction: "",
      attempted: "",
    }],
  }).success).toBe(false);
  expect(SolveUnitOutputSchema.safeParse({
    proofs: [{ id: "thm:main", proof_tex: "   " }],
  }).success).toBe(false);

  const output = SolveUnitOutputSchema.parse({
    open_obligations: [
      {
        node_id: "oeq:tightness",
        what_is_open: "first disposition",
        obstruction: "first obstruction",
        attempted: "first route",
      },
      {
        node_id: "oeq:tightness",
        what_is_open: "second disposition",
        obstruction: "second obstruction",
        attempted: "second route",
      },
    ],
  });
  expect(() => collectConflictingSolveEmissions([output], ["thm:main"])).toThrow(
    /conflicting duplicate open-obligation payloads for oeq:tightness/i,
  );
});

it("rejects cross-channel-inconsistent correction bundles", () => {
  const definitionChange = {
    id: "def:band",
    current: "old formula",
    proposed: "new formula",
    reason: "correct the construction",
    direction: "correct",
  };
  const definitionReplace = {
    kind: "definition-replace",
    id: "def:band",
    proposed: {
      id: "def:band",
      name: "Band",
      construction: "new formula",
      free_symbols: [],
      inputs: [],
    },
    reason: "synchronize complete metadata",
    direction: "correct",
  };
  expect(SolveUnitOutputSchema.safeParse({
    proposed_definition_changes: [definitionChange],
  }).success).toBe(false);
  expect(SolveUnitOutputSchema.safeParse({
    proposed_definition_changes: [definitionChange],
    proposed_core_edits: [{
      ...definitionReplace,
      proposed: { ...definitionReplace.proposed, construction: "stale formula" },
    }],
  }).success).toBe(false);
  expect(SolveUnitOutputSchema.safeParse({
    proposed_definition_changes: [definitionChange],
    proposed_core_edits: [definitionReplace],
  }).success).toBe(true);

  const statementChange = {
    id: "thm:band",
    current: "old claim",
    proposed: "new claim",
    reason: "narrow the claim",
    direction: "narrow",
  };
  const statementReplace = {
    kind: "statement-replace",
    id: "thm:band",
    proposed: {
      id: "thm:band",
      kind: "theorem",
      statement: "new claim",
      free_symbols: [],
      depends_on: [],
      status: "to-prove",
    },
    reason: "synchronize the post-change proof basis",
    direction: "correct",
  };
  expect(SolveUnitOutputSchema.safeParse({
    proposed_statement_changes: [statementChange],
  }).success).toBe(false);
  expect(SolveUnitOutputSchema.safeParse({
    proposed_statement_changes: [statementChange],
    proposed_core_edits: [{
      ...statementReplace,
      proposed: { ...statementReplace.proposed, statement: "old claim" },
    }],
  }).success).toBe(false);
  expect(SolveUnitOutputSchema.safeParse({
    proposed_statement_changes: [statementChange],
    proposed_core_edits: [statementReplace],
  }).success).toBe(true);
});

it("quarantines an obligation emitted by neither the semantic nor directive owner", () => {
  const empty = () => SolveUnitOutputSchema.parse({});
  const obligation = SolveUnitOutputSchema.parse({
    open_obligations: [{
      node_id: "oeq:tightness",
      what_is_open: "the exact residual",
      obstruction: "no construction",
      attempted: "standard routes",
    }],
  });
  const projected = projectOutputsToWriteCapabilities({
    outputs: [empty(), empty(), obligation],
    dispatch: [
      { label: "oeq:tightness", targets: [{ id: "oeq:tightness" } as any], priorContext: "" },
      { label: "thm:main", targets: [{ id: "thm:main" } as any], priorContext: "" },
      { label: "lem:unrelated", targets: [{ id: "lem:unrelated" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([
      ["oeq:tightness", "oeq:tightness"],
      ["thm:main", "thm:main"],
      ["lem:unrelated", "lem:unrelated"],
    ]),
    directiveOwnerLabel: "thm:main",
    requiredCoreTargets: new Set(["oeq:tightness"]),
  });
  expect(projected.outputs[2].open_obligations).toEqual([]);
  expect(projected.quarantined).toContainEqual(expect.objectContaining({
    category: "open-obligation", target: "oeq:tightness", unit: "lem:unrelated",
  }));
});

it("quarantines a sibling's exact claim correction despite an authorized proof", () => {
  const ownerProof = SolveUnitOutputSchema.parse({
    proofs: [{ id: "prop:exact", proof_tex: "Proof of the unchanged exact claim." }],
  });
  const siblingCorrection = SolveUnitOutputSchema.parse({
    proposed_statement_changes: [{
      id: "prop:exact",
      current: "the unchanged exact claim",
      proposed: "the sibling's corrected exact claim",
      reason: "cross-component correction",
      direction: "narrow",
    }],
    proposed_core_edits: [{
      kind: "statement-replace",
      id: "prop:exact",
      proposed: {
        id: "prop:exact", kind: "proposition",
        statement: "the sibling's corrected exact claim",
        free_symbols: [], depends_on: [], status: "to-prove",
      },
      reason: "cross-component replacement",
      direction: "correct",
    }],
  });
  const result = projectOutputsToWriteCapabilities({
    outputs: [ownerProof, siblingCorrection],
    dispatch: [
      { label: "prop:exact", targets: [{ id: "prop:exact" } as any], priorContext: "" },
      { label: "thm:coordinator", targets: [{ id: "thm:coordinator" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([
      ["prop:exact", "prop:exact"],
      ["thm:coordinator", "thm:coordinator"],
    ]),
    directiveOwnerLabel: "thm:coordinator",
    requiredCoreTargets: new Set(["prop:exact"]),
    existingStatementIds: new Set(["prop:exact"]),
  });
  expect(result.outputs[1].proposed_statement_changes).toEqual([]);
  expect(result.outputs[1].proposed_core_edits).toEqual([]);
  expect(result.quarantined).toEqual(expect.arrayContaining([
    expect.objectContaining({
      unit: "thm:coordinator", owner: "prop:exact",
      category: "statement-change", target: "prop:exact",
    }),
    expect.objectContaining({
      unit: "thm:coordinator", owner: "prop:exact",
      category: "core-edit", target: "prop:exact", operation: "statement-replace",
    }),
  ]));
});

it("uses durable ownership only to arbitrate an undispatched proof refresh", () => {
  const ownerOutput = SolveUnitOutputSchema.parse({
    proofs: [{ id: "lem:carried", proof_tex: "Refreshed proof.", argues_proposed: true }],
    proposed_statement_changes: [{
      id: "lem:carried",
      current: "old carried claim",
      proposed: "narrowed carried claim",
      reason: "narrow to the proved statement",
      direction: "narrow",
    }],
    proposed_core_edits: [{
      kind: "statement-replace",
      id: "lem:carried",
      proposed: {
        id: "lem:carried", kind: "lemma", statement: "narrowed carried claim",
        free_symbols: [], depends_on: [], status: "to-prove",
      },
      reason: "carry the narrowed agent-authored node",
      direction: "correct",
    }],
  });
  const siblingOutput = SolveUnitOutputSchema.parse({
    proofs: [{ id: "lem:carried", proof_tex: "Sibling overwrite." }],
  });
  const empty = SolveUnitOutputSchema.parse({});
  const result = projectOutputsToWriteCapabilities({
    outputs: [ownerOutput, siblingOutput],
    dispatch: [
      { label: "thm:owner", targets: [{ id: "thm:owner" } as any], priorContext: "" },
      { label: "thm:sibling", targets: [{ id: "thm:sibling" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([
      ["thm:owner", "thm:owner"],
      ["thm:sibling", "thm:sibling"],
    ]),
    durableTargetOwners: new Map([["lem:carried", "thm:owner"]]),
    directiveOwnerLabel: "thm:owner",
    requiredCoreTargets: new Set(),
    existingStatementIds: new Set(["lem:carried"]),
  });
  expect(result.outputs[0].proofs).toEqual([
    expect.objectContaining({ id: "lem:carried", proof_tex: "Refreshed proof.", argues_proposed: true }),
  ]);
  expect(result.outputs[1].proofs).toEqual(empty.proofs);
  expect(result.quarantined).toContainEqual(expect.objectContaining({
    unit: "thm:sibling", owner: "thm:owner", category: "proof", target: "lem:carried",
  }));
});

it("keeps existing-node notes with the directive-wide prose owner", () => {
  const output = SolveUnitOutputSchema.parse({
    prose_updates: {
      tldr: "valid paper-wide prose",
      statement_notes: [{ id: "lem:carried", consumer: "directive-owned node metadata" }],
    },
  });
  const result = projectOutputsToWriteCapabilities({
    outputs: [output],
    dispatch: [{ label: "thm:prose-owner", targets: [{ id: "thm:prose-owner" } as any], priorContext: "" }],
    semanticTargetOwners: new Map([["thm:prose-owner", "thm:prose-owner"]]),
    durableTargetOwners: new Map([["lem:carried", "thm:other-owner"]]),
    directiveOwnerLabel: "thm:prose-owner",
    requiredCoreTargets: new Set(),
    existingStatementIds: new Set(["lem:carried"]),
  });
  expect(result.outputs[0].prose_updates?.tldr).toBe("valid paper-wide prose");
  expect(result.outputs[0].prose_updates?.statement_notes).toEqual([
    expect.objectContaining({ id: "lem:carried", consumer: "directive-owned node metadata" }),
  ]);
  expect(result.quarantined).not.toContainEqual(expect.objectContaining({
    category: "statement-note", target: "lem:carried",
  }));
});

it("keeps a unique cited addition local to its downstream emitter", () => {
  const empty = SolveUnitOutputSchema.parse({});
  const cited = SolveUnitOutputSchema.parse({
    added_lemmas: [{
      id: "lem:new-cited", kind: "lemma", statement: "external fact", depends_on: [],
      status: "cited", source: { cite: "External2026", locator: "Theorem 1" },
    }],
  });
  const result = projectOutputsToWriteCapabilities({
    outputs: [empty, cited],
    dispatch: [
      { label: "thm:directive-owner", targets: [{ id: "thm:directive-owner" } as any], priorContext: "" },
      { label: "thm:sibling", targets: [{ id: "thm:sibling" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([
      ["thm:directive-owner", "thm:directive-owner"], ["thm:sibling", "thm:sibling"],
    ]),
    directiveOwnerLabel: "thm:directive-owner",
    requiredCoreTargets: new Set(),
  });
  expect(result.outputs[1].added_lemmas).toEqual([expect.objectContaining({ id: "lem:new-cited" })]);
  expect(result.quarantined).not.toContainEqual(expect.objectContaining({
    category: "cited-added-node", target: "lem:new-cited",
  }));
});

it("does not let a sibling delete another owner's durable node", () => {
  const empty = SolveUnitOutputSchema.parse({});
  const deletion = SolveUnitOutputSchema.parse({
    proposed_core_edits: [{
      kind: "statement-delete", id: "lem:durable-owned", replacement_id: "lem:replacement",
      reason: "unrelated deletion", direction: "delete-obsolete",
    }],
  });
  const result = projectOutputsToWriteCapabilities({
    outputs: [empty, deletion],
    dispatch: [
      { label: "thm:owner", targets: [{ id: "thm:owner" } as any], priorContext: "" },
      { label: "thm:sibling", targets: [{ id: "thm:sibling" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([["thm:owner", "thm:owner"], ["thm:sibling", "thm:sibling"]]),
    durableTargetOwners: new Map([["lem:durable-owned", "thm:owner"]]),
    directiveOwnerLabel: "thm:owner",
    requiredCoreTargets: new Set(),
    existingStatementIds: new Set(["lem:durable-owned"]),
  });
  expect(result.outputs[1].proposed_core_edits).toEqual([]);
  expect(result.quarantined).toContainEqual(expect.objectContaining({
    unit: "thm:sibling", owner: "thm:owner", category: "core-edit", target: "lem:durable-owned",
  }));
});

it("assigns same-round new-node notes to the node emitter", () => {
  const note = SolveUnitOutputSchema.parse({
    prose_updates: { statement_notes: [{ id: "lem:new-owned", consumer: "guessed metadata" }] },
  });
  const node = SolveUnitOutputSchema.parse({
    added_lemmas: [{
      id: "lem:new-owned", kind: "lemma", statement: "new fact", depends_on: [],
      status: "proved", proof_tex: "Proof.",
    }],
  });
  const result = projectOutputsToWriteCapabilities({
    outputs: [note, node],
    dispatch: [
      { label: "thm:directive-owner", targets: [{ id: "thm:directive-owner" } as any], priorContext: "" },
      { label: "thm:node-owner", targets: [{ id: "thm:node-owner" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([
      ["thm:directive-owner", "thm:directive-owner"], ["thm:node-owner", "thm:node-owner"],
    ]),
    directiveOwnerLabel: "thm:directive-owner",
    requiredCoreTargets: new Set(),
  });
  expect(result.outputs[0].prose_updates?.statement_notes).toEqual([]);
  expect(result.outputs[1].added_lemmas).toHaveLength(1);
  expect(result.quarantined).toContainEqual(expect.objectContaining({
    unit: "thm:directive-owner", owner: "thm:node-owner", category: "statement-note", target: "lem:new-owned",
  }));
});

it("lets only the durable owner re-emit an existing shelved node through added_lemmas", () => {
  const recovered = {
    id: "prop:recovered-shelved", kind: "proposition", statement: "the durable proposition",
    depends_on: [], status: "proved", proof_tex: "Recovered proof.",
  } as any;
  const ownerOutput = SolveUnitOutputSchema.parse({ added_lemmas: [recovered] });
  const siblingOutput = SolveUnitOutputSchema.parse({
    added_lemmas: [{ ...recovered, proof_tex: "Sibling overwrite." }],
  });
  const result = projectOutputsToWriteCapabilities({
    outputs: [ownerOutput, siblingOutput],
    dispatch: [
      { label: "thm:canonical", targets: [{ id: "thm:member" } as any], priorContext: "" },
      { label: "thm:sibling", targets: [{ id: "thm:sibling" } as any], priorContext: "" },
    ],
    semanticTargetOwners: new Map([
      ["thm:member", "thm:canonical"],
      ["thm:sibling", "thm:sibling"],
    ]),
    durableTargetOwners: new Map([[recovered.id, "thm:canonical"]]),
    directiveOwnerLabel: "thm:canonical",
    requiredCoreTargets: new Set(),
    existingStatementIds: new Set([recovered.id]),
  });
  expect(result.outputs[0].added_lemmas).toEqual([recovered]);
  expect(result.outputs[1].added_lemmas).toEqual([]);
  expect(result.quarantined).toContainEqual(expect.objectContaining({
    unit: "thm:sibling", owner: "thm:canonical", category: "added-node", target: recovered.id,
  }));
});

it("recovers durable owners through the live assembled dependency closure", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const helper2 = node("lem:helper-2");
  const helper1 = node("lem:helper-1", [helper2.id]);
  const unrelated = node("lem:unrelated-history");
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:main", [helper1.id])],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:main", "thm:main"]]),
    durableRecords: new Map([
      [helper1.id, { owner: "thm:historical", node: helper1 }],
      [helper2.id, { owner: "thm:historical", node: helper2 }],
      [unrelated.id, { owner: "thm:other", node: unrelated }],
    ]),
  });
  expect(owners).toEqual(new Map([
    [helper1.id, "thm:main"],
    [helper2.id, "thm:main"],
  ]));
});

it("normalizes a durable mathematical owner through its current WCC unit label", () => {
  const child = {
    id: "prop:durable-child", kind: "proposition", statement: "child",
    depends_on: [], status: "to-prove",
  } as any;
  const owners = selectLiveDurableProofOwners({
    coreStatements: [],
    requiredIds: new Set([child.id]),
    activeTargetOwners: new Map([["thm:component-member", "thm:canonical-label"]]),
    durableRecords: new Map([[child.id, {
      owner: "thm:component-member", node: child,
    }]]),
  });
  expect(owners.get(child.id)).toBe("thm:canonical-label");
});

// Supersedes the fail-closed ambiguity contract: two active components reaching one
// shared durable node is a NORMAL consequence of the dispatch partition (coupling
// edges run only through OPEN statements), and throwing here aborted whole paid
// rounds deterministically on every resume (exp_multiarm 3x, eid_periodic,
// exp_two_wave, 2026-08-29/30). The node is now left unowned (sole emissions land
// via the sole-emitter fallback; competing ones are conflict-dropped), unless its
// durable record names one of the reaching components, which then keeps it.
it("leaves a shared shelved durable helper unowned instead of aborting", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const helper = node("lem:shared-shelved");
  const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:a", [helper.id]), node("thm:b", [helper.id])],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:a", "thm:a"], ["thm:b", "thm:b"]]),
    durableRecords: new Map([[helper.id, { owner: "thm:historical", node: helper }]]),
  });
  expect(owners.has(helper.id)).toBe(false);
  expect(warn.mock.calls.flat().join("\n")).toMatch(
    /shared live durable node 'lem:shared-shelved'.*thm:a, thm:b/i,
  );
  warn.mockRestore();
});

it("keeps a shared durable helper with its recorded owner when that owner is reaching", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const helper = node("lem:shared-owned");
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:a", [helper.id]), node("thm:b", [helper.id])],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:a", "thm:a"], ["thm:b", "thm:b"]]),
    durableRecords: new Map([[helper.id, { owner: "thm:a", node: helper }]]),
  });
  expect(owners.get(helper.id)).toBe("thm:a");
});

it("leaves an untouched shared durable helper unowned", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const helper = node("lem:shared-immutable");
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:a", [helper.id]), node("thm:b", [helper.id])],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:a", "thm:a"], ["thm:b", "thm:b"]]),
    durableRecords: new Map([[helper.id, { owner: "thm:historical", node: helper }]]),
    writableIds: new Set(),
  });
  expect(owners.has(helper.id)).toBe(false);
});

it("leaves a written shared durable helper unowned instead of aborting", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const helper = node("lem:shared-written");
  const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:a", [helper.id]), node("thm:b", [helper.id])],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:a", "thm:a"], ["thm:b", "thm:b"]]),
    durableRecords: new Map([[helper.id, { owner: "thm:historical", node: helper }]]),
    writableIds: new Set([helper.id]),
  });
  expect(owners.has(helper.id)).toBe(false);
  expect(warn.mock.calls.flat().join("\n")).toMatch(/lem:shared-written/);
  warn.mockRestore();
});

it("stops durable reachability at an explicitly owned sibling target", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const privateLeaf = node("lem:private-leaf");
  const ownedTarget = node("prop:owned-target", [privateLeaf.id]);
  const consumerA = node("thm:consumer-a", [ownedTarget.id]);
  const consumerB = node("thm:consumer-b", [ownedTarget.id]);
  const owners = selectLiveDurableProofOwners({
    coreStatements: [consumerA, consumerB, ownedTarget],
    requiredIds: new Set(),
    activeTargetOwners: new Map([
      [consumerA.id, consumerA.id],
      [consumerB.id, consumerB.id],
      [ownedTarget.id, ownedTarget.id],
    ]),
    durableRecords: new Map([
      [ownedTarget.id, { owner: "thm:historical", node: ownedTarget }],
      [privateLeaf.id, { owner: "thm:historical", node: privateLeaf }],
    ]),
  });
  expect(owners.has(ownedTarget.id)).toBe(false);
  expect(owners.get(privateLeaf.id)).toBe(ownedTarget.id);
});

it("finds a shelved durable helper through an ordinary current-core bridge", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const helper = node("lem:shelved-leaf");
  const bridge = node("prop:current-bridge", [helper.id]);
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:main", [bridge.id]), bridge],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:main", "thm:main"]]),
    durableRecords: new Map([[helper.id, { owner: "thm:old", node: helper }]]),
  });
  expect(owners.get(helper.id)).toBe("thm:main");
});

it("assigns reachable published ownerless core nodes to the sole active root", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "proved", proof_tex: `Proof of ${id}.`,
  }) as any;
  const leaf = node("lem:published-ownerless-leaf");
  const bridge = node("lem:published-ownerless-bridge", [leaf.id]);
  const root = node("thm:main", [bridge.id]);
  const owners = selectLiveDurableProofOwners({
    coreStatements: [root, bridge, leaf],
    requiredIds: new Set(),
    activeTargetOwners: new Map([[root.id, root.id]]),
    durableRecords: new Map(),
  });
  expect(owners).toEqual(new Map([
    [bridge.id, root.id],
    [leaf.id, root.id],
  ]));
});

it("leaves a published ownerless core node reached by two roots unowned", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "proved", proof_tex: `Proof of ${id}.`,
  }) as any;
  const shared = node("lem:published-ownerless-shared");
  const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
  const owners = selectLiveDurableProofOwners({
    coreStatements: [node("thm:a", [shared.id]), node("thm:b", [shared.id]), shared],
    requiredIds: new Set(),
    activeTargetOwners: new Map([["thm:a", "thm:a"], ["thm:b", "thm:b"]]),
    durableRecords: new Map(),
  });
  expect(owners.has(shared.id)).toBe(false);
  expect(warn.mock.calls.flat().join("\n")).toMatch(/published-ownerless-shared/);
  warn.mockRestore();
});

it("follows an authorized statement postimage and durable proof-snapshot edges", () => {
  const node = (id: string, depends_on: string[] = []) => ({
    id, kind: "lemma", statement: id, depends_on, status: "to-prove",
  }) as any;
  const leaf = node("lem:snapshot-leaf");
  const helper = node("lem:durable-helper");
  const root = node("thm:main");
  const owners = selectLiveDurableProofOwners({
    coreStatements: [root],
    requiredIds: new Set(),
    activeTargetOwners: new Map([[root.id, root.id]]),
    statementPostimages: new Map([[root.id, { ...root, depends_on: [helper.id] }]]),
    durableRecords: new Map([
      [helper.id, { owner: "thm:old", node: helper, proofDependencies: [leaf.id] }],
      [leaf.id, { owner: "thm:old", node: leaf }],
    ]),
  });
  expect(owners).toEqual(new Map([
    [helper.id, root.id],
    [leaf.id, root.id],
  ]));
});

const PROTO = {
  qid: QID,
  specialization: SPEC,
  cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [
    {
      id: "ass:overlap",
      kind: "support",
      condition: "the propensity is bounded away from 0 and 1",
      free_symbols: [],
      standard: { name: "overlap", cite: "Rosenbaum1983" },
    },
  ],
  definitions: [
    { id: "def:env", name: "U", construction: "U = a", inputs: ["a"] },
    { id: "def:class", name: "W", construction: "{ P : P satisfies ass:overlap }", by_member_properties: ["ass:overlap"] },
  ],
  statements: [
    { id: "thm:main", kind: "theorem", statement: "tau is identified", depends_on: ["ass:overlap"], status: "to-prove", justification: "core ID", gap: "vs prior", consumer: "applied" },
    { id: "prop:aux", kind: "proposition", statement: "a supporting fact", depends_on: ["ass:overlap"], status: "to-prove", justification: "supports thm", gap: "vs prior", consumer: "thm:main" },
  ],
  target_estimand: "tau = E[Y(1) - Y(0)]",
  bibliography: [{ key: "Rosenbaum1983" }],
};

/** Keep correction fixtures on the production contract: a formula/claim
 * correction and its complete core post-image travel as one pair. */
function withCorrectionPairs(
  body: Record<string, any>,
  core: Record<string, any> = PROTO,
): Record<string, any> {
  const edits = [...(body.proposed_core_edits ?? [])];
  for (const change of body.proposed_definition_changes ?? []) {
    if (edits.some((edit) => edit.kind === "definition-replace" && edit.id === change.id)) continue;
    const prior = core.definitions?.find((definition: any) => definition.id === change.id) ?? {
      id: change.id, name: change.id, inputs: [],
    };
    edits.push({
      kind: "definition-replace",
      id: change.id,
      proposed: { ...prior, construction: change.proposed, free_symbols: prior.free_symbols ?? [] },
      reason: "synchronize the complete corrected definition",
      direction: "correct",
    });
  }
  for (const change of body.proposed_statement_changes ?? []) {
    if (edits.some((edit) => edit.kind === "statement-replace" && edit.id === change.id)) continue;
    const prior = core.statements?.find((statement: any) => statement.id === change.id) ?? {
      id: change.id,
      kind: change.id.startsWith("lem:") ? "lemma" : "theorem",
      depends_on: [],
      status: "to-prove",
    };
    const { proof_tex: _proofTex, ...metadata } = prior;
    edits.push({
      kind: "statement-replace",
      id: change.id,
      proposed: {
        ...metadata,
        statement: change.proposed,
        status: prior.status === "proved" ? "to-prove" : (prior.status ?? "to-prove"),
        free_symbols: prior.free_symbols ?? [],
      },
      reason: "synchronize the complete corrected statement",
      direction: "correct",
    });
  }
  return edits.length > 0 ? { ...body, proposed_core_edits: edits } : body;
}

let repoRoot: string;

async function stubPrompts(root: string): Promise<void> {
  const stub = async (name: string, body: string) => {
    const t = promptPath(root, name);
    await mkdir(path.dirname(t), { recursive: true });
    await writeFile(t, body, "utf8");
  };
  await stub("stage0_common_discovery.txt", "stub common");
  await stub("stage0_setup_stat.txt", "stub stat setup");
  await stub("stage0_solve.txt", "stub solver");
}

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}
function makeState(): StateJson {
  return {
    stage_completed: "0",
    // Must satisfy saveState's qid/lean_subdir invariant: runStage0Typed persists
    // the round budget before dispatch, so the stub state gets saved for real.
    lean_subdir: canonicalLeanSubdir(QID),
    design_decisions: {},
    added_assumptions: [],
    proposed_from: { topic: "t", novelty_target: "field", cluster: "stat" },
    flags: {},
  } as unknown as StateJson;
}
function makeVersionedState(version = 1): StateJson {
  const state = makeState();
  state.proposed_from!.current_angle_index = 0;
  state.proposed_from!.current_version = version;
  return state;
}

/** Mock solver: parse SOLVE_OUTPUT_PATH + the TARGET block from the prompt, write
 *  a proof for each target id (or a proposed change, per `mode`). */
function solverDeps(mode: "prove" | "propose" | "propose-def" | "propose-def-class" | "core-edit"): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
      let body: Record<string, unknown>;
      if (mode === "propose" && targets.some((t) => t.id === "thm:main")) {
        body = {
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_statement_changes: [
            { id: "thm:main", current: "tau is identified", proposed: "tau is identified on the overlap region", reason: "too strong without overlap on full support", direction: "narrow" },
          ],
        };
      } else if ((mode === "propose-def" || mode === "propose-def-class") && targets.some((t) => t.id === "thm:main")) {
        // the claim's SHAPE is right but a referenced constructed-object formula is too small → correct the DEF.
        const target = mode === "propose-def" ? "def:env" : "def:class"; // class target must be ignored
        // propose-def: leave thm unproven (it depends on the corrected def) → checkpoint.
        // propose-def-class: the class change is illegal/ignored, so prove the targets → clean discharge.
        body = {
          proofs: mode === "propose-def-class" ? targets.map((t) => ({ id: t.id, proof_tex: "QED." })) : [],
          added_lemmas: [],
          proposed_statement_changes: [],
          proposed_definition_changes: [
            { id: target, current: "U = a", proposed: "U = a + b", reason: "proof shows the envelope omits the b term", direction: "correct" },
          ],
        };
      } else if (mode === "core-edit" && targets.some((t) => t.id === "thm:main")) {
        body = {
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
          proposed_core_edits: [{
            kind: "statement-replace",
            id: "thm:main",
            proposed: {
              id: "thm:main", kind: "theorem", statement: "tau is identified",
              depends_on: ["ass:overlap", "def:env"], status: "to-prove",
              justification: "core ID", gap: "vs prior", consumer: "applied",
            },
            reason: "declare the already-used envelope dependency",
            direction: "correct",
          }],
        };
      } else {
        body = { proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })), added_lemmas: [], proposed_statement_changes: [] };
      }
      await writeFile(outPath, JSON.stringify(withCorrectionPairs(body)), "utf8");
      return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage0solve-"));
  await stubPrompts(repoRoot);
  const p = protoCoreJsonPath(makeCtx(repoRoot));
  await mkdir(path.dirname(p), { recursive: true });
  await writeFile(p, JSON.stringify(PROTO), "utf8");
});
afterAll(async () => { await rm(repoRoot, { recursive: true, force: true }); });

// Each test starts from the frozen proto only — clear carried working state, the
// escalation log, and any prior round's output so tests don't leak into each other.
beforeEach(async () => {
  const ctx = makeCtx(repoRoot);
  const dir = path.dirname(coreJsonPath(ctx));
  for (const f of await readdir(dir)) {
    if (f.includes("proto_core")) continue;
    await rm(path.join(dir, f), { recursive: true, force: true });
  }
  // restore the canonical proto so each test is isolated (reuse tests overwrite it
  // within a single `it()`, where beforeEach does not fire between calls).
  await writeFile(protoCoreJsonPath(ctx), JSON.stringify(PROTO), "utf8");
  // runStage0Typed persists the round budget to state.json before dispatch; the
  // harness's stub state is deliberately minimal, so a leaked file fails the strict
  // StateJson parse in tests that load state when it exists. Each test starts stateless.
  await rm(statePath(repoRoot, QID, SPEC), { force: true });
});

/** Mock that records the target-id sets it was asked to solve, proving each. */
function countingDeps(): { deps: StageDeps; calls: () => string[][] } {
  const calls: string[][] = [];
  const deps: StageDeps = {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
      calls.push(targets.map((t) => t.id));
      const body = { proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })), added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [] };
      await writeFile(outPath, JSON.stringify(body), "utf8");
      return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
  return { deps, calls: () => calls };
}

// one statement depending on a constructed-object def, so a def edit invalidates it.
const REUSE_PROTO = {
  ...PROTO,
  statements: [
    { id: "thm:a", kind: "theorem", statement: "A holds", depends_on: ["def:env"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
  ],
};

describe("incremental reuse across escalation rounds", () => {
  it("rejects a worker that mutates the immutable frozen-core snapshot", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const snapshotPath = /CORE_SNAPSHOT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(snapshotPath, '{"corrupt":true}\n', "utf8");
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:a", proof_tex: "QED." }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /modified immutable frozen-core snapshot/i,
    );
  });

  it("fails before dispatch when the D0 escalation journal has a torn row", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(escalationLogPath(ctx), '{"round":1,"directive":"truncated', "utf8");
    let calls = 0;
    const deps: StageDeps = {
      runCodex: async () => {
        calls += 1;
        throw new Error("must not dispatch");
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /escalation journal is corrupt.*refusing to skip/i,
    );
    expect(calls).toBe(0);
  });

  it("does not reuse a stale solve artifact when the current worker writes nothing", async () => {
    const ctx = makeCtx(repoRoot);
    const discoveryDir = path.dirname(protoCoreJsonPath(ctx));
    await writeFile(path.join(discoveryDir, "solve_thm_main.json"), JSON.stringify({
      proofs: [{ id: "thm:main", proof_tex: "stale proof" }],
    }), "utf8");
    await writeFile(path.join(discoveryDir, "solve_prop_aux.json"), JSON.stringify({
      proofs: [{ id: "prop:aux", proof_tex: "stale proof" }],
    }), "utf8");
    const deps: StageDeps = {
      runCodex: async () => ({
        stdout: JSON.stringify({ status: "completed", message: "claimed completion" }),
        stderr: "",
      }),
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /completed without writing/i,
    );
    expect(existsSync(path.join(discoveryDir, "solve_thm_main.json"))).toBe(false);
    expect(existsSync(path.join(discoveryDir, "solve_prop_aux.json"))).toBe(false);
  });

  it("accepts a valid persisted artifact when only the stdout receipt is malformed", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    let calls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        calls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:a", proof_tex: "QED." }],
        }), "utf8");
        return { stdout: "not a JSON completion receipt", stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result).toBe(false);
    expect(calls).toBe(1);
    expect(warn.mock.calls.flat().join("\n")).toMatch(/stdout receipt was unparseable.*accepting it without a model retry/i);
    warn.mockRestore();
  });

  it("repairs common JSON/TeX serialization in the orchestrator without a second model call", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    let calls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        calls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        // Deliberately invalid JSON escapes around TeX. The raw-byte normalizer
        // can recover these exactly, so Sol must not be called again.
        await writeFile(
          outPath,
          String.raw`{"proofs":[{"id":"thm:a","proof_tex":"Proof of \(\theta=0\)."}]}`,
          "utf8",
        );
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result).toBe(false);
    expect(calls).toBe(1);
  });

  it("repeats Sol only when a damaged JSON carrier cannot be accepted deterministically", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        prompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        if (prompt.includes("MODEL-CALL RECOVERY — NO TRUSTWORTHY ARTIFACT")) {
          await writeFile(outPath, JSON.stringify({
            proofs: [{ id: "thm:a", proof_tex: "QED." }],
          }), "utf8");
        } else {
          // Usable mathematical content, mechanically truncated JSON carrier.
          await writeFile(outPath, '{"proofs":[{"id":"thm:a","proof_tex":"QED."}]', "utf8");
        }
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result).toBe(false);
    expect(prompts).toHaveLength(2);
    expect(prompts[1]).toContain("MODEL-CALL RECOVERY — NO TRUSTWORTHY ARTIFACT");
    expect(prompts[1]).toContain("FROZEN CORE");
    expect(prompts[1]).not.toContain("D0 ORCHESTRATOR MECHANICAL ARTIFACT REPAIR");
  });

  it("treats residual unsealable TeX as a failed model call, not a clerical model task", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        prompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const repaired = prompt.includes("MODEL-CALL RECOVERY — NO TRUSTWORTHY ARTIFACT");
        await writeFile(outPath, JSON.stringify({
          proofs: [{
            id: "thm:a",
            proof_tex: repaired ? String.raw`Proof of \(A\).` : String.raw`Proof of \(A.`,
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result).toBe(false);
    expect(prompts).toHaveLength(2);
    expect(prompts[1]).toContain("MODEL-CALL RECOVERY — NO TRUSTWORTHY ARTIFACT");
    expect(prompts[1]).not.toContain("D0 ORCHESTRATOR MECHANICAL ARTIFACT REPAIR");
  });

  it("drains every sibling solve worker before propagating a unit failure", async () => {
    const ctx = makeCtx(repoRoot);
    let siblingFinished = false;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        if (outPath.includes("thm_main")) throw new Error("intentional fast unit failure");
        await new Promise((resolve) => setTimeout(resolve, 75));
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "prop:aux", proof_tex: "Delayed sibling proof." }],
          added_lemmas: [],
        }), "utf8");
        siblingFinished = true;
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /intentional fast unit failure/,
    );
    expect(siblingFinished).toBe(true);
    expect(existsSync(path.join(path.dirname(protoCoreJsonPath(ctx)), "solve_prop_aux.json"))).toBe(true);
  });

  it("rejects conflicting duplicate helper emissions instead of choosing by unit order", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "synchronize this directed round while preserving unexpected-conflict detection",
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const target = outPath.includes("prop_aux") ? "prop:aux" : "thm:main";
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: [{ id: target, proof_tex: "QED." }],
          added_lemmas: [{
            id: "lem:shared-helper",
            kind: "lemma",
            statement: target === "thm:main" ? "First incompatible claim." : "Second incompatible claim.",
            depends_on: [],
            status: "proved",
            proof_tex: "Proof.",
          }],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    // A CROSS-unit collision no longer aborts the round: aborting discarded every
    // unit's work, including units unrelated to the collision. The property this test
    // protects is unchanged -- neither payload may be chosen, so the assembled core
    // stays independent of unit order -- but it is now enforced by withholding BOTH
    // variants and reporting them, not by throwing away the round.
    //
    // The collision must also REACH the orchestrator. Here it drops the round's only
    // proposals, so every proposal list is empty; gating the checkpoint solely on those
    // lists skipped it, leaving the conflict unreported and the run advancing silently
    // -- worse than the abort this replaced, which at least failed loudly.
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(
      core.statements.some((s: { id: string }) => s.id === "lem:shared-helper"),
      "neither conflicting variant may land",
    ).toBe(false);
    expect(result, "a withheld collision must checkpoint on its own").toHaveProperty("status", "checkpoint");
    expect(String((result as { message?: string }).message ?? ""), "the diagnostic must name the colliding id")
      .toMatch(/lem:shared-helper/);
  });

  it("quarantines consumers of a withheld helper while committing unrelated work", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "lem:unrelated", kind: "lemma", statement: "an unrelated target",
      depends_on: [], status: "to-prove",
      justification: "regression witness", gap: "none", consumer: "test",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = targets.some((target) => target.id === "thm:main")
          ? "main"
          : targets.some((target) => target.id === "prop:aux") ? "aux" : null;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `QED ${target.id}.` })),
          added_lemmas: owner === null ? [] : [
            {
              id: "lem:shared-helper", kind: "lemma",
              statement: owner === "main" ? "first incompatible helper" : "second incompatible helper",
              depends_on: [], status: "proved", proof_tex: `Proof of ${owner} helper.`,
            },
            {
              id: `lem:${owner}-consumer`, kind: "lemma", statement: `${owner} consumer`,
              depends_on: owner === "main" ? [] : ["lem:main-consumer"], status: "proved",
              proof_tex: owner === "main" ? "By lem:shared-helper." : "By lem:main-consumer.",
            },
          ],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "lem:unrelated")?.status).toBe("proved");
    expect(core.statements.some((statement: any) =>
      ["lem:shared-helper", "lem:main-consumer", "lem:aux-consumer"].includes(statement.id)
    )).toBe(false);
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.conflict_consumers).toEqual(["lem:aux-consumer", "lem:main-consumer"]);
  });

  it("quarantines an inline proved consumer that reaches a conflict through an unchanged intermediate", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.push(
      {
        id: "lem:existing-shared", kind: "lemma", statement: "the durable shared claim",
        depends_on: [], status: "proved", proof_tex: "Durable proof.",
        justification: "regression witness", gap: "none", consumer: "intermediate",
      },
      {
        id: "lem:unchanged-mid", kind: "lemma", statement: "the unchanged intermediate",
        depends_on: ["lem:existing-shared"], status: "proved", proof_tex: "By the shared claim.",
        justification: "regression witness", gap: "none", consumer: "downstream",
      },
    );
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = targets.some((target) => target.id === "thm:main")
          ? "main"
          : targets.some((target) => target.id === "prop:aux") ? "aux" : null;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `QED ${target.id}.` })),
          added_lemmas: owner === null ? [] : [
            {
              id: "lem:existing-shared", kind: "lemma",
              statement: owner === "main" ? "first incompatible correction" : "second incompatible correction",
              depends_on: [], status: "proved", proof_tex: `Proof of ${owner} correction.`,
            },
            ...(owner === "main" ? [{
              id: "lem:indirect-inline-consumer", kind: "lemma",
              statement: "an inline result authored against the contested variant",
              depends_on: ["lem:unchanged-mid"], status: "proved", proof_tex: "By the unchanged intermediate.",
            }] : []),
          ],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "lem:existing-shared")?.statement)
      .toBe("the durable shared claim");
    expect(core.statements.some((statement: any) => statement.id === "lem:indirect-inline-consumer"))
      .toBe(false);
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.conflict_consumers).toContain("lem:indirect-inline-consumer");
  });

  it("quarantines a definition proposal that consumes a conflicted definition", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "lem:unrelated", kind: "lemma", statement: "unrelated definition-conflict witness",
      depends_on: [], status: "to-prove",
      justification: "regression witness", gap: "none", consumer: "test",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = targets.some((target) => target.id === "thm:main")
          ? "main"
          : targets.some((target) => target.id === "prop:aux") ? "aux" : null;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `QED ${target.id}.` })),
          proposed_core_edits: owner === null ? [] : [
            {
              kind: "definition-add", id: "def:shared",
              proposed: {
                id: "def:shared", name: "shared",
                construction: owner === "main" ? "first incompatible definition" : "second incompatible definition",
                inputs: [],
              },
              reason: "unit-local shared construction", direction: "correct",
            },
            ...(owner === "main" ? [{
              kind: "definition-add" as const, id: "def:consumer",
              proposed: {
                id: "def:consumer", name: "consumer",
                construction: "constructed from def:shared", inputs: ["def:shared"],
              },
              reason: "consume the shared construction", direction: "correct" as const,
            }] : []),
          ],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.conflict_consumers).toContain("def:consumer");
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: "core-edit", target: "def:consumer", reason: "conflicted-dependency-consumer",
        payload: expect.objectContaining({ kind: "definition-add", id: "def:consumer" }),
      }),
    ]));
    const proposals = await readSurfacedProposals(ctx);
    expect(proposals.coreEdits ?? []).not.toEqual(expect.arrayContaining([
      expect.objectContaining({ id: "def:consumer" }),
    ]));
  });

  it("surfaces a conflict-quarantined exact target instead of aborting unrelated work", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "lem:unrelated", kind: "lemma", statement: "an unrelated exact-round target",
      depends_on: [], status: "to-prove",
      justification: "regression witness", gap: "none", consumer: "test",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "repair thm:main exactly",
      required_core_targets: ["thm:main", "prop:aux", "lem:unrelated"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const hasMain = targets.some((target) => target.id === "thm:main");
        const hasAux = targets.some((target) => target.id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({
            id: target.id,
            proof_tex: target.id === "thm:main" ? "By lem:shared-helper." : `QED ${target.id}.`,
          })),
          added_lemmas: hasMain || hasAux ? [{
            id: "lem:shared-helper", kind: "lemma",
            statement: hasMain ? "first incompatible helper" : "second incompatible helper",
            depends_on: [], status: "proved", proof_tex: "Helper proof.",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "lem:unrelated")?.status).toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.conflict_consumers).toContain("thm:main");
  });

  it("persists an invalid OEQ resolution as withheld content on an otherwise complete round", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "resolve the remaining question and preserve all unrelated proofs",
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const isMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `QED ${target.id}.` })),
          resolved_oeqs: isMain ? [{
            source_id: "oeq:no-longer-live",
            theorem: {
              id: "thm:stale-answer", kind: "theorem", statement: "a stale answer",
              depends_on: [], status: "proved", proof_tex: "Stale proof.",
            },
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.invalid_resolutions).toEqual(["oeq:no-longer-live→thm:stale-answer"]);
  });

  it("surfaces an ownership-rejected invalid OEQ resolution before projection can erase it", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:mislabelled", kind: "theorem", statement: "not actually an OEQ",
      depends_on: [], status: "to-prove",
      justification: "regression witness", gap: "none", consumer: "test",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const isMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `QED ${target.id}.` })),
          resolved_oeqs: isMain ? [{
            source_id: "oeq:mislabelled",
            theorem: {
              id: "thm:mislabelled-answer", kind: "theorem", statement: "an invalid sibling answer",
              depends_on: [], status: "proved", proof_tex: "Invalid answer proof.",
            },
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.invalid_resolutions).toEqual(["oeq:mislabelled→thm:mislabelled-answer"]);
    expect(withheld.capability_emissions).toContain("oeq-resolution:oeq:mislabelled@thm:main");
  });

  it("checkpoints when a WITHHELD helper collision is the round's only defect", async () => {
    // Regression for a bug introduced BY a fix. Every withheld-content collector must
    // appear in the checkpoint guard, not only the proposal lists. The guard was widened
    // once for cross-unit conflicts; the added-helper and OEQ-answer collectors added
    // afterwards were pushed into the message but NOT into the condition -- so a round
    // whose ONLY defect was a withheld helper skipped the checkpoint and advanced
    // silently, presenting a proved-looking core. Removing the collectors from that
    // condition must fail here.
    const ctx = makeCtx(repoRoot);

    // Round 1: establish lem:shared with claim A, proved.
    const emit = (statement: string): StageDeps => ({
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: `By lem:shared, ${t.id} follows.` })),
          added_lemmas: [{
            id: "lem:shared", kind: "lemma", statement, depends_on: [],
            status: "proved", proof_tex: "Proof of the helper.",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    });

    await runStage0Solve({ ctx, state: makeState(), deps: emit("claim A") });

    // Round 2: re-emit the SAME id with a DIFFERENT claim, and nothing else. The helper is
    // withheld; no proposal of any other kind exists.
    await appendEscalationLog(ctx, { round: 2, changed: [], directive: "re-derive the targets" });
    const result = await runStage0Solve({ ctx, state: makeState(), deps: emit("claim B — incompatible") });

    expect(result, "a withheld helper must checkpoint on its own").toHaveProperty("status", "checkpoint");
    expect(String((result as { message?: string }).message ?? "")).toMatch(/lem:shared/);
  });

  it("halts when a proof names a nonexistent id on an otherwise COMPLETE round", async () => {
    // Class sweep: `unmatchedProofIds` was surfaced only inside the incomplete-round
    // checkpoint, so a round that discharged every target AND emitted a proof under an id
    // present in no core store completed clean with the drop invisible. That is the silent
    // id-mapping drop the project's debugging rule names: what the agent EMITTED must be
    // reconciled against what was PERSISTED.
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((t) => ({ id: t.id, proof_tex: `QED ${t.id}.` })),
            { id: "lem:does-not-exist", proof_tex: "a proof for nothing" },
          ],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result, "a dropped proof must halt even on a complete round").toHaveProperty("status", "checkpoint");
    expect(String((result as { message?: string }).message ?? "")).toMatch(/lem:does-not-exist/);
  });

  it("routes a shared cited comparator and symbol edit to one canonical directive owner", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "add the shared comparator and correct the paper-wide target symbol once",
      require_core_changes: true,
      required_core_targets: ["lem:shared-comparator", "sym:tau", "sym:t_pi"],
    });
    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        prompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({
            id: target.id,
            proof_tex: owner ? "QED." : "By `lem:shared-comparator`, QED.",
          })),
          added_lemmas: owner ? [{
            id: "lem:shared-comparator",
            kind: "lemma",
            statement: "The external comparator studies a distinct regime.",
            depends_on: [],
            status: "cited",
            source: {
              cite: "SharedComparator2026",
              locator: "Theorem 1",
              verbatim_statement: "A distinct comparison regime.",
            },
          }] : [],
          proposed_core_edits: owner ? [
            {
              kind: "symbol-replace",
              name: "tau",
              proposed: {
                name: "tau",
                type: "causal_parameter",
                def: "the corrected shared causal estimand",
              },
              reason: "one paper-wide symbol definition is required",
              direction: "correct",
            },
            {
              kind: "symbol-add",
              name: "t_pi",
              proposed: {
                name: "t_pi",
                type: "positive constant",
                role: "propensity smoothness",
              },
              reason: "declare a new paper-wide constant",
              direction: "correct",
            },
          ] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    expect(prompts).toHaveLength(1);
    const ownerPrompts = prompts.filter((prompt) =>
      prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads")
    );
    expect(ownerPrompts).toHaveLength(1);
    expect(prompts[0]).toBe(ownerPrompts[0]);
    // Equal-size components prefer the headline theorem, not dispatch/Promise
    // completion order, as the deterministic integration point.
    expect(ownerPrompts[0]).toContain('"id": "thm:main"');

    const edits = (await readSurfacedProposals(ctx)).coreEdits;
    expect(edits).toEqual(expect.arrayContaining([
      expect.objectContaining({ kind: "symbol-replace", name: "tau" }),
      expect.objectContaining({ kind: "symbol-add", name: "t_pi" }),
    ]));
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.filter((statement: any) => statement.id === "lem:shared-comparator"))
      .toEqual([expect.objectContaining({
        status: "cited",
        source: expect.objectContaining({ cite: "SharedComparator2026" }),
      })]);
  });

  const singletonCapabilityCases: Array<{
    name: string;
    diagnostic: string;
    required?: string;
    build: (marker: string) => Record<string, unknown>;
    artifact: (ctx: PipelineContext) => string;
  }> = [
    ...([
      {
        name: "symbol catalog edit",
        diagnostic: "core-edit.*sym:tau",
        edit: (marker: string) => ({
          kind: "symbol-replace", name: "tau",
          proposed: { ...PROTO.symbols[0], role: `${marker} symbol` },
          reason: `${marker} symbol repair`, direction: "correct",
        }),
      },
      {
        name: "definition catalog edit",
        diagnostic: "core-edit.*def:env",
        edit: (marker: string) => ({
          kind: "definition-replace", id: "def:env",
          proposed: { ...PROTO.definitions[0], construction: `${marker} envelope`, free_symbols: [] },
          reason: `${marker} definition repair`, direction: "correct",
        }),
      },
      {
        name: "bibliography catalog edit",
        diagnostic: "core-edit.*bib:Rosenbaum1983",
        edit: (marker: string) => ({
          kind: "bibliography-replace", key: "Rosenbaum1983",
          proposed: { key: "Rosenbaum1983", citation: `${marker} citation` },
          reason: `${marker} bibliography repair`, direction: "correct",
        }),
      },
    ] as const).map(({ name, diagnostic, edit }) => ({
      name,
      diagnostic,
      build: (marker: string) => name === "definition catalog edit"
        ? {
            proposed_definition_changes: [{
              id: "def:env", current: "U = a", proposed: `${marker} envelope`,
              reason: `${marker} definition repair`, direction: "correct",
            }],
            proposed_core_edits: [edit(marker)],
          }
        : { proposed_core_edits: [edit(marker)] },
      artifact: workingPath,
    })),
    {
      name: "proposed definition change",
      diagnostic: "definition-change.*def:env",
      build: (marker: string) => ({ proposed_definition_changes: [{
        id: "def:env", current: "U = a", proposed: `${marker} U`,
        reason: `${marker} correction`, direction: "correct",
      }] }),
      artifact: workingPath,
    },
    {
      name: "proposed assumption",
      diagnostic: "assumption.*ass:new-condition",
      build: (marker: string) => ({ proposed_assumptions: [{
        id: "ass:new-condition", condition: `${marker} condition`, reason: `${marker} reason`,
        standard_or_novel: "novel: test", not_crux: "separate regularity condition",
      }] }),
      artifact: workingPath,
    },
    {
      name: "new exact required node",
      diagnostic: "added-node.*lem:required-singleton",
      required: "lem:required-singleton",
      build: (marker: string) => ({ added_lemmas: [{
        id: "lem:required-singleton", kind: "lemma", statement: `${marker} required statement`,
        depends_on: [], status: "proved", proof_tex: `${marker} proof`,
      }] }),
      artifact: coreJsonPath,
    },
    {
      name: "paper-wide prose update",
      diagnostic: "prose-updates.*prose:paper-wide",
      build: (marker: string) => ({ prose_updates: { tldr: `${marker} prose`, statement_notes: [] } }),
      artifact: coreJsonPath,
    },
  ];

  it.each(singletonCapabilityCases)(
    "routes $name through the directive-wide capability owner",
    async ({ required, build, artifact }) => {
      const ctx = makeCtx(repoRoot);
      await appendEscalationLog(ctx, {
        round: 1,
        changed: [],
        directive: "exercise the centralized singleton write-capability matrix",
        ...(required ? { require_core_changes: true, required_core_targets: [required] } : {}),
      });
      const deps: StageDeps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
          const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
          const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
          const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
          await writeFile(outPath, JSON.stringify(withCorrectionPairs({
            proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof of ${id}.` })),
            ...build(owner ? "OWNER" : "SIBLING"),
          })), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      };

      let calls = 0;
      const originalRunCodex = deps.runCodex;
      deps.runCodex = async (input: any) => {
        calls += 1;
        return originalRunCodex(input);
      };
      await runStage0Solve({ ctx, state: makeState(), deps });
      expect(calls).toBe(required ? 1 : 2);
      const canonical = await readFile(artifact(ctx), "utf8");
      expect(canonical).toContain("OWNER");
      expect(canonical).not.toContain("SIBLING");
    },
  );

  // Downstream is not paid until the staged owner's postimage has been accepted.
  it("defers downstream for a global exact catalog target", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the shared symbol through the directive-wide owner",
      require_core_changes: true,
      required_core_targets: ["sym:tau"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
          proposed_core_edits: owner ? [{
            kind: "symbol-replace", name: "tau",
            proposed: { ...PROTO.symbols[0], role: "authorized staged symbol repair" },
            reason: "the shared owner performs the exact repair", direction: "correct",
          }] : [{
            kind: "symbol-replace", name: "tau",
            proposed: { ...PROTO.symbols[0], role: "unauthorized-only symbol repair" },
            reason: "sibling attempted the only exact emission", direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    let calls = 0;
    const originalRunCodex = deps.runCodex;
    deps.runCodex = async (input: any) => {
      calls += 1;
      return originalRunCodex(input);
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls).toBe(1);
    expect(result).toHaveProperty("status", "checkpoint");
    const surfaced = JSON.stringify(await readSurfacedProposals(ctx));
    expect(surfaced).toContain("authorized staged symbol repair");
    expect(surfaced).not.toContain("unauthorized-only symbol repair");
    // The round reached a committed checkpoint, so its reuse receipts are consumed:
    // nothing from this round can be replayed into the next dispatch.
    expect(existsSync(solveReuseReceiptsDir(ctx))).toBe(false);
  });

  // An exact-target directive pays only for the components it names; an
  // unrelated open component is deferred to an undirected round instead of
  // being blindly re-solved (and re-paid) alongside every repair.
  it("defers unrelated open components on an exact-target directive", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "re-prove thm:main exactly",
      required_core_targets: ["thm:main"],
    });
    const dispatchedUnits: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        dispatchedUnits.push(/TARGET STATEMENT\(S\) TO SOLVE \(unit: ([^)]+)\)/.exec(prompt)![1]);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(warn.mock.calls.flat().join("\n")).toMatch(/deferring unrelated open component/i);
    warn.mockRestore();
    expect(dispatchedUnits).toEqual(["thm:main"]);
  });

  // A merge/gate fatal lands AFTER every unit is paid for. A resume with an
  // unchanged directive used to clear the outputs and re-pay every model call just
  // to reach the same deterministic error (observed back-to-back: exp_mixed
  // 2026-08-09 19:26→19:32, stat_transport 2026-08-30 15:51→16:00). The reuse lane
  // binds each validated output to its exact prompt; an unchanged resume replays
  // the persisted outputs with zero model calls.
  it("reuses persisted unit outputs on an unchanged resume after an uncommitted fatal", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "prove everything and also emit the missing frontier node",
      require_core_changes: true,
      required_core_targets: ["thm:never-emitted"],
    });
    let codexCalls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        codexCalls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(/thm:never-emitted/);
    const paidCalls = codexCalls;
    expect(paidCalls).toBeGreaterThan(0);
    expect(existsSync(solveReuseReceiptsDir(ctx))).toBe(true);

    const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(/thm:never-emitted/);
    expect(warn.mock.calls.flat().join("\n")).toMatch(/reusing the persisted validated output/i);
    warn.mockRestore();
    expect(codexCalls).toBe(paidCalls);
  });

  // Supersedes an earlier contract that REJECTED two reverse-dependency rebuilds whose
  // `reason` prose differed. That aborted a real D0 round (stat_pn_weak_event_honest_inference
  // round 36, ~1.4h of solving discarded) even though the operation is a parameterless,
  // idempotent recomputation of `used_by`: `kind`/`id`/`direction` are schema literals, so
  // two rebuilds can only ever differ in human-readable rationale. Two LLM units will
  // essentially never word that identically, making the old contract a guaranteed
  // round-killer rather than a defect detector. Edits that carry a real payload are still
  // compared in full — see the `prop:aux` conflict test below.
  it("dedupes idempotent reverse-dependency rebuilds that differ only in rationale", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "rebuild reverse dependencies exactly once",
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
          proposed_core_edits: owner ? [{
            kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
            reason: "first owner rebuild", direction: "correct",
          }, {
            kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
            reason: "second incompatible owner rebuild", direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    // The round survives the rationale mismatch, and the derived-metadata request is
    // normalized away instead of buying an adjudication checkpoint.
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result ? result.status : undefined).toBeUndefined();
    expect(result.message).not.toMatch(/rebuild-reverse-dependencies/i);
    expect((await readSurfacedProposals(ctx)).coreEdits).toEqual([]);
  });

  // Solvers re-emit a statement-replace that ECHOES the node wholesale (statement,
  // kind, deps, source all unchanged; status echoed `to-prove` while the same round
  // supplies the proof through the proofs channel). One run logged 40 such from≡to
  // entries — each one a checkpoint + adjudication + apply + re-solve cycle that
  // changed nothing. The echo must be dropped as a no-op; the proof must still land.
  it("drops a wholesale statement-replace echo instead of checkpointing on it", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "confirm the dependency wiring of thm:main",
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
          proposed_core_edits: owner && targets.some(({ id }) => id === "thm:main") ? [{
            kind: "statement-replace", id: "thm:main",
            proposed: {
              id: "thm:main", kind: "theorem", statement: "tau is identified",
              depends_on: ["ass:overlap"], status: "to-prove",
              justification: "core ID", gap: "vs prior", consumer: "applied",
            },
            reason: "confirming wiring as directed", direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    // No proposal checkpoint: the echo is a no-op, and both targets are proved.
    expect(result.message).not.toMatch(/statement-replace/i);
    const surfaced = await readSurfacedProposals(ctx);
    expect((surfaced.coreEdits ?? []).filter((e: { kind?: string }) => e.kind === "statement-replace")).toEqual([]);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const main = core.statements.find((s: { id: string }) => s.id === "thm:main");
    expect(main.status, "the same-round proof must still land").toBe("proved");
  });

  it("keeps TeX-comment whitespace claim changes exact and their proof provisional", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].statement = "A % comment\nand B";
    const proposed = "A % comment and B";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the TeX-sensitive claim bytes exactly",
      require_core_changes: true,
      required_core_targets: ["thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({
            id,
            proof_tex: `Proof of ${id}.`,
            ...(id === "thm:main" ? { argues_proposed: true } : {}),
          })),
          proposed_statement_changes: ownsMain ? [{
            id: "thm:main", current: proto.statements[0].statement, proposed,
            reason: "the newline changes TeX comment scope", direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...proto.statements[0], statement: proposed, free_symbols: [] },
            reason: "preserve the exact post-image", direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.proposals.statements).toContainEqual(expect.objectContaining({ id: "thm:main", proposed }));
    expect(working.proposals.proofs).toContainEqual(expect.objectContaining({ id: "thm:main", argues_proposed: true }));
    expect(working.solved["thm:main"]).toMatchObject({ partial: true });
    const changed = await applyProposedChanges({ ctx, note: "accept exact TeX-sensitive correction" });
    expect(changed).toContainEqual(expect.objectContaining({ id: "thm:main", kind: "statement" }));
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.statements.find((statement: any) => statement.id === "thm:main").statement).toBe(proposed);
    const appliedWorking = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(appliedWorking.solved["thm:main"]).toMatchObject({ proof_tex: "Proof of thm:main." });
    expect(appliedWorking.solved["thm:main"].partial).not.toBe(true);
  });

  it("selects the same directive owner when dispatch order is reversed", () => {
    const units = [
      { label: "thm:zeta", targets: [{ id: "thm:zeta" }] },
      { label: "prop:alpha", targets: [{ id: "prop:alpha" }] },
      { label: "thm:broad", targets: [{ id: "lem:a" }, { id: "thm:broad" }] },
    ];
    expect(selectDirectiveEmissionOwnerLabel(units)).toBe("thm:broad");
    expect(selectDirectiveEmissionOwnerLabel([...units].reverse())).toBe("thm:broad");
    const tied = units.slice(0, 2);
    expect(selectDirectiveEmissionOwnerLabel(tied)).toBe("thm:zeta");
    expect(selectDirectiveEmissionOwnerLabel([...tied].reverse())).toBe("thm:zeta");

    const semantic = selectSemanticTargetOwners(units);
    const reversedSemantic = selectSemanticTargetOwners([...units].reverse());
    expect(Object.fromEntries(semantic)).toEqual({
      "lem:a": "thm:broad",
      "prop:alpha": "prop:alpha",
      "thm:broad": "thm:broad",
      "thm:zeta": "thm:zeta",
    });
    expect(Object.fromEntries(reversedSemantic)).toEqual(Object.fromEntries(semantic));
    expect(Object.fromEntries(selectSemanticTargetOwners([
      { label: "thm:first", targets: [{ id: "lem:shared" }] },
      { label: "thm:second", targets: [{ id: "lem:shared" }] },
    ]))).toEqual({});
  });

  it("quarantines every carrier for a target duplicated across dispatch labels", () => {
    const dispatch = [
      { label: "thm:first", targets: [{ id: "lem:shared" } as any], priorContext: "" },
      { label: "thm:second", targets: [{ id: "lem:shared" } as any], priorContext: "" },
    ];
    const outputs = ["first", "second"].map((name) => SolveUnitOutputSchema.parse({
      proofs: [{ id: "lem:shared", proof_tex: `${name} proof` }],
      open_obligations: [{
        node_id: "lem:shared", what_is_open: `${name} residual`,
        obstruction: "contested ownership", attempted: "local proof",
      }],
    }));
    const result = projectOutputsToWriteCapabilities({
      outputs,
      dispatch,
      semanticTargetOwners: selectSemanticTargetOwners(dispatch),
      directiveOwnerLabel: "thm:first",
      requiredCoreTargets: new Set(["lem:shared"]),
      existingStatementIds: new Set(["lem:shared"]),
    });
    expect(result.outputs.every((output) =>
      output.proofs.length === 0 && output.open_obligations.length === 0
    )).toBe(true);
    expect(result.quarantined.filter((receipt) => receipt.target === "lem:shared")).toHaveLength(4);
    expect(result.quarantined.every((receipt) => receipt.owner === "(contested dispatch ownership)")).toBe(true);
  });

  it("gives an existing shared statement to its own semantic solve unit, not the cross-cutting owner", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = {
      ...PROTO,
      statements: [
        {
          id: "thm:gaussian-frontier", kind: "theorem", statement: "The Gaussian frontier holds.",
          depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
        {
          id: "prop:regular-reduction", kind: "proposition", statement: "The regular reduction holds.",
          depends_on: ["def:learners"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
      ],
      definitions: [...PROTO.definitions, {
        id: "def:learners", name: "learners", construction: "shared learner map", inputs: [],
      }],
    };
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the Gaussian frontier and regular reduction consistently",
      require_core_changes: true,
      required_core_targets: ["thm:gaussian-frontier", "prop:regular-reduction"],
    });
    const prompts = new Map<string, string>();
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const target = targets[0].id;
        prompts.set(target, prompt);
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof of ${id}.` })),
          proposed_core_edits: target === "prop:regular-reduction" ? [{
            kind: "statement-replace",
            id: "prop:regular-reduction",
            proposed: {
              ...proto.statements[1],
              depends_on: ["ass:overlap", "def:learners"],
            },
            reason: "the regular score uses overlap directly",
            direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    expect(prompts.get("thm:gaussian-frontier")).toContain(
      "prop:regular-reduction -> semantic owner prop:regular-reduction",
    );
    expect(prompts.get("thm:gaussian-frontier")).toContain(
      "does NOT authorize you to prove, replace, edit, or re-emit",
    );
    expect(prompts.get("prop:regular-reduction")).toContain(
      "Statement target ids semantically owned by YOUR unit: prop:regular-reduction",
    );
    const edits = (await readSurfacedProposals(ctx)).coreEdits;
    expect(edits).toEqual([expect.objectContaining({
      kind: "statement-replace",
      id: "prop:regular-reduction",
      proposed: expect.objectContaining({ depends_on: ["ass:overlap", "def:learners"] }),
    })]);
  });

  it("quarantines an incompatible sibling edit when the semantic owner emitted the target", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = {
      ...PROTO,
      definitions: [...PROTO.definitions, {
        id: "def:learners", name: "learners", construction: "combined learner", inputs: [],
      }, {
        id: "def:pn-learners", name: "PN learners", construction: "PN learner", inputs: [],
      }, {
        id: "def:ps-learners", name: "PS learners", construction: "PS learner", inputs: [],
      }],
      statements: [
        {
          id: "thm:gaussian-frontier", kind: "theorem", statement: "The Gaussian frontier holds.",
          depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
        {
          id: "prop:regular-reduction", kind: "proposition", statement: "The regular reduction holds.",
          depends_on: ["def:learners"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
      ],
    };
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair both targets while retaining fail-closed collision detection",
      require_core_changes: true,
      required_core_targets: ["thm:gaussian-frontier", "prop:regular-reduction"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const localOwner = targets.some(({ id }) => id === "prop:regular-reduction");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof of ${id}.` })),
          proposed_core_edits: [{
            kind: "statement-replace",
            id: "prop:regular-reduction",
            proposed: {
              ...proto.statements[1],
              depends_on: localOwner
                ? ["ass:overlap", "def:learners"]
                : ["def:pn-learners", "def:ps-learners"],
            },
            reason: localOwner ? "retain combined learners" : "split learners by direction",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
    try {
      const result = await runStage0Solve({ ctx, state: makeState(), deps });
      expect(result).toHaveProperty("status", "checkpoint");
      expect(warn).toHaveBeenCalledWith(expect.stringMatching(
        /quarantined unauthorized core-edit.*prop:regular-reduction.*thm:gaussian-frontier.*capability owner.*prop:regular-reduction/i,
      ));
    } finally {
      warn.mockRestore();
    }
    const edits = (await readSurfacedProposals(ctx)).coreEdits;
    expect(edits).toEqual([expect.objectContaining({
      id: "prop:regular-reduction",
      proposed: expect.objectContaining({ depends_on: ["ass:overlap", "def:learners"] }),
    })]);
  });

  it("projects a forbidden frontier edit of lower-owned lf-membership regardless of completion order", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = {
      ...PROTO,
      statements: [
        {
          id: "lem:lf-membership", kind: "lemma", statement: "The LF witness belongs to the shell.",
          depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
        {
          id: "conj:gaussian-lower", kind: "conjecture", statement: "The Gaussian lower bound holds.",
          depends_on: ["lem:lf-membership"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
        {
          id: "lem:frontier-a", kind: "lemma", statement: "Frontier input A.",
          depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
        {
          id: "lem:frontier-b", kind: "lemma", statement: "Frontier input B.",
          depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
        {
          id: "thm:gaussian-frontier", kind: "theorem", statement: "The Gaussian frontier holds.",
          depends_on: ["lem:frontier-a", "lem:frontier-b"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
        },
      ],
    };
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "split upper and LF schedules without cross-writing lower membership",
      require_core_changes: true,
      required_core_targets: ["lem:lf-membership", "conj:gaussian-lower", "thm:gaussian-frontier"],
    });
    const completionOrder: string[] = [];
    const prompts = new Map<string, string>();
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const lowerOwner = targets.some(({ id }) => id === "lem:lf-membership");
        const label = lowerOwner ? "conj:gaussian-lower" : "thm:gaussian-frontier";
        prompts.set(label, prompt);
        if (lowerOwner) await new Promise((resolve) => setTimeout(resolve, 25));
        const ownerReplacement = {
          ...proto.statements[0],
          statement: "The LF witness belongs along the capped LF schedule.",
          depends_on: ["ass:overlap", "def:lf-admissible-schedules"],
          free_symbols: [],
        };
        const siblingReplacement = {
          ...proto.statements[0],
          depends_on: ["ass:overlap", "def:upper-schedule", "def:lf-admissible-schedules"],
          free_symbols: [],
        };
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets
            .filter(({ id }) => id !== "lem:lf-membership")
            .map(({ id }) => ({ id, proof_tex: `Proof of ${id}.` })),
          proposed_statement_changes: lowerOwner ? [{
            id: "lem:lf-membership",
            current: proto.statements[0].statement,
            proposed: ownerReplacement.statement,
            reason: "restrict to the LF schedule",
            direction: "narrow",
          }] : [],
          proposed_core_edits: [{
            kind: "statement-replace",
            id: "lem:lf-membership",
            proposed: lowerOwner ? ownerReplacement : siblingReplacement,
            reason: lowerOwner ? "canonical lower-owner repair" : "forbidden frontier dependency repair",
            direction: "correct",
          }],
        })), "utf8");
        completionOrder.push(label);
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
    try {
      const result = await runStage0Solve({ ctx, state: makeState(), deps });
      expect(result).toHaveProperty("status", "checkpoint");
      expect(completionOrder).toEqual(["thm:gaussian-frontier", "conj:gaussian-lower"]);
      expect(prompts.get("thm:gaussian-frontier")).toContain(
        "lem:lf-membership -> semantic owner conj:gaussian-lower",
      );
      expect(warn).toHaveBeenCalledWith(expect.stringMatching(
        /quarantined unauthorized core-edit.*lem:lf-membership.*thm:gaussian-frontier.*conj:gaussian-lower/i,
      ));
    } finally {
      warn.mockRestore();
    }
    const edits = (await readSurfacedProposals(ctx)).coreEdits;
    expect(edits).toEqual([expect.objectContaining({
      id: "lem:lf-membership",
      proposed: expect.objectContaining({
        statement: "The LF witness belongs along the capped LF schedule.",
        depends_on: ["ass:overlap", "def:lf-admissible-schedules"],
      }),
    })]);
  });

  it("checkpoints when an exact statement target has only an unauthorized sibling payload", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair prop:aux through its semantic owner",
      require_core_changes: true,
      // thm:main is named too so BOTH components dispatch: exact-target scoping
      // now defers unrelated open components, and this scenario needs the
      // sibling unit alive to attempt the cross-component interference.
      required_core_targets: ["prop:aux", "thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsProp = targets.some(({ id }) => id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: ownsProp ? [] : targets.map(({ id }) => ({ id, proof_tex: "QED." })),
          proposed_core_edits: ownsProp ? [] : [{
            kind: "statement-replace",
            id: "prop:aux",
            proposed: {
              ...PROTO.statements[1],
              depends_on: ["ass:overlap", "def:env"],
            },
            reason: "unauthorized sibling-only repair",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.capability_emissions).toContain("core-edit:prop:aux@thm:main");
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: "core-edit", target: "prop:aux", unit: "thm:main",
        payload: expect.objectContaining({ kind: "statement-replace", id: "prop:aux" }),
      }),
    ]));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.escalation_entries_consumed).toBe(0);
  });

  it("does not let a no-op owner correction mask a sibling's exact claim correction", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair prop:aux through its semantic owner",
      require_core_changes: true,
      // thm:main is named too so BOTH components dispatch: exact-target scoping
      // now defers unrelated open components, and this scenario needs the
      // sibling unit alive to attempt the cross-component interference.
      required_core_targets: ["prop:aux", "thm:main"],
    });
    const current = PROTO.statements[1];
    const proposed = `${current.statement} on the narrowed domain`;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsProp = targets.some(({ id }) => id === "prop:aux");
        const statement = ownsProp ? current.statement : proposed;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof of ${id}.` })),
          proposed_statement_changes: [{
            id: "prop:aux", current: current.statement, proposed: statement,
            reason: ownsProp ? "stale no-op owner echo" : "genuine sibling correction",
            direction: "narrow",
          }],
          proposed_core_edits: [{
            kind: "statement-replace", id: "prop:aux",
            proposed: { ...current, statement, free_symbols: [] },
            reason: ownsProp ? "stale no-op owner replacement" : "genuine sibling replacement",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.capability_emissions).toEqual(expect.arrayContaining([
      "statement-change:prop:aux@thm:main",
      "core-edit:prop:aux@thm:main",
    ]));
  });

  it("accepts a claim-only owner correction while quarantining sibling correction noise", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair prop:aux through its semantic owner",
      require_core_changes: true,
      required_core_targets: ["prop:aux"],
    });
    const current = PROTO.statements[1];
    const ownerClaim = `${current.statement} on the owner-certified domain`;
    const siblingClaim = `${current.statement} on an incompatible sibling domain`;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsProp = targets.some(({ id }) => id === "prop:aux");
        const statement = ownsProp ? ownerClaim : siblingClaim;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({
            id, proof_tex: `Proof of ${id}.`,
            ...(id === "prop:aux" ? { argues_proposed: true } : {}),
          })),
          proposed_statement_changes: [{
            id: "prop:aux", current: current.statement, proposed: statement,
            reason: ownsProp ? "owner claim correction" : "sibling correction noise",
            direction: "narrow",
          }],
          proposed_core_edits: [{
            kind: "statement-replace", id: "prop:aux",
            proposed: { ...current, statement, status: "to-prove", free_symbols: [] },
            reason: ownsProp ? "owner claim replacement" : "sibling replacement noise",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.statements).toContainEqual(expect.objectContaining({
      id: "prop:aux", proposed: ownerClaim,
    }));
    expect(JSON.stringify(surfaced)).not.toContain(siblingClaim);
  });

  it("still rejects incompatible duplicate edits emitted inside the authorized owner's own output", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = { ...PROTO, statements: [PROTO.statements[1]] };
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the proposition once",
      require_core_changes: true,
      required_core_targets: ["prop:aux"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "prop:aux", proof_tex: "QED." }],
          proposed_core_edits: [{
            kind: "statement-replace", id: "prop:aux",
            proposed: { ...PROTO.statements[1], depends_on: ["ass:overlap"] },
            reason: "first incompatible owner payload", direction: "correct",
          }, {
            kind: "statement-replace", id: "prop:aux",
            proposed: { ...PROTO.statements[1], depends_on: ["def:env"] },
            reason: "second incompatible owner payload", direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /conflicting duplicate core-edit payloads for prop:aux/i,
    );
  });

  it("fails closed when a structured-core directive produces no structured proposal", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "replace the stale formal assumption node",
      require_core_changes: true,
    });
    const c = countingDeps();
    await expect(runStage0Solve({ ctx, state: makeState(), deps: c.deps })).rejects.toThrow(
      /STRUCTURED CORE CHANGES REQUIRED.*no proposed changes/i,
    );
  });

  it("allows a later auditable directive to retire a mistaken bare structured-core guard", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair what was initially believed to be a frozen-core defect",
      require_core_changes: true,
    });
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "review determined the repair is prose-only",
      cancel_require_core_changes: true,
    });
    const c = countingDeps();
    await expect(runStage0Solve({ ctx, state: makeState(), deps: c.deps })).resolves.toBeDefined();
  });

  it("allows a later auditable directive to retire a required target that normalizes to a no-op", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the theorem and rebuild already-correct reverse edges",
      require_core_changes: true,
      required_core_targets: ["thm:main", "metadata:reverse-dependencies"],
    });
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "review confirmed reverse edges are already exact; retain the theorem repair",
      cancelled_core_targets: ["metadata:reverse-dependencies"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        const body = ownsMain ? withCorrectionPairs({
          proofs: [{ id: "thm:main", proof_tex: "QED.", argues_proposed: true }],
          proposed_statement_changes: [{
            id: "thm:main",
            current: PROTO.statements[0].statement,
            proposed: `${PROTO.statements[0].statement} Sharpened.`,
            reason: "substantive theorem repair",
            direction: "narrow",
          }],
        }) : { proofs: targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })) };
        await writeFile(outPath, JSON.stringify(body), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStage0Solve({ ctx, state: makeState(), deps })).resolves.toBeDefined();
  });

  it("does not let an unrelated structured edit satisfy an exact required target", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "replace the stale length symbol",
      require_core_changes: true,
      required_core_targets: ["sym:len"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: "QED." })),
          proposed_core_edits: [{
            kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
            reason: "unrelated", direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /required exact structured target.*sym:len.*unrelated proposals cannot satisfy/i,
    );
  });

  it("keeps forced targets out of established context and defers only proofs affected by an edit", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].depends_on = ["ass:overlap", "prop:aux"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");

    await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") });
    await appendEscalationLog(ctx, {
      round: 2,
      changed: [],
      directive: "repair both proofs and declare the main theorem's envelope dependency",
      require_core_changes: true,
      required_core_targets: ["prop:aux", "thm:main"],
    });

    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        prompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `REPAIRED ${target.id}` })),
          added_lemmas: [{
            id: "lem:independent-certificate", kind: "lemma",
            statement: "An independent certificate holds.",
            depends_on: ["ass:overlap"], status: "proved",
            proof_tex: "Independent certificate proof.",
          }],
          proposed_core_edits: [{
            kind: "statement-replace",
            id: "thm:main",
            proposed: {
              ...proto.statements[0],
              depends_on: ["ass:overlap", "prop:aux", "def:env"],
            },
            reason: "declare the proof's envelope dependency",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    expect(result.artifacts).toEqual(expect.arrayContaining([
      expect.stringMatching(/d0_working\.json$/),
      expect.stringMatching(/proposal_review_packet\.json$/),
    ]));

    const prompt = prompts.join("\n");
    const established = prompt.includes("=== ALREADY-ESTABLISHED")
      ? prompt.split("=== ALREADY-ESTABLISHED")[1].split("=== PRIOR PROOF OF A DIRECTED TARGET")[0]
      : "";
    expect(established).not.toContain("prop:aux");
    expect(prompt).toContain("=== PRIOR PROOF OF A DIRECTED TARGET");
    expect(prompt).toContain("- prop:aux: QED.");

    // The statement-replace only GROWS thm:main's dependency set (adds def:env, whose
    // construction is unchanged). Dependency bookkeeping with all referenced content
    // intact no longer invalidates the same-round proof — it lands immediately instead
    // of becoming partial debt pending adjudication (a rejected edit still invalidates
    // through the apply-side rejection path, and auto-wiring re-adds cited deps anyway).
    const deferred = (await readSurfacedProposals(ctx)).proofs;
    expect(deferred).toEqual([]);
    const packet = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "proposal_review_packet.json"),
      "utf8",
    ));
    expect(packet.full_current_paper_tex).toContain("tau is identified");
    expect(packet.proposed_core_edits).toHaveLength(1);
    expect(packet.provisional_proofs).toEqual(deferred);
    expect(packet.durable_working_state.solved["prop:aux"]).toMatchObject({
      proof_tex: "REPAIRED prop:aux",
    });
    expect(packet.durable_working_state.solved["prop:aux"].partial).toBeUndefined();
    expect(packet.durable_working_state.solved["lem:independent-certificate"]).toMatchObject({
      proof_tex: "Independent certificate proof.",
      node: { status: "proved" },
    });
    expect(packet.durable_working_state.solved["lem:independent-certificate"].partial).toBeUndefined();
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["prop:aux"]).toMatchObject({ proof_tex: "REPAIRED prop:aux" });
    expect(working.solved["prop:aux"].partial).toBeUndefined();
    expect(working.solved["lem:independent-certificate"].partial).toBeUndefined();
    expect(working.solved["thm:main"]).toMatchObject({ proof_tex: "REPAIRED thm:main" });
    expect(working.solved["thm:main"].partial, "dep-growth-only edit must not defer the proof").toBeUndefined();
  });

  it("credits a resolved OEQ source and a cited comparator as their exact directed targets", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = {
      ...PROTO,
      statements: [{
        id: "oeq:sharp-learning-boundary",
        kind: "openendedquestion",
        statement: "What is the sharp learning boundary?",
        depends_on: ["ass:overlap"],
        status: "to-prove",
        justification: "resolve the boundary",
        gap: "open in the proposal",
        consumer: "headline",
      }],
    };
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "replace the OEQ with its answer and add the exact comparator",
      require_core_changes: true,
      required_core_targets: [
        "oeq:sharp-learning-boundary",
        "lem:cheng-mao-pearl-li-2026-comparator",
      ],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [],
          resolved_oeqs: [{
            source_id: "oeq:sharp-learning-boundary",
            theorem: {
              id: "thm:learning-boundary-is-indexing-not-necessity",
              kind: "theorem",
              statement: "The boundary indexes this learner rather than a universal necessity claim.",
              depends_on: ["ass:overlap"],
              status: "proved",
              proof_tex: "Direct argument.",
            },
          }],
          added_lemmas: [{
            id: "lem:cheng-mao-pearl-li-2026-comparator",
            kind: "lemma",
            statement: "The comparator studies a distinct regular regime.",
            depends_on: [],
            status: "cited",
            source: {
              cite: "Rosenbaum1983",
              locator: "Section 1",
              verbatim_statement: "A distinct regular regime.",
            },
          }],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
          proposed_assumptions: [],
          // Adversarial reason drift must not create a second copy or replace the
          // orchestrator's canonical operation.
          proposed_core_edits: [{
            kind: "statement-delete",
            id: "thm:main",
            replacement_id: "prop:aux",
            reason: "worker supplied a different rationale",
            direction: "delete-obsolete",
          }],
          open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.some((s: any) => s.id === "oeq:sharp-learning-boundary")).toBe(false);
    expect(core.statements.find((s: any) => s.id === "thm:learning-boundary-is-indexing-not-necessity"))
      .toMatchObject({ status: "proved" });
    expect(core.statements.find((s: any) => s.id === "lem:cheng-mao-pearl-li-2026-comparator"))
      .toMatchObject({ status: "cited", source: { cite: "Rosenbaum1983" } });
  });

  it("persists an auto-healed bibliography key used by a cited solver-added node", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const target = outPath.includes("prop_aux") ? "prop:aux" : "thm:main";
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: target, proof_tex: "QED." }],
          added_lemmas: target === "thm:main" ? [{
            id: "lem:new-cited-source",
            kind: "lemma",
            statement: "A newly cited external fact.",
            depends_on: [],
            status: "cited",
            source: {
              cite: "NewSource2026",
              locator: "Theorem 1",
              verbatim_statement: "The external fact.",
            },
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const persisted = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(persisted.bibliography).toContainEqual({ key: "NewSource2026" });
  });

  it("re-opens an exact required agent-added target held as a checkpoint partial", async () => {
    // Phase 1 (store consolidation): a proposal checkpoint records every
    // checkpoint-withheld agent node into the WORKING STATE as a partial (the
    // cursor is the durable catalog), and the old recovery that re-read the
    // prior published core.json as truth is deleted. This test seeds exactly
    // the record `surfaceProposalCheckpoint` writes and requires the next
    // directed round to re-open it as a dispatchable target.
    const ctx = makeCtx(repoRoot);
    const required = {
      id: "thm:agent-result",
      kind: "theorem",
      statement: "The agent result holds.",
      depends_on: ["ass:overlap"],
      status: "to-prove",
      justification: "agent-added result",
      gap: "not frozen in the proposal",
      consumer: "main theorem",
    };
    await saveWorkingState(ctx, {
      round: 3,
      escalation_entries_consumed: 0,
      solved: {
        [required.id]: {
          proof_tex: "",
          snapshot: snapshotMember(PROTO as any, required as any),
          node: required as never,
          partial: true,
        },
      },
      resolved_oeqs: {},
    });
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "correct the exact agent-added result",
      require_core_changes: true,
      required_core_targets: [required.id],
    });
    const calls: string[][] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        calls.push(targets.map((target) => target.id));
        const ownsRequired = targets.some((target) => target.id === required.id);
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets
            .filter((target) => target.id !== required.id)
            .map((target) => ({ id: target.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_statement_changes: ownsRequired ? [{
            id: required.id,
            current: required.statement,
            proposed: "The corrected agent result holds.",
            reason: "directed correction",
            direction: "narrow",
          }] : [],
          proposed_definition_changes: [],
        }, { ...PROTO, statements: [...PROTO.statements, required] })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(calls.some((targets) => targets.includes(required.id))).toBe(true);
    expect(result.status).toBe("checkpoint");
    expect(result.message).toMatch(/STATEMENT change/i);
  });

  it("reopens a stale agent helper through the accepted proof snapshot when a catalog re-emission lost the edge", async () => {
    const ctx = makeCtx(repoRoot);
    const helper: CoreStatement = {
      id: "lem:agent-helper",
      kind: "lemma",
      statement: "The agent helper holds.",
      depends_on: ["ass:overlap"],
      status: "to-prove",
    };
    const consumer: CoreStatement = {
      id: "thm:agent-consumer",
      kind: "theorem",
      statement: "The agent consumer holds.",
      // Reproduce the incident: a later catalog re-emission lost this edge,
      // while the accepted proof snapshot still records that it used the helper.
      depends_on: [],
      status: "to-prove",
    };
    await saveWorkingState(ctx, {
      round: 3,
      escalation_entries_consumed: 0,
      solved: {
        [helper.id]: {
          proof_tex: "Prior helper proof.",
          snapshot: {
            stmt: helper.statement,
            depends_on: helper.depends_on,
            defs: {},
            assumptions: { "ass:overlap": PROTO.assumptions[0].condition },
          },
          node: helper,
          partial: true,
        },
        [consumer.id]: {
          proof_tex: "Prior consumer proof using lem:agent-helper.",
          snapshot: {
            stmt: consumer.statement,
            depends_on: [helper.id],
            defs: {},
            assumptions: {},
          },
          node: consumer,
          partial: true,
        },
      },
      resolved_oeqs: {},
    });
    const calls: string[][] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        calls.push(targets.map(({ id }) => id));
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter(({ id }) => id !== helper.id)
            .map(({ id }) => ({ id, proof_tex: `Fresh proof for ${id}.` })),
          added_lemmas: targets.some(({ id }) => id === helper.id)
            ? [{ ...helper, status: "proved", proof_tex: "Fresh helper proof." }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls.flat()).toContain(consumer.id);
    expect(calls.flat()).toContain(helper.id);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id].partial).toBeUndefined();
    expect(working.solved[helper.id].shelved).toBeUndefined();
    const published = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(published.statements.some((statement: any) => statement.id === helper.id)).toBe(true);
  });

  it("adopts ALL legacy checkpoint-only agent nodes into the cursor, not just the targeted one (audit R2F1)", async () => {
    // A pre-migration cursor + a published core holding two agent nodes the cursor
    // never catalogued. The first post-migration round targets only one; the OTHER
    // must survive as shelved debt in the (now format-2) cursor — otherwise the
    // commit's render drops it and no later directive can ever recover it.
    const ctx = makeCtx(repoRoot);
    const agentNode = (id: string) => ({
      id, kind: "theorem", statement: `${id} holds.`, depends_on: ["ass:overlap"], status: "to-prove",
      justification: "agent-added", gap: "g", consumer: "c",
    });
    await writeFile(coreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [...PROTO.statements, agentNode("thm:agent-a"), agentNode("thm:agent-b")],
    }), "utf8");
    // Legacy cursor: written directly, no store_format stamp.
    await writeFile(workingPath(ctx), JSON.stringify({
      round: 3, escalation_entries_consumed: 0, solved: {}, resolved_oeqs: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    }), "utf8");
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "correct thm:agent-a",
      require_core_changes: true,
      required_core_targets: ["thm:agent-a"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets.filter((t) => t.id !== "thm:agent-a").map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_statement_changes: targets.some((t) => t.id === "thm:agent-a") ? [{
            id: "thm:agent-a",
            current: "thm:agent-a holds.",
            proposed: "thm:agent-a holds on the overlap region.",
            reason: "directed correction",
            direction: "narrow",
          }] : [],
          proposed_definition_changes: [],
        }, {
          ...PROTO,
          statements: [...PROTO.statements, agentNode("thm:agent-a"), agentNode("thm:agent-b")],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    const cursor = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(cursor.store_format).toBe(2);
    const adopted = cursor.solved["thm:agent-b"];
    expect(adopted).toBeDefined();
    expect(adopted.partial).toBe(true);
    expect(adopted.shelved).toBe(true);
    expect(adopted.node.statement).toBe("thm:agent-b holds.");
    // The shelved adoption is catalog-only: the published render must not carry it.
    const published = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(published.statements.some((s: any) => s.id === "thm:agent-b")).toBe(false);
  });

  it("resolves solver TeX from the companion file end-to-end: raw bytes reach the committed core (Phase 3)", async () => {
    const ctx = makeCtx(repoRoot);
    // Deliberately under-escaped TeX that the JSON channel would corrupt.
    const rawTex = "Assume \\theta; then\n\\[ \\theta \\le \\tau(\\bar d). \\]";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const companionPath = /SOLVE_COMPANION_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const blocks = targets.map((t) => `%%% FIELD ${t.id}.proof\n${rawTex}\n`).join("");
        await writeFile(companionPath, blocks, "utf8");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: { tex_ref: `${t.id}.proof` } })),
          added_lemmas: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.solved).toBeGreaterThan(0);
    const published = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    for (const s of published.statements) {
      expect(s.status).toBe("proved");
      expect(s.proof_tex).toBe(rawTex);
    }
    // The companion blocks were content-addressed into the proof archive at ingest.
    const archive = await readProofArchiveIndex(path.dirname(coreJsonPath(ctx)));
    expect(archive.some((e) => e.node_id.startsWith("companion:") && e.reason.startsWith("solve-companion/"))).toBe(true);
  });

  it("pipeline-pins an omitted statement-replace revision across a status echo drift", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<Record<string, any>>;
        const main = targets.some((t) => t.id === "thm:main") ? PROTO.statements[0] : undefined;
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_core_edits: main ? [{
            kind: "statement-replace",
            id: "thm:main",
            // Deliberately omit based_on_revision and echo the assembled/settled
            // status rather than the open dispatch status. The pipeline owns the
            // target revision and must bind it before the fragile echo fallback.
            proposed: {
              id: main.id, kind: main.kind, statement: main.statement, status: "proved",
              depends_on: ["def:env"],
              justification: main.justification, gap: main.gap, consumer: main.consumer,
            },
            reason: "wire the environment definition the proof uses",
            direction: "correct",
          }] : [],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    expect(result.message).toMatch(/STRUCTURED CORE edit/);
    expect((await readSurfacedProposals(ctx)).coreEdits).toContainEqual(
      expect.objectContaining({
        kind: "statement-replace",
        id: "thm:main",
        based_on_revision: expect.stringMatching(/^rev:[a-f0-9]{64}$/),
      }),
    );
    await applyProposedChanges({ ctx });
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.statements.find((s: any) => s.id === "thm:main").depends_on).toEqual(["def:env"]);
    expect(proto.assumptions.find((a: any) => a.id === "ass:overlap").used_by)
      .toEqual(["def:class", "prop:aux"]);
  });

  it("a revision pinned to the DISPLAYED settled view survives a same-bundle claim change (audit R2P23F1)", async () => {
    // The claim-change loop marks the working record partial before the
    // core-edit loop runs, so the settled-overlay view is no longer derivable
    // from the record — the unconditional {...original, status:"proved"}
    // candidate is what keeps the solver's rev(proved) applicable.
    const ctx = makeCtx(repoRoot);
    const main = PROTO.statements[0];
    await saveWorkingState(ctx, {
      round: 2,
      escalation_entries_consumed: 0,
      solved: {
        "thm:main": { proof_tex: "Settled proof.", snapshot: snapshotMember(PROTO as any, main as any) },
        "prop:aux": { proof_tex: "Aux proof.", snapshot: snapshotMember(PROTO as any, PROTO.statements[1] as any) },
      },
      resolved_oeqs: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    } as never);
    const { statementRevision } = await import("../../src/discovery/core/revision.js");
    // The packet/dispatch showed the ASSEMBLED settled view: proved.
    const displayedRevision = statementRevision({ ...main, status: "proved" });
    await seedWorkingProposals(ctx, {
      statements: [{
        id: "thm:main",
        current: main.statement,
        proposed: "tau is identified on the overlap region",
        reason: "narrow to the provable claim",
        direction: "narrow",
      }],
      coreEdits: [{
        kind: "statement-replace",
        id: "thm:main",
        based_on_revision: displayedRevision,
        proposed: {
          id: main.id, kind: main.kind, statement: "tau is identified on the overlap region", status: main.status,
          depends_on: [...main.depends_on, "def:env"],
          justification: main.justification, gap: main.gap, consumer: main.consumer,
        },
        reason: "wire def:env alongside the narrowing",
        direction: "correct",
      }],
    });
    const changed = await applyProposedChanges({ ctx });
    expect(changed.map((c) => c.id).filter((id) => id === "thm:main").length).toBeGreaterThanOrEqual(2);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const applied = proto.statements.find((s: any) => s.id === "thm:main");
    expect(applied.statement).toBe("tau is identified on the overlap region");
    expect(applied.depends_on).toContain("def:env");
  });

  it("skips fail-safe on a stale based_on_revision (unknown hash)", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<Record<string, any>>;
        const main = targets.some((t) => t.id === "thm:main") ? PROTO.statements[0] : undefined;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_core_edits: main ? [{
            kind: "statement-replace",
            id: "thm:main",
            based_on_revision: "rev:" + "0".repeat(64),
            proposed: {
              id: main.id, kind: main.kind, statement: main.statement, status: main.status,
              depends_on: [...main.depends_on, "def:env"],
              justification: main.justification, gap: main.gap, consumer: main.consumer,
            },
            reason: "authored against a stale view",
            direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    // The apply refuses the stale edit fail-safe, naming the hash.
    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/rev:0{64}|matches no current view/);
  });

  it("quarantines an exact claim correction whose structural postimage is stale", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "independent downstream use";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the exact headline claim",
      require_core_changes: true,
      required_core_targets: ["thm:main"],
    });
    const proposedClaim = "tau is identified on the certified overlap region";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: ownsMain ? [{
            id: "thm:main", proof_tex: "Proof of the proposed headline.", argues_proposed: true,
          }] : targets.map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          proposed_statement_changes: ownsMain ? [{
            id: "thm:main", current: proto.statements[0].statement, proposed: proposedClaim,
            reason: "narrow to the certified region", direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace", id: "thm:main",
            based_on_revision: `rev:${"0".repeat(64)}`,
            proposed: { ...proto.statements[0], statement: proposedClaim, free_symbols: [] },
            reason: "stale structural postimage", direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.statements ?? []).not.toContainEqual(expect.objectContaining({ id: "thm:main" }));
    expect(surfaced.coreEdits ?? []).not.toContainEqual(expect.objectContaining({ id: "thm:main" }));
    expect(surfaced.proofs ?? []).not.toContainEqual(expect.objectContaining({ id: "thm:main" }));
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("to-prove");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({ category: "statement-change", target: "thm:main", reason: "correction-pair-inapplicable" }),
      expect.objectContaining({ category: "core-edit", target: "thm:main", reason: "correction-pair-inapplicable" }),
      expect.objectContaining({ category: "proof", target: "thm:main", reason: "correction-pair-inapplicable" }),
    ]));
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });

  it("surfaces a complete correction triple for an explicitly dispatched carried partial", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "thm:carried-correction", kind: "theorem", statement: "the old carried claim",
      depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove",
    } as any;
    const sibling = {
      ...carried,
      id: "thm:carried-correction-sibling",
      statement: "the old sibling carried claim",
    } as any;
    await saveWorkingState(ctx, {
      round: 8,
      solved: {
        [carried.id]: {
          node: carried,
          owner: "thm:historical-owner",
          partial: true,
          proof_tex: "",
          snapshot: snapshotMember(PROTO as any, carried),
        },
        [sibling.id]: {
          node: sibling,
          owner: "thm:different-historical-owner",
          partial: true,
          proof_tex: "",
          snapshot: snapshotMember(PROTO as any, sibling),
        },
      },
    } as never);
    await appendEscalationLog(ctx, {
      round: 9,
      changed: [],
      directive: "correct exactly the carried theorem through its current dispatched owner",
      require_core_changes: true,
      required_core_targets: [carried.id, sibling.id],
    });
    const proposedById = new Map([
      [carried.id, "the corrected carried claim"],
      [sibling.id, "the corrected sibling carried claim"],
    ]);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const targetId = /TARGET STATEMENT\(S\) TO SOLVE[\s\S]*?"id":\s*"([^"]+)"/.exec(prompt)?.[1]!;
        const target = targetId === carried.id ? carried : sibling;
        const proposed = proposedById.get(targetId)!;
        const revision = new RegExp(`"id":\\s*"${targetId}"[\\s\\S]*?"revision":\\s*"([^"]+)"`).exec(prompt)?.[1];
        expect(revision).toMatch(/^rev:[a-f0-9]{64}$/);
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: targetId, proof_tex: `Proof of the corrected claim for ${targetId}.`, argues_proposed: true }],
          proposed_statement_changes: [{
            id: targetId, current: target.statement, proposed,
            based_on_revision: revision, reason: "repair the carried claim", direction: "correct",
          }],
          proposed_core_edits: [{
            kind: "statement-replace", id: targetId, based_on_revision: revision,
            proposed: { ...target, statement: proposed },
            reason: "paired structural postimage", direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const surfaced = await readSurfacedProposals(ctx);
    for (const target of [carried, sibling]) {
      expect(surfaced.statements).toContainEqual(expect.objectContaining({ id: target.id, proposed: proposedById.get(target.id) }));
      expect(surfaced.coreEdits).toContainEqual(expect.objectContaining({ kind: "statement-replace", id: target.id }));
      expect(surfaced.proofs).toContainEqual(expect.objectContaining({ id: target.id, argues_proposed: true }));
    }
    const withheldPath = path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json");
    if (existsSync(withheldPath)) {
      const withheld = JSON.parse(await readFile(withheldPath, "utf8"));
      expect(withheld.withheld_payloads ?? []).not.toContainEqual(
        expect.objectContaining({ reason: "correction-pair-inapplicable" }),
      );
    }
    await applyProposedChanges({ ctx });
    const applied = assembleCore(
      JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")),
      JSON.parse(await readFile(workingPath(ctx), "utf8")),
    );
    for (const target of [carried, sibling]) {
      expect(applied.statements.find((statement: any) => statement.id === target.id)).toMatchObject({
        statement: proposedById.get(target.id),
        status: "proved",
      });
    }
  });

  it("does not re-dispatch or republish a pruned proto orphan on an unrelated round (audit R2F3)", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [
        ...PROTO.statements,
        { id: "lem:orphan", kind: "lemma", statement: "an abandoned helper", depends_on: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      ],
    }), "utf8");
    await saveWorkingState(ctx, {
      round: 6,
      escalation_entries_consumed: 0,
      solved: {},
      resolved_oeqs: {},
      pruned_proto_orphans: ["lem:orphan"],
      store_format: 2,
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    } as never);
    const c = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: c.deps });
    expect(c.calls().flat()).not.toContain("lem:orphan");
    const published = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(published.statements.some((s: any) => s.id === "lem:orphan")).toBe(false);
  });

  it("dispatches a metadata-only directive after every mathematical node is valid", async () => {
    const ctx = makeCtx(repoRoot);
    await saveWorkingState(ctx, {
      round: 3,
      escalation_entries_consumed: 0,
      solved: Object.fromEntries(PROTO.statements.map((statement) => [statement.id, {
        proof_tex: `Proof of ${statement.id}.`,
        snapshot: snapshotMember(PROTO as any, statement as any),
      }])),
    });
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "replace the stale comparator promise table",
      require_core_changes: true,
      required_core_targets: ["metadata:comparator-promise-table"],
    });
    let sawEmptyMetadataUnit = false;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1));
        sawEmptyMetadataUnit = Array.isArray(targets) && targets.length === 0 &&
          prompt.includes("metadata:comparator-promise-table");
        await writeFile(outPath, JSON.stringify({
          proposed_core_edits: [{
            kind: "comparator-promise-table-replace",
            id: "metadata:comparator-promise-table",
            proposed: [{
              comparator_bibkey: "Rosenbaum1983",
              comparator_claim: "background comparator only",
              matched_by: "unmatched",
              match_kind: "downgraded_to_informed_by",
            }],
            reason: "synchronize the structured comparator contract",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(sawEmptyMetadataUnit).toBe(true);
    expect(result.status).toBe("checkpoint");
    expect((await readSurfacedProposals(ctx)).coreEdits).toContainEqual(expect.objectContaining({
      kind: "comparator-promise-table-replace",
      id: "metadata:comparator-promise-table",
    }));
  });

  it("applies a sealed metadata mandate mechanically without dispatching Sol", async () => {
    const ctx = makeCtx(repoRoot);
    const working = {
      round: 3,
      proposal_revision: "angle:0/version:1",
      escalation_entries_consumed: 0,
      solved: Object.fromEntries(PROTO.statements.map((statement) => [statement.id, {
        proof_tex: `Proof of ${statement.id}.`,
        snapshot: snapshotMember(PROTO as any, statement as any),
      }])),
    } as any;
    await saveWorkingState(ctx, working);
    const edit = {
      kind: "rebuild-reverse-dependencies" as const,
      id: "metadata:reverse-dependencies" as const,
      reason: "mechanically rebuild the derived reverse edge table",
      direction: "correct" as const,
    };
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "apply the already-adjudicated reverse-dependency rebuild",
      require_core_changes: true,
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: PROTO as any,
        working,
        edit,
        proposalRevision: "angle:0/version:1",
      })],
    });
    let solverCalls = 0;
    const deps: StageDeps = {
      runCodex: async () => {
        solverCalls += 1;
        throw new Error("sealed mechanical edit must not dispatch a solver");
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeVersionedState(), deps }) as any;
    expect(solverCalls).toBe(0);
    expect(result.status).toBe("checkpoint");
    expect((await readSurfacedProposals(ctx)).coreEdits).toEqual([
      expect.objectContaining({ kind: "rebuild-reverse-dependencies" }),
    ]);
  });

  it("surfaces a statement-replace whose ONLY delta is free_symbols", async () => {
    // Regression (stat_doseresponse_minimax_elbow, 2026-07-29). `free_symbols` on a
    // proto-frozen statement is writable through exactly ONE channel, `statement-replace`,
    // and apply REQUIRES that channel to echo the claim text byte-for-byte. But the merge
    // no-op filter compared only {status, kind, statement, depends_on, source} — so a
    // payload whose sole delta was `free_symbols` matched "no-op" and was spliced out,
    // while anything altered enough to survive the filter was then refused by apply's echo
    // check. The field was unwritable BY CONSTRUCTION, and because the splice happens
    // upstream of apply's `skipped` ledger it left no receipt: the round just reported
    // fewer edits than the model emitted. Two orchestrators mis-attributed it (to the
    // ownership projection, and to the echo view) before the emitted-vs-persisted diff
    // located it.
    const ctx = makeCtx(repoRoot);
    const target = PROTO.statements[0] as any;
    await saveWorkingState(ctx, {
      round: 3,
      escalation_entries_consumed: 0,
      solved: Object.fromEntries(PROTO.statements.map((statement) => [statement.id, {
        proof_tex: `Proof of ${statement.id}.`,
        snapshot: snapshotMember(PROTO as any, statement as any),
      }])),
    });
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "drop the retired symbol from the declaration; change nothing else",
      require_core_changes: true,
      required_core_targets: [target.id],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proposed_core_edits: [{
            kind: "statement-replace",
            id: target.id,
            // The solver sees the assembled proved overlay, not the frozen to-prove
            // storage node. Echo that apply-time status exactly; ONLY free_symbols moves.
            proposed: { ...target, status: "proved", free_symbols: [] },
            reason: "retired symbol removed from the declaration",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });

    expect((await readSurfacedProposals(ctx)).coreEdits).toContainEqual(expect.objectContaining({
      kind: "statement-replace",
      id: target.id,
    }));
  });

  it("keeps the full agent-node frontier across auto-apply, core clearing, and restart", async () => {
    const ctx = makeCtx(repoRoot);
    const rate = {
      id: "lem:agent-rate", kind: "lemma", statement: "The old rate holds.",
      depends_on: [], status: "proved", proof_tex: "Old rate proof.",
    } as any;
    const remainder = {
      id: "lem:agent-remainder", kind: "lemma", statement: "The remainder is small.",
      depends_on: [rate.id], status: "proved", proof_tex: "Use the rate.",
    } as any;
    const theorem = {
      id: "thm:agent-inference", kind: "theorem", statement: "Inference is valid.",
      depends_on: [remainder.id], status: "proved", proof_tex: "Use the remainder.",
    } as any;
    const snap = (node: any) => ({
      stmt: node.statement, depends_on: node.depends_on, defs: {}, assumptions: {},
    });
    await saveWorkingState(ctx, {
      round: 7,
      solved: Object.fromEntries([rate, remainder, theorem].map((node) => [node.id, {
        proof_tex: node.proof_tex,
        snapshot: snap(node),
        node,
        owner: theorem.id,
      }])),
    });
    await writeFile(coreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [...PROTO.statements, rate, remainder, theorem],
    }), "utf8");
    await appendEscalationLog(ctx, {
      round: 8,
      changed: [],
      directive: "split the agent rate without losing its consumers",
      require_core_changes: true,
      required_core_targets: [rate.id],
    });

    let corrected = false;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsRate = targets.some((target) => target.id === rate.id);
        const body = !corrected && ownsRate ? {
          proofs: targets.map((target) => ({
            id: target.id,
            proof_tex: `Reproved ${target.id}.`,
            ...(target.id === rate.id ? { argues_proposed: true } : {}),
          })),
          added_lemmas: [{
            id: "lem:agent-score", kind: "lemma", statement: "The score rate holds.",
            depends_on: [rate.id], status: "proved", proof_tex: "Use the corrected rate.",
          }],
          proposed_statement_changes: [{
            id: rate.id,
            current: rate.statement,
            proposed: "The corrected transport-only rate holds.",
            reason: "separate the estimator-side score rate",
            direction: "narrow",
          }],
          proposed_core_edits: [{
            kind: "statement-replace",
            id: remainder.id,
            proposed: {
              id: remainder.id,
              kind: remainder.kind,
              statement: remainder.statement,
              depends_on: [rate.id, "lem:agent-score"],
              status: remainder.status,
            },
            reason: "wire the estimator-side score lemma",
            direction: "correct",
          }, {
            kind: "rebuild-reverse-dependencies",
            id: "metadata:reverse-dependencies",
            reason: "refresh metadata after the split",
            direction: "correct",
          }],
        } : {
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `Reproved ${target.id}.` })),
          added_lemmas: [],
          proposed_statement_changes: [],
          proposed_core_edits: [],
        };
        if (ownsRate) corrected = true;
        await writeFile(outPath, JSON.stringify(withCorrectionPairs(body, {
          ...PROTO,
          statements: [...PROTO.statements, rate, remainder, theorem],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const first = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(first).toHaveProperty("status", "checkpoint");
    const beforeApply = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(Object.keys(beforeApply.solved)).toEqual(expect.arrayContaining([
      rate.id, remainder.id, theorem.id, "lem:agent-score",
    ]));
    expect(beforeApply.solved[rate.id]).toMatchObject({ node: { statement: rate.statement } });
    const provisional = (await readSurfacedProposals(ctx)).proofs;
    expect(provisional).toContainEqual({
      id: "lem:agent-score",
      proof_tex: "Use the corrected rate.",
    });

    await applyProposedChanges({ ctx });
    expect(existsSync(coreJsonPath(ctx))).toBe(false);
    const afterApply = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(afterApply.solved[rate.id].node.statement).toBe("The corrected transport-only rate holds.");
    expect(afterApply.solved[rate.id].partial).toBeUndefined();
    expect(afterApply.solved[remainder.id]).toBeDefined();
    expect(afterApply.solved[theorem.id]).toBeDefined();

    const second = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(second).not.toHaveProperty("status");
    const rebuilt = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rebuilt.statements.map((statement: any) => statement.id)).toEqual(expect.arrayContaining([
      rate.id, remainder.id, theorem.id, "lem:agent-score",
    ]));
    expect(rebuilt.statements.find((statement: any) => statement.id === rate.id)).toMatchObject({
      statement: "The corrected transport-only rate holds.",
      status: "proved",
    });
  });

  it("persists proofs and a dependent new proposition alongside a metadata-only rebuild", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements = [proto.statements[0]];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "add the exact finite certificate proposition and rebuild reverse dependencies",
      require_core_changes: true,
      required_core_targets: ["prop:finite-certificate"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:main", proof_tex: "QED." }],
          added_lemmas: [{
            id: "prop:finite-certificate",
            kind: "proposition",
            statement: "The exact certificate is feasible and sharp.",
            depends_on: ["thm:main"],
            status: "proved",
            proof_tex: "Direct substitution proves feasibility and equality.",
          }],
          proposed_core_edits: [{
            kind: "rebuild-reverse-dependencies",
            id: "metadata:reverse-dependencies",
            reason: "refresh derived inverse edges",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });

    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:main")).toMatchObject({ status: "proved", proof_tex: "QED." });
    expect(core.statements.find((s: any) => s.id === "prop:finite-certificate")).toMatchObject({
      status: "proved",
      depends_on: ["thm:main"],
    });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(Object.keys(working.solved)).toEqual(expect.arrayContaining(["thm:main", "prop:finite-certificate"]));
  });

  it("persists an exact new target as partial when its proof awaits a same-round claim edit", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements = [proto.statements[0]];
    const main = proto.statements[0];
    const proposed = `${main.statement} Strengthened post-image.`;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "revise the main claim and add its exact dependent comparison",
      required_core_targets: [main.id, "thm:new-comparison"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: main.id, proof_tex: "The revised main claim follows.", argues_proposed: true }],
          added_lemmas: [{
            id: "thm:new-comparison",
            kind: "theorem",
            statement: "The new comparison follows from the revised main claim.",
            depends_on: [main.id],
            status: "proved",
            proof_tex: "Apply the revised main claim.",
          }],
          proposed_statement_changes: [{
            id: main.id,
            current: main.statement,
            proposed,
            reason: "separate the reviewed comparison",
            direction: "narrow",
          }],
          proposed_core_edits: [{
            kind: "statement-replace",
            id: main.id,
            proposed: { ...main, statement: proposed, free_symbols: [] },
            reason: "synchronize dependencies and metadata",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:new-comparison"]).toMatchObject({
      partial: true,
      node: { id: "thm:new-comparison", status: "to-prove" },
    });
    expect(working.proposals.statements).toHaveLength(1);
    expect(working.proposals.coreEdits).toHaveLength(1);
  });

  it("keeps an exact theorem target pending when only a prerequisite edit is emitted", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements[0].depends_on.push("def:env");
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "correct the estimator definition, then re-prove the main theorem",
      require_core_changes: true,
      required_core_targets: ["thm:main"],
    });

    await expect(runStage0Solve({
      ctx,
      state: makeState(),
      deps: solverDeps("propose-def"),
    })).rejects.toThrow(/required exact structured target.*thm:main.*omitted thm:main/i);
  });

  it("credits an open_obligations attestation for a required oeq target left genuinely open", async () => {
    // The solve prompt instructs that an OEQ with no substantive answer is LEFT OPEN
    // (no proof, no resolution entry). A directive that lists such an oeq among its
    // required targets must therefore accept the sanctioned "stays open" channel —
    // an open_obligations entry — instead of discarding the whole round as "omitted".
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:tightness",
      kind: "openendedquestion",
      statement: "Is the identification bound tight?",
      depends_on: ["thm:main"],
      status: "to-prove",
      justification: "residual question",
      gap: "vs prior",
      consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "re-prove the frontier and settle or attest the tightness question",
      required_core_targets: ["thm:main", "prop:aux", "oeq:tightness"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((t) => !t.id.startsWith("oeq:")).map((t) => ({ id: t.id, proof_tex: "QED." })),
          open_obligations: targets.filter((t) => t.id.startsWith("oeq:")).map((t) => ({
            node_id: t.id,
            what_is_open: "whether the bound is tight",
            obstruction: "no matching lower-bound construction is known",
            attempted: "searched the standard two-point families",
          })),
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result).toBe(false); // clean discharge, oeq recorded as residual
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:main")).toMatchObject({ status: "proved" });
    expect(core.statements.find((s: any) => s.id === "oeq:tightness")).toMatchObject({ status: "to-prove" });
  });

  it.each([
    ["directive owner", true],
    ["semantic owner", false],
  ] as const)("keeps an exact OEQ obligation emitted by the %s", async (_label, emitFromDirectiveOwner) => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:tightness",
      kind: "openendedquestion",
      statement: "Is the identification bound tight?",
      depends_on: [],
      status: "to-prove",
      justification: "residual question",
      gap: "vs prior",
      consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the frontier transaction and leave the residual tightness question open",
      required_core_targets: ["oeq:tightness"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        const semanticOwner = targets.some(({ id }) => id === "oeq:tightness");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((target) => !target.id.startsWith("oeq:"))
            .map(({ id }) => ({ id, proof_tex: "QED." })),
          open_obligations: (emitFromDirectiveOwner ? owner : semanticOwner) ? [{
            node_id: "oeq:tightness",
            what_is_open: "canonical residual",
            obstruction: "no matching lower-bound construction is known",
            attempted: "searched the standard two-point families",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const obligations = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "open_obligations.json"),
      "utf8",
    ));
    expect(JSON.stringify(obligations)).toContain("canonical residual");
  });

  it("credits a substantive scoped statement note for its exact metadata target", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "correct only the theorem's stale consumer metadata",
      required_core_targets: ["thm:main"],
      require_core_changes: true,
    });
    const updatedConsumer = "The residual open question consumes this theorem.";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          prose_updates: { statement_notes: [{ id: "thm:main", consumer: updatedConsumer }] },
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });

    // Phase 1: prose durability lives in the working state's overlay and the
    // rendered core.json — the frozen proto is NEVER written mid-round.
    expect(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")).statements.find(
      (statement: any) => statement.id === "thm:main",
    ).consumer).toBe(updatedConsumer);
    const cursor = await loadWorkingState(ctx);
    expect(cursor?.prose_overlay?.statement_notes?.["thm:main"]?.consumer).toBe(updatedConsumer);
    expect(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")).statements.find(
      (statement: any) => statement.id === "thm:main",
    ).consumer).toBe(PROTO.statements[0].consumer);
  });

  it("prunes orphan statement notes from the durable overlay while preserving live notes", async () => {
    const ctx = makeCtx(repoRoot);
    const dormantHelper: CoreStatement = {
      id: "lem:dormant-helper",
      kind: "lemma",
      statement: "The dormant helper remains available for a later exact-target revival.",
      depends_on: [],
      status: "to-prove",
      justification: "durable helper",
      gap: "later repair",
      consumer: "future theorem",
    };
    await saveWorkingState(ctx, {
      round: 1,
      solved: {
        [dormantHelper.id]: {
          proof_tex: "Partial argument.",
          snapshot: snapshotMember(PROTO as never, dormantHelper as never),
          node: dormantHelper,
          partial: true,
          shelved: true,
        },
      },
      prose_overlay: {
        statement_notes: {
          "thm:main": { consumer: "live durable note" },
          [dormantHelper.id]: { consumer: "revivable shelved note" },
          "oeq:retired-question": { consumer: "stale question note" },
          "thm:retired-answer": { justification: "stale answer note" },
        },
      },
    });

    await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") });

    const cursor = await loadWorkingState(ctx);
    expect(cursor?.prose_overlay?.statement_notes).toEqual({
      "thm:main": { consumer: "live durable note" },
      [dormantHelper.id]: { consumer: "revivable shelved note" },
    });
    const rendered = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rendered.statements.find((statement: any) => statement.id === "thm:main")?.consumer)
      .toBe("live durable note");
  });

  it("preserves notes for reversible resolved-OEQ and shelved-node records", () => {
    const source: CoreStatement = {
      id: "oeq:resolved-source",
      kind: "openendedquestion",
      statement: "Can the residual bound be sharpened?",
      depends_on: [],
      status: "to-prove",
      justification: "durable question",
      gap: "sharpness",
      consumer: "future narrowing",
    };
    const shelved: CoreStatement = {
      id: "lem:shelved-helper",
      kind: "lemma",
      statement: "A helper retained for a later revival.",
      depends_on: [],
      status: "to-prove",
      justification: "durable helper",
      gap: "later repair",
      consumer: "future theorem",
    };
    const agentSourceId = "oeq:agent-resolved-source";
    const agentSource: CoreStatement = {
      ...source,
      id: agentSourceId,
      statement: "Can an agent-authored residual question be answered?",
    };
    const agentAnswer: CoreStatement = {
      id: "thm:agent-resolved-answer",
      kind: "theorem",
      statement: "The agent-authored residual has a negative answer.",
      depends_on: [],
      status: "proved",
      proof_tex: "Direct argument.",
    };
    const proto = structuredClone(PROTO) as any;
    proto.statements.push(source);
    const working = {
      round: 1,
      solved: {
        [shelved.id]: {
          proof_tex: "Partial argument.",
          snapshot: snapshotMember(proto as never, shelved as never),
          node: shelved,
          partial: true as const,
          shelved: true,
        },
        [agentAnswer.id]: {
          proof_tex: agentAnswer.proof_tex!,
          snapshot: snapshotMember(proto as never, agentAnswer as never),
          node: agentAnswer,
          owner: agentSourceId,
        },
      },
      resolved_oeqs: {
        [agentSourceId]: {
          theorem_id: agentAnswer.id,
          source_fingerprint: oeqSourceFingerprint(agentSource),
        },
      },
      prose_overlay: {
        statement_notes: {
          [source.id]: { consumer: "restore this if the resolution detaches" },
          [shelved.id]: { consumer: "restore this if a root revives it" },
          [agentSourceId]: { consumer: "restore this agent source if its answer is deleted" },
          "thm:deleted": { consumer: "orphaned note" },
        },
      },
    };

    expect(pruneOrphanStatementNotes(proto, working)).toEqual(["thm:deleted"]);
    expect(working.prose_overlay.statement_notes[source.id]).toEqual({
      consumer: "restore this if the resolution detaches",
    });
    expect(working.prose_overlay.statement_notes[shelved.id]).toEqual({
      consumer: "restore this if a root revives it",
    });
    expect(working.prose_overlay.statement_notes[agentSourceId]).toEqual({
      consumer: "restore this agent source if its answer is deleted",
    });
    expect(working.prose_overlay.statement_notes).not.toHaveProperty("thm:deleted");
  });

  it("does not credit a byte-identical statement note for an exact metadata target", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "require a substantive theorem metadata correction",
      required_core_targets: ["thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          prose_updates: {
            statement_notes: [{ id: "thm:main", consumer: PROTO.statements[0].consumer }],
          },
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /required exact structured target.*thm:main.*omitted thm:main/i,
    );
  });

  it("rejects an open obligation that competes with a proof disposition", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "settle each target exactly once",
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const semanticOwner = targets.some(({ id }) => id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
          open_obligations: semanticOwner ? [{
            node_id: "prop:aux",
            what_is_open: "a competing claimed gap",
            obstruction: "claimed obstruction",
            attempted: "claimed route",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /mutually exclusive terminal dispositions for prop:aux.*open-obligation.*proof/i,
    );
  });

  it("rejects a sibling-target self-contradiction before capability quarantine", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: ownsMain
            ? [
              { id: "thm:main", proof_tex: "Main proof." },
              { id: "prop:aux", proof_tex: "Unauthorized sibling proof." },
            ]
            : [{ id: "prop:aux", proof_tex: "Owner proof." }],
          open_obligations: ownsMain ? [{
            node_id: "prop:aux",
            what_is_open: "the same sibling is also claimed open",
            obstruction: "self-contradictory sibling assessment",
            attempted: "the sibling route",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /mutually exclusive terminal dispositions for prop:aux.*open-obligation.*proof/i,
    );
  });

  it("rejects a same-worker proof plus deletion of the same target", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          proposed_core_edits: ownsMain ? [{
            kind: "statement-delete", id: "thm:main",
            reason: "simultaneously claimed obsolete", direction: "delete-obsolete",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /mutually exclusive terminal dispositions for thm:main.*proof.*statement-delete/i,
    );
  });

  it("quarantines a cross-worker proof versus sibling deletion", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "independent downstream use";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "settle both targets without discarding unrelated work",
      required_core_targets: ["thm:main", "prop:aux"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsAux = targets.some(({ id }) => id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `Owner proof for ${id}.` })),
          proposed_core_edits: ownsAux ? [{
            kind: "statement-delete", id: "thm:main",
            reason: "sibling claims it obsolete", direction: "delete-obsolete",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("to-prove");
    expect(core.statements.find((statement: any) => statement.id === "prop:aux")?.status).toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({ category: "proof", target: "thm:main", reason: "cross-unit-terminal-disposition" }),
      expect.objectContaining({ category: "statement-delete", target: "thm:main", reason: "cross-unit-terminal-disposition" }),
    ]));
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });

  it("quarantines a proofless claim correction versus sibling deletion", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "independent downstream use";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "repair both exact targets without losing deletion disputes",
      require_core_changes: true, required_core_targets: ["thm:main", "prop:aux"],
    });
    const proposedClaim = "tau is identified on the certified region";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        const ownsAux = targets.some(({ id }) => id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: ownsAux ? [{ id: "prop:aux", proof_tex: "Independent auxiliary proof." }] : [],
          proposed_statement_changes: ownsMain ? [{
            id: "thm:main", current: proto.statements[0].statement, proposed: proposedClaim,
            reason: "narrow the claim", direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...proto.statements[0], statement: proposedClaim, free_symbols: [] },
            reason: "complete correction postimage", direction: "correct",
          }] : ownsAux ? [{
            kind: "statement-delete", id: "thm:main",
            reason: "sibling instead declares it obsolete", direction: "delete-obsolete",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.statements ?? []).not.toContainEqual(expect.objectContaining({ id: "thm:main" }));
    expect(surfaced.coreEdits ?? []).not.toContainEqual(expect.objectContaining({ id: "thm:main" }));
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")).toMatchObject({
      statement: proto.statements[0].statement, status: "to-prove",
    });
    expect(core.statements.find((statement: any) => statement.id === "prop:aux")?.status).toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({ category: "statement-mutation", target: "thm:main", reason: "cross-unit-terminal-disposition" }),
      expect.objectContaining({ category: "statement-delete", target: "thm:main", reason: "cross-unit-terminal-disposition" }),
    ]));
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });

  it("quarantines an authorized proof that races an unauthorized sibling open receipt", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "independent downstream use";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "settle both exact targets while retaining disagreements",
      required_core_targets: ["thm:main", "prop:aux"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsAux = targets.some(({ id }) => id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `Owner proof for ${id}.` })),
          open_obligations: ownsAux ? [{
            node_id: "thm:main",
            what_is_open: "the sibling disputes the main proof",
            obstruction: "a sibling-side obstruction",
            attempted: "the sibling route",
            partial_result: "Sibling partial bytes.",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("to-prove");
    expect(core.statements.find((statement: any) => statement.id === "prop:aux")?.status).toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: "proof", target: "thm:main", reason: "cross-unit-terminal-disposition",
        payload: expect.objectContaining({ proof_tex: "Owner proof for thm:main." }),
      }),
      expect.objectContaining({
        category: "open-obligation", target: "thm:main", reason: "cross-unit-terminal-disposition",
        payload: expect.objectContaining({ partial_result: "Sibling partial bytes." }),
      }),
    ]));
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });

  it("quarantines an authorized proof when a sibling emits an incompatible settled version", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "independent downstream use";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "settle both exact targets while retaining version disputes",
      required_core_targets: ["thm:main", "prop:aux"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsAux = targets.some(({ id }) => id === "prop:aux");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `Owner proof for ${id}.` })),
          added_lemmas: ownsAux ? [{
            ...proto.statements[0],
            statement: "INCOMPATIBLE SIBLING CLAIM",
            status: "proved", proof_tex: "Sibling incompatible proof.",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")).toMatchObject({
      statement: proto.statements[0].statement, status: "to-prove",
    });
    expect(core.statements.find((statement: any) => statement.id === "prop:aux")?.status).toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: "added-node", target: "thm:main", reason: "capability-quarantine",
        payload: expect.objectContaining({ statement: "INCOMPATIBLE SIBLING CLAIM" }),
      }),
      expect.objectContaining({
        category: "proof", target: "thm:main", reason: "conflicted-dependency-consumer",
        payload: expect.objectContaining({ carrier: expect.objectContaining({ proof_tex: "Owner proof for thm:main." }) }),
      }),
    ]));
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });

  it("quarantines cross-unit proof/open dispositions while committing unrelated work", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "settle the two targets without discarding unrelated work on disagreement",
      required_core_targets: ["thm:main", "prop:aux"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const mainUnit = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          open_obligations: mainUnit && !targets.some(({ id }) => id === "prop:aux") ? [{
            node_id: "prop:aux",
            what_is_open: "the directive owner reports a residual gap",
            obstruction: "a competing obstruction assessment",
            attempted: "the directive-wide route",
            partial_result: "Partial prop:aux argument.",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("proved");
    expect(core.statements.find((statement: any) => statement.id === "prop:aux")?.status).toBe("to-prove");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: "proof", target: "prop:aux", reason: "cross-unit-terminal-disposition",
      }),
      expect.objectContaining({
        category: "open-obligation", target: "prop:aux", reason: "cross-unit-terminal-disposition",
      }),
    ]));
  });

  it("quarantines both OEQ endpoints and answer consumers when Q-to-T races open T", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:terminal-race", kind: "openendedquestion",
      statement: "Is the terminal rate sharp?", depends_on: ["ass:overlap"], status: "to-prove",
      justification: "residual question", gap: "vs prior", consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "settle or attest the rate question while preserving unrelated work",
      required_core_targets: ["thm:main", "oeq:terminal-race", "thm:terminal-answer"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        const ownsQuestion = targets.some(({ id }) => id === "oeq:terminal-race");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter(({ id }) => !id.startsWith("oeq:"))
            .map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          resolved_oeqs: ownsQuestion ? [{
            source_id: "oeq:terminal-race",
            theorem: {
              id: "thm:terminal-answer", kind: "theorem", statement: "The terminal rate is sharp.",
              depends_on: ["ass:overlap"], status: "proved", proof_tex: "Sharp answer proof.",
            },
          }] : [],
          added_lemmas: ownsQuestion ? [{
            id: "lem:answer-consumer", kind: "lemma", statement: "A consequence of the sharp answer.",
            depends_on: ["thm:terminal-answer"], status: "proved", proof_tex: "Consumer proof.",
          }] : [],
          open_obligations: ownsMain && !ownsQuestion ? [{
            node_id: "thm:terminal-answer",
            what_is_open: "whether the proposed answer theorem is established",
            obstruction: "a competing obstruction assessment",
            attempted: "the directive-wide route",
            partial_result: "Partial question analysis.",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("proved");
    expect(core.statements.find((statement: any) => statement.id === "oeq:terminal-race")?.status)
      .toBe("to-prove");
    expect(core.statements.some((statement: any) =>
      statement.id === "thm:terminal-answer" || statement.id === "lem:answer-consumer"
    )).toBe(false);
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.conflict_consumers).toContain("lem:answer-consumer");
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({
        category: "oeq-resolution", target: "oeq:terminal-race",
        reason: "cross-unit-terminal-disposition",
        payload: expect.objectContaining({ theorem: expect.objectContaining({ proof_tex: "Sharp answer proof." }) }),
      }),
      expect.objectContaining({
        category: "oeq-resolution", target: "thm:terminal-answer",
        reason: "cross-unit-terminal-disposition",
      }),
      expect.objectContaining({
        category: "statement", target: "lem:answer-consumer",
        reason: "conflicted-dependency-consumer",
        payload: expect.objectContaining({ proof_tex: "Consumer proof." }),
      }),
    ]));
  });

  it("quarantines both OEQ endpoints when the answer transitively consumes a conflicted helper", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:transitive-resolution-race", kind: "openendedquestion",
      statement: "Is the transitive answer sharp?", depends_on: [], status: "to-prove",
      justification: "residual question", gap: "vs prior", consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "answer the sharpness question while preserving unrelated progress",
      require_core_changes: true,
      required_core_targets: ["oeq:transitive-resolution-race", "thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsQuestion = targets.some(({ id }) => id === "oeq:transitive-resolution-race");
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        const shared = {
          id: "lem:transitive-shared", kind: "lemma",
          statement: ownsQuestion ? "the first helper variant" : "the competing helper variant",
          depends_on: ["ass:overlap"], status: "proved",
          proof_tex: ownsQuestion ? "First helper proof." : "Competing helper proof.",
        };
        await writeFile(outPath, JSON.stringify({
          proofs: ownsMain ? [{ id: "thm:main", proof_tex: "Unrelated accepted proof." }] : [],
          added_lemmas: [shared],
          resolved_oeqs: ownsQuestion ? [{
            source_id: "oeq:transitive-resolution-race",
            theorem: {
              id: "thm:transitive-answer", kind: "theorem",
              statement: "The transitive answer is sharp.",
              depends_on: [shared.id], status: "proved", proof_tex: "Answer via the shared helper.",
            },
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("proved");
    expect(core.statements.find((statement: any) => statement.id === "oeq:transitive-resolution-race")?.status)
      .toBe("to-prove");
    expect(core.statements.some((statement: any) => statement.id === "thm:transitive-answer")).toBe(false);
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.conflict_consumers).toEqual(expect.arrayContaining([
      "oeq:transitive-resolution-race", "thm:transitive-answer",
    ]));
    for (const endpoint of ["oeq:transitive-resolution-race", "thm:transitive-answer"]) {
      expect(withheld.withheld_payloads).toContainEqual(expect.objectContaining({
        category: "oeq-resolution", target: endpoint,
        reason: "conflicted-dependency-consumer",
        payload: expect.objectContaining({
          source_id: "oeq:transitive-resolution-race",
          theorem: expect.objectContaining({ id: "thm:transitive-answer" }),
        }),
      }));
    }
  });

  it("rejects same-unit Q-to-T resolution plus open T as self-contradictory", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:same-unit-terminal-race", kind: "openendedquestion",
      statement: "Is the same-unit rate sharp?", depends_on: [], status: "to-prove",
      justification: "residual question", gap: "vs prior", consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsQuestion = targets.some(({ id }) => id === "oeq:same-unit-terminal-race");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter(({ id }) => !id.startsWith("oeq:"))
            .map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          resolved_oeqs: ownsQuestion ? [{
            source_id: "oeq:same-unit-terminal-race",
            theorem: {
              id: "thm:same-unit-answer", kind: "theorem", statement: "The same-unit rate is sharp.",
              depends_on: [], status: "proved", proof_tex: "Answer proof.",
            },
          }] : [],
          open_obligations: ownsQuestion ? [{
            node_id: "thm:same-unit-answer",
            what_is_open: "the emitted answer theorem remains open",
            obstruction: "self-reported obstruction",
            attempted: "the same solve route",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /mutually exclusive terminal dispositions for thm:same-unit-answer.*oeq-resolution.*open-obligation/i,
    );
  });

  it("rejects settling an existing OEQ through added_lemmas while leaving it open", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:tightness",
      kind: "openendedquestion",
      statement: "Is the identification bound tight?",
      depends_on: [],
      status: "to-prove",
      justification: "residual question",
      gap: "vs prior",
      consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsOeq = targets.some(({ id }) => id === "oeq:tightness");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter(({ id }) => !id.startsWith("oeq:")).map(({ id }) => ({ id, proof_tex: "QED." })),
          added_lemmas: ownsOeq ? [{
            id: "oeq:tightness",
            kind: "openendedquestion",
            statement: "Is the identification bound tight?",
            depends_on: [],
            status: "proved",
            proof_tex: "An in-place answer.",
          }] : [],
          open_obligations: ownsOeq ? [{
            node_id: "oeq:tightness",
            what_is_open: "the same question",
            obstruction: "no construction",
            attempted: "standard routes",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).resolves.toMatchObject({
      status: "checkpoint", advance: false,
    });
    const rendered = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rendered.statements.find((statement: any) => statement.id === "oeq:tightness"))
      .toMatchObject({ kind: "openendedquestion", status: "to-prove" });
  });

  it("does not let a definition-change payload masquerade as an exact OEQ disposition", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:tightness",
      kind: "openendedquestion",
      statement: "Is the identification bound tight?",
      depends_on: [],
      status: "to-prove",
      justification: "residual question",
      gap: "vs prior",
      consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "settle or attest the exact OEQ target",
      required_core_targets: ["oeq:tightness"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets.filter(({ id }) => !id.startsWith("oeq:")).map(({ id }) => ({ id, proof_tex: "QED." })),
          proposed_definition_changes: owner ? [{
            id: "oeq:tightness",
            current: "not a definition",
            proposed: "still not a definition",
            reason: "wrong payload channel",
            direction: "correct",
          }] : [],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(/invalid solve JSON/i);
  });

  it("does not let a no-op definition echo consume an exact structured target", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "change the exact envelope definition substantively",
      require_core_changes: true,
      required_core_targets: ["def:env"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets.map(({ id }) => ({ id, proof_tex: "QED." })),
          proposed_definition_changes: owner ? [{
            id: "def:env",
            current: "U = a",
            proposed: "U = a",
            reason: "echo only",
            direction: "correct",
          }] : [],
          proposed_statement_changes: owner ? [{
            id: "def:env",
            current: "not a statement",
            proposed: "still not a statement",
            reason: "wrong-channel fallback",
            direction: "narrow",
          }] : [],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(/invalid solve JSON/i);
  });

  it("drops a re-proposal of an assumption the proto already holds verbatim (no-op echo)", async () => {
    // The statement/definition no-op filters already drop already-applied echoes;
    // assumptions had no such filter, so a solver re-emitting an applied assumption
    // verbatim forced a proposal checkpoint every round — and the apply-side skip
    // then made the orchestrator's apply-all refuse as a partial apply.
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
          proposed_assumptions: [{
            id: "ass:overlap",
            condition: "the propensity is bounded away from 0 and 1",
            reason: "restating the standing support condition",
            standard_or_novel: "standard: Rosenbaum1983",
            not_crux: "background condition",
          }],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect("status" in result, "a verbatim assumption echo must not force a checkpoint").toBe(false);
  });

  it("applies a proofs[]-channel proof to a lemma the SAME round adds via added_lemmas", async () => {
    // The unmatched-id partition snapshotted core.statements per unit BEFORE that
    // unit's added_lemmas were installed, so the prompt-licensed split — lemma node in
    // added_lemmas, its proof in proofs[] — was withheld as a "PLUMBING FAULT:
    // unmatched id" even though the id exists in the very core the round persists
    // (and matching was dispatch-order-dependent for cross-unit splits).
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
            ...(targets.some((t) => t.id === "thm:main")
              ? [{ id: "lem:split-helper", proof_tex: "The helper follows by direct computation." }]
              : []),
          ],
          added_lemmas: targets.some((t) => t.id === "thm:main")
            ? [{ id: "lem:split-helper", kind: "lemma", statement: "the split helper claim", depends_on: [], status: "to-prove" }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(String((result as { message?: string }).message ?? "")).not.toMatch(/PLUMBING FAULT/);
    expect("status" in result, "the split emission must discharge cleanly").toBe(false);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const lem = core.statements.find((s: any) => s.id === "lem:split-helper");
    expect(lem?.status).toBe("proved");
    expect(lem?.proof_tex).toBe("The helper follows by direct computation.");
  });

  it("accepts the durable owner's proposed proof for a shelved agent node", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "lem:carried-partial",
      kind: "lemma",
      statement: "the broad carried claim",
      depends_on: [],
      status: "to-prove",
    } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [carried.id]: {
          proof_tex: "Partial argument.",
          snapshot: { stmt: carried.statement, depends_on: [], defs: {}, assumptions: {} },
          node: carried,
          owner: "thm:main",
          partial: true,
          shelved: true,
        },
      },
    });
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "narrow the carried helper and complete the main result",
      require_core_changes: true,
      required_core_targets: ["thm:main"],
    });
    const proposed = "the narrowed carried claim";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsMain
              ? [{ id: carried.id, proof_tex: "Complete narrowed proof.", argues_proposed: true }]
              : []),
          ],
          proposed_statement_changes: ownsMain ? [{
            id: carried.id,
            current: carried.statement,
            proposed,
            reason: "the argument establishes exactly the narrower form",
            direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace",
            id: carried.id,
            proposed: { ...carried, statement: proposed, free_symbols: [] },
            reason: "publish the complete narrowed agent-node metadata",
            direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.proofs).toContainEqual({
      id: carried.id,
      proof_tex: "Complete narrowed proof.",
      argues_proposed: true,
    });
    expect(surfaced.statements).toContainEqual(expect.objectContaining({ id: carried.id, proposed }));
  });

  it("keeps sole-directive-owner proofs across a reachable paired postimage chain", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:paired-chain-helper", kind: "lemma", statement: "old helper claim",
      depends_on: [], status: "to-prove",
    } as any;
    const bridge = {
      id: "lem:paired-chain-bridge", kind: "lemma", statement: "old bridge claim",
      depends_on: [], status: "to-prove",
    } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [helper.id]: {
          proof_tex: "Old helper proof.", snapshot: { stmt: helper.statement, depends_on: [], defs: {}, assumptions: {} },
          node: { ...helper, status: "proved", proof_tex: "Old helper proof." }, owner: "thm:stale-owner",
        },
        [bridge.id]: {
          proof_tex: "Old bridge proof.", snapshot: { stmt: bridge.statement, depends_on: [], defs: {}, assumptions: {} },
          node: { ...bridge, status: "proved", proof_tex: "Old bridge proof." }, owner: "thm:stale-owner",
        },
      },
    });
    await appendEscalationLog(ctx, {
      round: 4,
      changed: [],
      directive: "repair the root and its reachable paired helper chain",
      require_core_changes: true,
      required_core_targets: ["thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        const mainClaim = "tau is identified through the paired chain";
        const bridgeClaim = "new bridge claim";
        const helperClaim = "new helper claim";
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.`, argues_proposed: ownsMain })),
            ...(ownsMain ? [
              { id: bridge.id, proof_tex: "Proved new bridge claim.", argues_proposed: true },
              { id: helper.id, proof_tex: "Proved new helper claim.", argues_proposed: true },
            ] : []),
          ],
          proposed_statement_changes: ownsMain ? [
            { id: "thm:main", current: PROTO.statements[0].statement, proposed: mainClaim, reason: "root repair", direction: "narrow" },
            { id: bridge.id, current: bridge.statement, proposed: bridgeClaim, reason: "bridge repair", direction: "narrow" },
            { id: helper.id, current: helper.statement, proposed: helperClaim, reason: "helper repair", direction: "narrow" },
          ] : [],
          proposed_core_edits: ownsMain ? [
            {
              kind: "statement-replace", id: "thm:main",
              proposed: { ...PROTO.statements[0], statement: mainClaim, depends_on: ["ass:overlap", bridge.id], free_symbols: [] },
              reason: "wire bridge", direction: "correct",
            },
            {
              kind: "statement-replace", id: bridge.id,
              proposed: { ...bridge, statement: bridgeClaim, depends_on: [helper.id], free_symbols: [] },
              reason: "wire helper", direction: "correct",
            },
            {
              kind: "statement-replace", id: helper.id,
              proposed: { ...helper, statement: helperClaim, free_symbols: [] },
              reason: "publish helper repair", direction: "correct",
            },
          ] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    const proofs = (await readSurfacedProposals(ctx)).proofs;
    expect(proofs).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: bridge.id, proof_tex: "Proved new bridge claim." }),
      expect.objectContaining({ id: helper.id, proof_tex: "Proved new helper claim." }),
    ]));
  });

  it("keeps sole-root paired revalidations for reachable published ownerless core nodes", async () => {
    const ctx = makeCtx(repoRoot);
    const leaf = {
      id: "lem:published-ownerless-leaf", kind: "lemma", statement: "old published leaf",
      depends_on: [], status: "proved", proof_tex: "Old published leaf proof.",
    } as any;
    const bridge = {
      id: "lem:published-ownerless-bridge", kind: "lemma", statement: "old published bridge",
      depends_on: [leaf.id], status: "proved", proof_tex: "Old published bridge proof.",
    } as any;
    const root = { ...PROTO.statements[0], depends_on: ["ass:overlap", bridge.id] } as any;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [root, PROTO.statements[1], bridge, leaf],
    }), "utf8");
    await saveWorkingState(ctx, {
      round: 1,
      solved: {
        [bridge.id]: {
          proof_tex: bridge.proof_tex,
          snapshot: { stmt: bridge.statement, depends_on: bridge.depends_on, defs: {}, assumptions: {} },
          node: bridge,
        },
        [leaf.id]: {
          proof_tex: leaf.proof_tex,
          snapshot: { stmt: leaf.statement, depends_on: leaf.depends_on, defs: {}, assumptions: {} },
          node: leaf,
        },
      },
    });
    await appendEscalationLog(ctx, {
      round: 2,
      changed: [],
      directive: "revalidate the published ownerless proof chain under the sole theorem root",
      require_core_changes: true,
      required_core_targets: [root.id],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsRoot = targets.some((target) => target.id === root.id);
        const bridgeClaim = "revalidated published bridge";
        const leafClaim = "revalidated published leaf";
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.filter((target) => target.id !== bridge.id && target.id !== leaf.id)
              .map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsRoot ? [
              { id: bridge.id, proof_tex: "Fresh published bridge proof.", argues_proposed: true },
              { id: leaf.id, proof_tex: "Fresh published leaf proof.", argues_proposed: true },
            ] : []),
          ],
          proposed_statement_changes: ownsRoot ? [
            { id: bridge.id, current: bridge.statement, proposed: bridgeClaim, reason: "definition-triggered revalidation", direction: "narrow" },
            { id: leaf.id, current: leaf.statement, proposed: leafClaim, reason: "definition-triggered revalidation", direction: "narrow" },
          ] : [],
          proposed_core_edits: ownsRoot ? [
            {
              kind: "statement-replace", id: bridge.id,
              proposed: { ...bridge, statement: bridgeClaim, status: "to-prove", proof_tex: undefined, free_symbols: [] },
              reason: "publish revalidated bridge", direction: "correct",
            },
            {
              kind: "statement-replace", id: leaf.id,
              proposed: { ...leaf, statement: leafClaim, status: "to-prove", proof_tex: undefined, free_symbols: [] },
              reason: "publish revalidated leaf", direction: "correct",
            },
          ] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.proofs).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: bridge.id, proof_tex: "Fresh published bridge proof." }),
      expect.objectContaining({ id: leaf.id, proof_tex: "Fresh published leaf proof." }),
    ]));
  });

  it("does not resurrect an explicitly shelved agent proposition as an independent root", async () => {
    const ctx = makeCtx(repoRoot);
    const shelved = {
      id: "prop:shelved-rejected", kind: "proposition", statement: "a rejected partial proposition",
      depends_on: ["prop:aux"], status: "to-prove",
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        [shelved.id]: {
          proof_tex: "Rejected partial proof.",
          snapshot: { stmt: shelved.statement, depends_on: shelved.depends_on, defs: {}, assumptions: {} },
          node: shelved,
          owner: "thm:main",
          partial: true,
          shelved: true,
        },
      },
    });
    const calls: string[][] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        calls.push(targets.map((target) => target.id));
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls.flat()).not.toContain(shelved.id);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[shelved.id]).toMatchObject({ partial: true, shelved: true });
  });

  it("revokes a downstream chain proof when its intermediate postimage is inapplicable", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = { id: "lem:rollback-chain-helper", kind: "lemma", statement: "old rollback helper", depends_on: [], status: "to-prove" } as any;
    const bridge = { id: "lem:rollback-chain-bridge", kind: "lemma", statement: "old rollback bridge", depends_on: [], status: "to-prove" } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [helper.id]: {
          proof_tex: "Old helper proof.", snapshot: { stmt: helper.statement, depends_on: [], defs: {}, assumptions: {} },
          node: { ...helper, status: "proved", proof_tex: "Old helper proof." }, owner: "thm:stale-owner",
        },
        [bridge.id]: {
          proof_tex: "Old bridge proof.", snapshot: { stmt: bridge.statement, depends_on: [], defs: {}, assumptions: {} },
          node: { ...bridge, status: "proved", proof_tex: "Old bridge proof." }, owner: "thm:stale-owner",
        },
      },
    });
    await appendEscalationLog(ctx, {
      round: 4, changed: [], directive: "repair the root chain with one stale intermediate",
      require_core_changes: true, required_core_targets: ["thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        const claims = { root: "new rollback root", bridge: "new rollback bridge", helper: "new rollback helper" };
        await writeFile(outPath, JSON.stringify({
          proofs: ownsMain ? [
            { id: "thm:main", proof_tex: "New root proof.", argues_proposed: true },
            { id: bridge.id, proof_tex: "New bridge proof.", argues_proposed: true },
            { id: helper.id, proof_tex: "New helper proof.", argues_proposed: true },
          ] : targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
          proposed_statement_changes: ownsMain ? [
            { id: "thm:main", current: PROTO.statements[0].statement, proposed: claims.root, reason: "root", direction: "narrow" },
            { id: bridge.id, current: "a stale nonmatching bridge claim", proposed: claims.bridge, reason: "bridge", direction: "narrow" },
            { id: helper.id, current: helper.statement, proposed: claims.helper, reason: "helper", direction: "narrow" },
          ] : [],
          proposed_core_edits: ownsMain ? [
            {
              kind: "statement-replace", id: "thm:main",
              proposed: { ...PROTO.statements[0], statement: claims.root, depends_on: ["ass:overlap", bridge.id], free_symbols: [] },
              reason: "wire bridge", direction: "correct",
            },
            {
              kind: "statement-replace", id: bridge.id,
              proposed: { ...bridge, statement: claims.bridge, depends_on: [helper.id], free_symbols: [] },
              reason: "stale intermediate", direction: "correct", based_on_revision: `rev:${"0".repeat(64)}`,
            },
            {
              kind: "statement-replace", id: helper.id,
              proposed: { ...helper, statement: claims.helper, free_symbols: [] },
              reason: "downstream correction", direction: "correct",
            },
          ] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.proofs ?? [])
      .not.toContainEqual(expect.objectContaining({ id: helper.id, proof_tex: "New helper proof." }));
    expect(surfaced.statements ?? [])
      .not.toContainEqual(expect.objectContaining({ id: helper.id }));
    expect(surfaced.coreEdits ?? [])
      .not.toContainEqual(expect.objectContaining({ id: helper.id }));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id].proof_tex).toBe("Old helper proof.");
  });

  it("carries a recovered partial added-helper proof into provisional review", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:reviewed-recovered-helper",
      kind: "lemma",
      statement: "the recovered helper claim",
      depends_on: [],
      status: "to-prove",
    } as any;
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].depends_on = ["ass:overlap", helper.id];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [helper.id]: {
          proof_tex: "Historical partial helper proof.",
          snapshot: { stmt: helper.statement, depends_on: [], defs: {}, assumptions: {} },
          node: helper,
          owner: "thm:main",
          partial: true,
          shelved: true,
        },
      },
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        const ownsHelper = targets.some((target) => target.id === helper.id);
        const proposed = "tau is identified with the recovered helper";
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((target) => target.id !== helper.id)
            .map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.`, argues_proposed: ownsMain })),
          added_lemmas: ownsHelper ? [{ ...helper, status: "proved", proof_tex: "Complete reviewed helper proof." }] : [],
          proposed_statement_changes: ownsMain ? [{
            id: "thm:main", current: proto.statements[0].statement, proposed,
            reason: "narrow the root while retaining its helper", direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...proto.statements[0], statement: proposed, free_symbols: [] },
            reason: "publish the narrowed root", direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(result.status).toBe("checkpoint");
    expect((await readSurfacedProposals(ctx)).proofs).toContainEqual({
      id: helper.id,
      proof_tex: "Complete reviewed helper proof.",
    });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id]).toMatchObject({ partial: true });
  });

  it("does not replace shelved durable metadata through added_lemmas", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:shelved-added-identity", kind: "lemma", statement: "the durable old claim",
      depends_on: [], status: "to-prove",
    } as any;
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].depends_on = ["ass:overlap", helper.id];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [helper.id]: {
          proof_tex: "Historical partial proof.",
          snapshot: { stmt: helper.statement, depends_on: [], defs: {}, assumptions: {} },
          node: helper, owner: "thm:main", partial: true, shelved: true,
        },
      },
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((target) => target.id !== helper.id)
            .map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
          added_lemmas: ownsMain ? [{
            ...helper,
            free_symbols: ["invented_symbol"],
            status: "proved",
            proof_tex: "Proof under substituted metadata.",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id].node.statement).toBe(helper.statement);
    expect(working.solved[helper.id].proof_tex).toBe("Historical partial proof.");
    expect(JSON.stringify(working.solved[helper.id])).not.toContain("invented_symbol");
    expect(JSON.stringify(await readSurfacedProposals(ctx))).not.toContain("invented_symbol");
  });

  it("revokes a shelved helper proof when its enabling root postimage is inapplicable", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:postimage-only-helper",
      kind: "lemma",
      statement: "the postimage-only helper claim",
      depends_on: [],
      status: "to-prove",
    } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [helper.id]: {
          proof_tex: "Historical partial argument.",
          snapshot: { stmt: helper.statement, depends_on: [], defs: {}, assumptions: {} },
          node: helper,
          owner: "thm:historical",
          partial: true,
          shelved: true,
        },
      },
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        const proposed = "tau is identified on the narrowed postimage";
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.`, argues_proposed: ownsMain })),
            ...(ownsMain ? [{ id: helper.id, proof_tex: "Improperly retained helper proof." }] : []),
          ],
          proposed_statement_changes: ownsMain ? [{
            id: "thm:main",
            current: "tau is identified",
            proposed,
            reason: "test an inapplicable root postimage",
            direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace",
            id: "thm:main",
            proposed: {
              ...PROTO.statements[0], statement: proposed,
              depends_on: ["ass:overlap", helper.id], free_symbols: [],
            },
            reason: "stale root replacement must not mint helper authority",
            direction: "correct",
            based_on_revision: `rev:${"0".repeat(64)}`,
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id]).toMatchObject({
      partial: true,
      shelved: true,
      proof_tex: "Historical partial argument.",
    });
  });

  it("does not authorize downstream proofs from an incomplete semantic-owner postimage", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:incomplete-postimage-helper", kind: "lemma",
      statement: "the incomplete-postimage helper claim", depends_on: [], status: "to-prove",
    } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [helper.id]: {
          proof_tex: "Historical partial argument.",
          snapshot: { stmt: helper.statement, depends_on: [], defs: {}, assumptions: {} },
          node: helper, owner: "thm:historical", partial: true, shelved: true,
        },
      },
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        const proposed = "tau is identified through an incomplete postimage";
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsMain ? [{ id: helper.id, proof_tex: "Must not be authorized." }] : []),
          ],
          proposed_statement_changes: ownsMain ? [{
            id: "thm:main", current: PROTO.statements[0].statement, proposed,
            reason: "exercise an incomplete proof transaction", direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...PROTO.statements[0], statement: proposed, depends_on: ["ass:overlap", helper.id], free_symbols: [] },
            reason: "the postimage lacks an argues_proposed proof", direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect((await readSurfacedProposals(ctx)).proofs ?? [])
      .not.toContainEqual(expect.objectContaining({ id: helper.id }));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id]).toMatchObject({
      partial: true, shelved: true, proof_tex: "Historical partial argument.",
    });
  });

  it("does not let a sibling correction bootstrap the owner's shelved proof", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "lem:shelved-bootstrap",
      kind: "lemma",
      statement: "the historical broad claim",
      depends_on: [],
      status: "to-prove",
    } as any;
    const leaf = {
      id: "lem:sibling-minted-leaf",
      kind: "lemma",
      statement: "the downstream leaf claim",
      depends_on: [],
      status: "to-prove",
    } as any;
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].depends_on = ["ass:overlap", carried.id];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [carried.id]: {
          proof_tex: "Historical partial argument.",
          snapshot: { stmt: carried.statement, depends_on: [], defs: {}, assumptions: {} },
          node: carried,
          owner: "thm:main",
          partial: true,
          shelved: true,
        },
        [leaf.id]: {
          proof_tex: "Historical leaf fragment.",
          snapshot: { stmt: leaf.statement, depends_on: [], defs: {}, assumptions: {} },
          node: leaf,
          owner: "thm:main",
          partial: true,
          shelved: true,
        },
      },
    });
    const proposed = "the sibling's narrower claim";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets
              .filter((target) => target.id !== carried.id && target.id !== leaf.id)
              .map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsMain
              ? [{ id: leaf.id, proof_tex: "Owner's newly reachable leaf proof." }]
              : [{ id: carried.id, proof_tex: "Sibling correction proof.", argues_proposed: true }]),
          ],
          proposed_statement_changes: ownsMain ? [] : [{
            id: carried.id,
            current: carried.statement,
            proposed,
            reason: "unauthorized sibling correction",
            direction: "narrow",
          }],
          proposed_core_edits: ownsMain ? [] : [{
            kind: "statement-replace",
            id: carried.id,
            proposed: { ...carried, statement: proposed, depends_on: [leaf.id], free_symbols: [] },
            reason: "unauthorized sibling replacement",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    // An existing id the emitter does not own is an OWNERSHIP withhold, not an id fault.
    expect(String((result as { message?: string }).message ?? "")).toMatch(/OWNERSHIP.*lem:shelved-bootstrap.*owner/i);
    expect(String((result as { message?: string }).message ?? "")).not.toMatch(/named no core statement/);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[carried.id]).toMatchObject({ partial: true });
    expect(working.solved[carried.id].proof_tex).toBe("Historical partial argument.");
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.statements ?? []).not.toContainEqual(expect.objectContaining({ id: carried.id }));
    expect(surfaced.coreEdits ?? []).not.toContainEqual(expect.objectContaining({ id: carried.id }));
    expect(surfaced.proofs ?? []).not.toContainEqual(expect.objectContaining({ id: carried.id }));
    expect(surfaced.proofs ?? []).not.toContainEqual(expect.objectContaining({ id: leaf.id }));
  });

  it("fails closed on byte-identical complete correction transactions from two units", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "lem:duplicate-correction", kind: "lemma", statement: "the old duplicate claim",
      depends_on: [], status: "to-prove",
    } as any;
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].depends_on = ["ass:overlap", carried.id];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [carried.id]: {
          proof_tex: "Old partial proof.",
          snapshot: { stmt: carried.statement, depends_on: [], defs: {}, assumptions: {} },
          node: carried, owner: "thm:main", partial: true, shelved: true,
        },
      },
    });
    const proposed = "the identical narrowed duplicate claim";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            { id: carried.id, proof_tex: "Identical correction proof.", argues_proposed: true },
          ],
          proposed_statement_changes: [{
            id: carried.id, current: carried.statement, proposed,
            reason: "identical cross-unit correction", direction: "narrow",
          }],
          proposed_core_edits: [{
            kind: "statement-replace", id: carried.id,
            proposed: { ...carried, statement: proposed, free_symbols: [] },
            reason: "identical cross-unit replacement", direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.statements ?? []).not.toContainEqual(expect.objectContaining({ id: carried.id }));
    expect(surfaced.coreEdits ?? []).not.toContainEqual(expect.objectContaining({ id: carried.id }));
    expect(surfaced.proofs ?? []).not.toContainEqual(expect.objectContaining({ id: carried.id }));
  });

  it("does not let a no-op correction revive the owner's shelved proof", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "lem:no-op-revival",
      kind: "lemma",
      statement: "the unchanged historical claim",
      depends_on: [],
      status: "to-prove",
    } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [carried.id]: {
          proof_tex: "Historical partial argument.",
          snapshot: { stmt: carried.statement, depends_on: [], defs: {}, assumptions: {} },
          node: carried,
          owner: "thm:main",
          partial: true,
          shelved: true,
        },
      },
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsMain ? [{ id: carried.id, proof_tex: "Improperly revived proof.", argues_proposed: true }] : []),
          ],
          proposed_statement_changes: ownsMain ? [{
            id: carried.id,
            current: carried.statement,
            proposed: carried.statement,
            reason: "no-op correction",
            direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace",
            id: carried.id,
            proposed: { ...carried, free_symbols: [] },
            reason: "no-op replacement",
            direction: "correct",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /proof lem:no-op-revival sets argues_proposed=true but has 0 complete claim-change transaction\(s\)/i,
    );
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[carried.id]).toMatchObject({ partial: true, shelved: true });
    expect(working.solved[carried.id].proof_tex).toBe("Historical partial argument.");
  });

  it("restores current-round invalidation rather than a stale full prior record", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "lem:invalidated-before-merge",
      kind: "lemma",
      statement: "the previously proved agent claim",
      depends_on: ["def:env"],
      status: "proved",
      proof_tex: "Previously complete proof.",
    } as any;
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        [carried.id]: {
          proof_tex: carried.proof_tex,
          snapshot: {
            stmt: carried.statement,
            depends_on: carried.depends_on,
            defs: { "def:env": "a stale construction" },
            assumptions: {},
          },
          node: carried,
          owner: "thm:main",
        },
      },
    });
    const proposed = "the substantively narrowed agent claim";
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsMain ? [{ id: carried.id, proof_tex: "Proof against an inapplicable replacement.", argues_proposed: true }] : []),
          ],
          proposed_statement_changes: ownsMain ? [{
            id: carried.id,
            current: carried.statement,
            proposed,
            reason: "substantive narrowing",
            direction: "narrow",
          }] : [],
          proposed_core_edits: ownsMain ? [{
            kind: "statement-replace",
            id: carried.id,
            proposed: { ...carried, statement: proposed, status: "to-prove", proof_tex: undefined, free_symbols: [] },
            reason: "stale replacement revision",
            direction: "correct",
            based_on_revision: `rev:${"0".repeat(64)}`,
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[carried.id]).toMatchObject({ partial: true, shelved: true });
    expect(working.solved[carried.id].proof_tex).toBe("Previously complete proof.");
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.some((statement: any) => statement.id === carried.id)).toBe(false);
  });

  it("lets the durable owner refresh an undispatched published agent proof", async () => {
    const ctx = makeCtx(repoRoot);
    const carried = {
      id: "lem:published-agent",
      kind: "lemma",
      statement: "the published agent claim",
      depends_on: [],
      status: "proved",
      proof_tex: "Old serialized proof.",
    } as any;
    await saveWorkingState(ctx, {
      round: 5,
      solved: {
        [carried.id]: {
          proof_tex: carried.proof_tex,
          snapshot: { stmt: carried.statement, depends_on: [], defs: {}, assumptions: {} },
          node: carried,
          owner: "thm:main",
        },
      },
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some((target) => target.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
            ...(ownsMain ? [{ id: carried.id, proof_tex: "Corrected serialized proof." }] : []),
          ],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).not.toHaveProperty("status");
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[carried.id].proof_tex).toBe("Corrected serialized proof.");
  });

  it("records a skipped reason when an already-present assumption is selected for apply", async () => {
    // The silent `continue` on an existing assumption id recorded nothing, so the
    // partial-apply refusal fired with "No per-edit reason was recorded" — an
    // undiagnosable dead end the error message itself calls a gap.
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, {
      assumptions: [{
        id: "ass:overlap",
        condition: "the propensity is bounded away from 0 and 1",
        reason: "echo of a standing assumption",
        standard_or_novel: "standard: Rosenbaum1983",
        not_crux: "background condition",
      }],
    });
    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/ass:overlap.*already/i);
  });

  it("records a skipped reason for an inapplicable definition-replace core edit", async () => {
    // definition-add/replace/delete and missing-target statement-delete previously
    // skipped silently, leaving the partial-apply refusal with no per-edit reason.
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, {
      coreEdits: [{
        kind: "definition-replace",
        id: "def:ghost",
        proposed: { id: "def:ghost", name: "G", construction: "G = 1", inputs: [] },
        reason: "correct a definition that does not exist",
        direction: "correct",
      }],
    });
    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/def:ghost.*no frozen definition/i);
  });

  it("surfaces open obligations alongside a proposal checkpoint instead of discarding them", async () => {
    // finalizeRound writes open_obligations.json, but a round that ALSO proposes a
    // change halts earlier at surfaceProposalCheckpoint — which used to drop the
    // obligation texts entirely, so the orchestrator adjudicated the proposals never
    // knowing an obstruction had been isolated, and the next round re-paid for it.
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const hasMain = targets.some((t) => t.id === "thm:main");
        await writeFile(outPath, JSON.stringify(withCorrectionPairs({
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          proposed_statement_changes: hasMain
            ? [{ id: "thm:main", current: "tau is identified", proposed: "tau is identified on the overlap region", reason: "needs overlap", direction: "narrow" }]
            : [],
          open_obligations: hasMain
            ? [{ node_id: "thm:main", what_is_open: "the full-support case", obstruction: "no bound without overlap", attempted: "direct decomposition" }]
            : [],
        })), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect((result as { status?: string }).status).toBe("checkpoint");
    expect(String((result as { message?: string }).message ?? "")).toMatch(/OPEN OBLIGATION/i);
    const obPath = path.join(path.dirname(coreJsonPath(ctx)), "open_obligations.json");
    expect(existsSync(obPath), "the obligation texts must survive the proposal checkpoint").toBe(true);
    const obligations = JSON.parse(await readFile(obPath, "utf8"));
    expect(obligations[0]).toMatchObject({ node_id: "thm:main", obstruction: "no bound without overlap" });

    // A later round with ZERO obligations must clear the stale file (only the apply
    // path swept it before), or the old diagnostics keep presenting as current.
    const cleanDeps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const clean = await runStage0Solve({ ctx, state: makeState(), deps: cleanDeps });
    expect("status" in clean, "the follow-up round must discharge cleanly").toBe(false);
    expect(existsSync(obPath), "a zero-obligation round must clear the stale file").toBe(false);
  });

  it("rejects a sibling proof for a round-added lemma and keeps the installer's bytes", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const isMainUnit = targets.some((t) => t.id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          // Whichever unit is NOT the installer supplies the shared helper's proof.
          proofs: [
            ...targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
            ...(isMainUnit ? [] : [{ id: "lem:cross-helper", proof_tex: "Proved by the sibling unit." }]),
          ],
          added_lemmas: isMainUnit
            ? [{ id: "lem:cross-helper", kind: "lemma", statement: "the cross-unit helper claim",
                 depends_on: [], status: "proved", proof_tex: "Proved by the installing unit." }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(String((result as { message?: string }).message ?? "")).toMatch(/OWNERSHIP.*lem:cross-helper.*owner/);
    expect(String((result as { message?: string }).message ?? "")).not.toMatch(/named no core statement/);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const rec = working.solved["lem:cross-helper"];
    expect(rec?.node, "the agent-added lemma must keep its catalog node definition").toBeDefined();
    expect(rec?.node?.id).toBe("lem:cross-helper");
    expect(rec?.proof_tex).toBe("Proved by the installing unit.");
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "lem:cross-helper")?.status).toBe("proved");
  });

  it("remaps a PARTIAL record's dependency edges when the OEQ it cites is resolved", async () => {
    // The OEQ transition remaps core deps, but the working records were remapped only as
    // a side effect of refreshSnapshots — which now skips partials (to preserve the
    // argued basis). A partial's catalog node therefore kept the dead `oeq:` edge, and
    // the NEXT round re-opened it via openSolveTarget carrying that edge: the merge
    // dangling-edge check then threw AFTER a full paid dispatch, every round, until the
    // solve cap. An id remap is not a basis retarget — it must reach partials too.
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:rate", kind: "openendedquestion", statement: "What is the sharp rate?",
      depends_on: ["ass:overlap"], status: "to-prove",
      justification: "open rate question", gap: "vs prior", consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");

    // Round 1: add an agent lemma that DEPENDS on the open oeq and leave it unproved,
    // so it is carried as a partial record with its own catalog node.
    const addHelper: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((t) => !t.id.startsWith("oeq:")).map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: targets.some((t) => t.id === "thm:main")
            ? [{ id: "lem:rate-helper", kind: "lemma", statement: "a helper about the rate",
                 depends_on: ["oeq:rate"], status: "to-prove" }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStage0Solve({ ctx, state: makeState(), deps: addHelper });
    const afterRound1 = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(afterRound1.solved["lem:rate-helper"]?.partial, "helper must be carried as a partial").toBe(true);
    expect(afterRound1.solved["lem:rate-helper"]?.node?.depends_on).toEqual(["oeq:rate"]);

    // Round 2: resolve the oeq. The partial's catalog edge must follow the replacement.
    const resolveOeq: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const hasOeq = targets.some((t) => t.id === "oeq:rate");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((t) => !t.id.startsWith("oeq:") && t.id !== "lem:rate-helper")
            .map((t) => ({ id: t.id, proof_tex: "QED." })),
          resolved_oeqs: hasOeq
            ? [{ source_id: "oeq:rate", theorem: {
                id: "thm:sharp-rate", kind: "theorem", statement: "The sharp rate is n^{-1/2}.",
                depends_on: ["ass:overlap"], status: "proved", proof_tex: "By the two-point bound." } }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStage0Solve({ ctx, state: makeState(), deps: resolveOeq });

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const helper = working.solved["lem:rate-helper"];
    expect(helper?.node?.depends_on, "the partial's catalog edge must follow the OEQ replacement")
      .toEqual(["thm:sharp-rate"]);
    expect(helper?.node?.depends_on).not.toContain("oeq:rate");
  });

  it("does not misfile a proofs[] re-emission for a resolved-OEQ answer theorem as unmatched", async () => {
    // roundEmittedIds includes resolved_oeqs theorem ids, but those nodes are only
    // installed by the OEQ-transition block late in merge — a parked proof drained
    // before that saw no target and reported a "PLUMBING FAULT: unmatched id" on a
    // clean round. The final drain runs after the transition; the redundant copy is
    // classified as a duplicate re-proof of the settled answer theorem.
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO);
    proto.statements.push({
      id: "oeq:rate",
      kind: "openendedquestion",
      statement: "What is the sharp rate?",
      depends_on: ["ass:overlap"],
      status: "to-prove",
      justification: "open rate question",
      gap: "vs prior",
      consumer: "applied",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const hasOeq = targets.some((t) => t.id === "oeq:rate");
        await writeFile(outPath, JSON.stringify({
          proofs: [
            ...targets.filter((t) => t.id !== "oeq:rate").map((t) => ({ id: t.id, proof_tex: "QED." })),
            ...(hasOeq ? [{ id: "thm:sharp-rate", proof_tex: "The rate follows from the two-point bound." }] : []),
          ],
          resolved_oeqs: hasOeq
            ? [{
                source_id: "oeq:rate",
                theorem: {
                  id: "thm:sharp-rate", kind: "theorem", statement: "The sharp rate is n^{-1/2}.",
                  depends_on: ["ass:overlap"], status: "proved",
                  proof_tex: "The rate follows from the two-point bound.",
                },
              }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(String((result as { message?: string }).message ?? "")).not.toMatch(/PLUMBING FAULT/);
    expect("status" in result, "the redundant re-emission must not checkpoint a clean round").toBe(false);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:sharp-rate")).toMatchObject({ status: "proved" });
    expect(core.statements.find((s: any) => s.id === "oeq:rate")).toBeUndefined();
  });

  it("persists the solve-round budget before dispatch so a thrown round still consumes it", async () => {
    // A merge-gate throw escapes runStage0Typed without the driver saving state, so an
    // in-memory-only counter increment made every failed retry budget-free — the
    // d0_loop_cap_hit circuit breaker could never trip on a repeated mechanical abort.
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "correct the estimator definition, then re-prove the main theorem",
      require_core_changes: true,
      required_core_targets: ["thm:main"],
    });

    await expect(runStage0Typed({
      ctx,
      state: makeState(),
      deps: solverDeps("propose-def"),
    })).rejects.toThrow(/required exact structured target/i);

    const persisted = JSON.parse(await readFile(statePath(repoRoot, QID, SPEC), "utf8"));
    expect(persisted.flags.d0_loop_counters.solve_rounds).toBe(1);
  });

  it("accepts and applies a typed addition of a genuinely new definition", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "add the missing replicated frontier definition",
      require_core_changes: true,
      required_core_targets: ["def:replicated-frontier"],
    });
    let agentReproofCalls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const targetBlock = (prompt.split("=== TARGET STATEMENT(S) TO SOLVE")[1] ?? "")
          .split("SOLVE_OUTPUT_PATH")[0];
        const reproveAgentNodes = targetBlock.includes('"id": "thm:replicated-boundary"');
        const definitionAlreadyFrozen = prompt.includes('"id": "def:replicated-frontier"');
        const canonicalDirectiveOwner = prompt.includes(
          "You are the ONLY solve unit allowed to emit directive-wide shared payloads",
        );
        if (reproveAgentNodes) agentReproofCalls += 1;
        await writeFile(outPath, JSON.stringify(reproveAgentNodes ? {
          proofs: [
            { id: "lem:replicated-separator", proof_tex: "The corrected frontier admits the separator." },
            { id: "thm:replicated-boundary", proof_tex: "Apply the corrected separator." },
          ],
          added_lemmas: [], proposed_core_edits: [],
        } : definitionAlreadyFrozen ? {
          proofs: [
            { id: "thm:main", proof_tex: "QED after the definition was frozen." },
            { id: "prop:aux", proof_tex: "Auxiliary result after the definition was frozen." },
          ],
          added_lemmas: [], proposed_core_edits: [],
        } : !canonicalDirectiveOwner ? {
          proofs: [{ id: "prop:aux", proof_tex: "Auxiliary result while the canonical owner emits the shared definition." }],
          added_lemmas: [], proposed_core_edits: [],
        } : {
          proofs: [{ id: "thm:main", proof_tex: "QED." }],
          added_lemmas: [
            {
              id: "lem:replicated-separator", kind: "lemma", statement: "A separator exists.",
              depends_on: ["def:replicated-frontier"], status: "proved", proof_tex: "Separate the sets.",
            },
            {
              id: "thm:replicated-boundary", kind: "theorem", statement: "The replicated boundary is sharp.",
              depends_on: ["lem:replicated-separator"], status: "proved", proof_tex: "Apply the separator.",
            },
          ],
          proposed_core_edits: [{
            kind: "definition-add",
            id: "def:replicated-frontier",
            proposed: {
              id: "def:replicated-frontier",
              name: "replicated all-tests frontier",
              construction: "beta_rep is the supremum over all level-alpha randomized tests",
              inputs: ["ass:overlap"],
            },
            reason: "the strengthened theorem needs a named formal object",
            direction: "correct",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    await applyProposedChanges({ ctx });
    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.definitions.find((d: any) => d.id === "def:replicated-frontier")).toMatchObject({
      name: "replicated all-tests frontier",
      inputs: ["ass:overlap"],
    });
    const pending = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(pending.solved["thm:replicated-boundary"].partial).toBeUndefined();
    expect(pending.solved["lem:replicated-separator"].partial).toBeUndefined();

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(agentReproofCalls).toBe(0);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:replicated-boundary")).toMatchObject({
      status: "proved",
      proof_tex: "Apply the separator.",
    });
    expect(core.statements.find((s: any) => s.id === "lem:replicated-separator")).toMatchObject({
      status: "proved",
      proof_tex: "Separate the sets.",
    });

  });

  it("accepts statement-delete at the structured solver-output boundary", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements[1].depends_on = ["thm:main"];
    proto.statements[1].consumer = "canonical downstream applications";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "prop:aux", proof_tex: "The canonical proposition is enough." }],
          proposed_core_edits: [{
            kind: "statement-delete",
            id: "thm:main",
            replacement_id: "prop:aux",
            reason: "the headline is an obsolete duplicate",
            direction: "delete-obsolete",
          }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const edits = (await readSurfacedProposals(ctx)).coreEdits;
    expect(edits).toEqual([expect.objectContaining({
      kind: "statement-delete",
      id: "thm:main",
      replacement_id: "prop:aux",
    })]);
  });

  it("carries an orchestrator-mandated delete even when its owner re-proves the obsolete target", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements[1].depends_on = ["ass:overlap"];
    proto.statements[1].consumer = "canonical downstream applications";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const requiredEdit = {
      kind: "statement-delete" as const,
      id: "thm:main",
      replacement_id: "prop:aux",
      reason: "independently adjudicated obsolete duplicate",
      direction: "delete-obsolete" as const,
    };
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "delete the obsolete headline in favor of the canonical proposition",
      require_core_changes: true,
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto,
        working: null,
        edit: requiredEdit,
        proposalRevision: "angle:0/version:1",
      })],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const targetBlock = (prompt.split("=== TARGET STATEMENT(S) TO SOLVE")[1] ?? "")
          .split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(
          targetBlock.slice(targetBlock.indexOf("["), targetBlock.lastIndexOf("]") + 1),
        ) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          // Reproduces the live defect: the semantic owner follows the generic
          // prove-target instruction instead of the requested deletion.
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `Reproved ${target.id}.` })),
          proposed_core_edits: [{ ...requiredEdit, reason: "worker rationale must not replace canonical provenance" }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const state = makeVersionedState();
    const result = await runStage0Solve({ ctx, state, deps });
    expect(result).toHaveProperty("status", "checkpoint");
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.coreEdits).toContainEqual(expect.objectContaining({
      kind: "statement-delete",
      id: "thm:main",
      replacement_id: "prop:aux",
    }));
    expect(surfaced.proofs ?? []).not.toContainEqual(expect.objectContaining({ id: "thm:main" }));
    const assembled = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(assembled.statements.find((statement: any) => statement.id === "thm:main").proof_tex).toBeUndefined();
    const workingAfterFirst = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(workingAfterFirst.required_core_edit_mandates).toHaveLength(1);
    const mandateId = workingAfterFirst.required_core_edit_mandates[0].mandate_id;
    expect(surfaced.coreEdits).toHaveLength(1);
    const packet = JSON.parse(await readFile(proposalReviewPacketPath(ctx), "utf8"));
    expect(packet.required_core_edit_mandates).toEqual([
      expect.objectContaining({ mandate_id: mandateId }),
    ]);
    await expect(discardAllProposedChanges({ ctx, note: "reject everything" })).rejects.toThrow(/required core edits/i);
    await expect(applyProposedChanges({ ctx, ids: new Set(["statement:prop:aux"]) })).rejects.toThrow(/mandated edits apply atomically/i);

    // The journal row is now consumed; durability must come from the working cursor.
    await runStage0Solve({ ctx, state, deps });
    const workingAfterSecond = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(workingAfterSecond.required_core_edit_mandates).toEqual([
      expect.objectContaining({ mandate_id: mandateId }),
    ]);
    expect((await readSurfacedProposals(ctx)).coreEdits).toHaveLength(1);
    const archived = await readProofArchiveIndex(path.dirname(coreJsonPath(ctx)));
    expect(archived).toContainEqual(expect.objectContaining({
      node_id: "thm:main",
      reason: "mandated-delete",
    }));

    await applyProposedChanges({ ctx });
    const appliedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(appliedProto.statements.some((statement: any) => statement.id === "thm:main")).toBe(false);
    const workingAfterApply = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(workingAfterApply.required_core_edit_mandates).toEqual([]);
  });

  it("quarantines open against a mandated delete while committing an unrelated proof", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.push({
      id: "lem:mandate-unrelated", kind: "lemma", statement: "an unrelated result survives",
      depends_on: ["ass:overlap"], status: "to-prove",
      justification: "regression witness", gap: "none", consumer: "test",
    });
    // This fixture represents a deletion already adjudicated as safe.  The base
    // PROTO's auxiliary node names thm:main in authored prose, which would make
    // deleting thm:main a claim/prose edit rather than a dependency remap.
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "downstream";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const requiredEdit = {
      kind: "statement-delete" as const,
      id: "thm:main",
      replacement_id: "prop:aux",
      reason: "independently adjudicated obsolete duplicate",
      direction: "delete-obsolete" as const,
    };
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "delete the obsolete headline and preserve unrelated progress",
      require_core_changes: true,
      required_core_targets: ["lem:mandate-unrelated"],
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto,
        working: null,
        edit: requiredEdit,
        proposalRevision: "angle:0/version:1",
      })],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          open_obligations: ownsMain ? [{
            node_id: "thm:main",
            what_is_open: "the obsolete headline remains unresolved",
            obstruction: "a worker-side objection to the deletion",
            attempted: "the old proof route",
            partial_result: "Partial obsolete proof.",
          }] : [],
          proposed_core_edits: ownsMain ? [requiredEdit] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeVersionedState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "lem:mandate-unrelated")?.status)
      .toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toContainEqual(expect.objectContaining({
      category: "open-obligation",
      target: "thm:main",
      reason: "mandate-shadowed",
      payload: expect.objectContaining({ partial_result: "Partial obsolete proof." }),
    }));
    const checkpointWorking = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(checkpointWorking.escalation_entries_consumed).toBe(1);

    await applyProposedChanges({ ctx });
    expect(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")).statements
      .some((statement: any) => statement.id === "thm:main")).toBe(false);
    const appliedWorking = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(appliedWorking.required_core_edit_mandates).toEqual([]);
    expect(appliedWorking.escalation_entries_consumed).toBe(1);

    // Restart must not replay the already-applied mandate against its changed
    // target snapshot merely because worker noise on that target was archived.
    await expect(runStage0Solve({ ctx, state: makeVersionedState(), deps })).resolves.toBeDefined();
  });

  it("preserves and applies a metadata-only mandated statement replacement", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const edit = {
      kind: "statement-replace" as const,
      id: "thm:main",
      proposed: { ...proto.statements[0], consumer: "revised canonical consumer" },
      reason: "independently adjudicated metadata repair",
      direction: "correct" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto,
      working: null,
      edit,
      proposalRevision: "angle:0/version:1",
    });
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair the theorem metadata",
      require_core_changes: true,
      required_core_edit_mandates: [mandate],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:main", proof_tex: "Worker proof against the old metadata." }],
          proposed_core_edits: [{ ...edit, reason: "worker rationale" }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStage0Solve({ ctx, state: makeVersionedState(), deps });
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.coreEdits).toEqual([expect.objectContaining({
      kind: "statement-replace", id: "thm:main", reason: edit.reason,
    })]);
    expect(surfaced.statements).toEqual([]);
    const archived = await readProofArchiveIndex(path.dirname(coreJsonPath(ctx)));
    expect(archived).toContainEqual(expect.objectContaining({
      node_id: "thm:main", reason: "mandated-statement-replace",
    }));
    await applyProposedChanges({ ctx });
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.statements.find((statement: any) => statement.id === "thm:main").consumer)
      .toBe("revised canonical consumer");
  });

  it("round-trips and applies a metadata-only mandated definition replacement", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "definition-replace" as const,
      id: "def:env",
      proposed: { ...proto.definitions[0], name: "revised envelope" },
      reason: "independently adjudicated definition metadata repair",
      direction: "correct" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
    });
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "repair the definition metadata", require_core_changes: true,
      required_core_edit_mandates: [mandate],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:main", proof_tex: "Worker proof against unchanged construction." }],
          proposed_core_edits: [{ ...edit, reason: "worker rationale" }],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeVersionedState(), deps });
    const surfaced = await readSurfacedProposals(ctx) as any;
    expect(surfaced.coreEdits).toEqual([expect.objectContaining({
      kind: "definition-replace", id: "def:env", reason: edit.reason,
    })]);
    expect(surfaced.definitions).toEqual([]);
    expect(surfaced.basis_revision).toMatch(/^rev:[a-f0-9]{64}$/);
    await applyProposedChanges({ ctx });
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.definitions.find((definition: any) => definition.id === "def:env"))
      .toMatchObject({ name: "revised envelope", construction: "U = a" });
  });

  it("round-trips and applies a construction-changing mandated definition replacement without a worker substitute", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "definition-replace" as const,
      id: "def:env",
      proposed: { ...proto.definitions[0], construction: "U = a + b" },
      reason: "independently adjudicated construction correction",
      direction: "correct" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
    });
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "correct the definition construction", require_core_changes: true,
      required_core_edit_mandates: [mandate],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(
          segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1),
        ) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((target) => ({ id: target.id, proof_tex: `Proved ${target.id}.` })),
          proposed_core_edits: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeVersionedState(), deps });
    const surfaced = await readSurfacedProposals(ctx) as any;
    expect(surfaced.coreEdits).toEqual([expect.objectContaining({
      kind: "definition-replace", id: "def:env", reason: edit.reason,
    })]);
    expect(surfaced.definitions).toEqual([]);
    expect(surfaced.basis_revision).toMatch(/^rev:[a-f0-9]{64}$/);
    await applyProposedChanges({ ctx });
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.definitions.find((definition: any) => definition.id === "def:env").construction)
      .toBe("U = a + b");
  });

  it("applies a claim change with its paired structural statement replacement", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const proposedStatement = "tau is identified on the overlap region";
    await saveWorkingState(ctx, {
      round: 1, solved: {},
      proposals: {
        statements: [{
          id: "thm:main", current: proto.statements[0].statement,
          proposed: proposedStatement, reason: "narrow the claim", direction: "narrow",
        }],
        definitions: [], assumptions: [],
        coreEdits: [{
          kind: "statement-replace", id: "thm:main",
          proposed: { ...proto.statements[0], statement: proposedStatement, consumer: "revised consumer" },
          reason: "synchronize structural metadata", direction: "correct",
        }],
        proofs: [],
      },
    });
    await expect(applyProposedChanges({ ctx })).resolves.toHaveLength(2);
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.statements.find((statement: any) => statement.id === "thm:main"))
      .toMatchObject({ statement: proposedStatement, consumer: "revised consumer", status: "to-prove" });
  });

  it("applies a paired claim+structural replacement echoing the assembled settled-overlay view", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const frozen = proto.statements[0];
    const proposedStatement = "tau is identified on the overlap region";
    await saveWorkingState(ctx, {
      round: 1,
      solved: {
        "thm:main": {
          proof_tex: "Settled proof of the frozen claim.",
          snapshot: {
            stmt: frozen.statement, depends_on: frozen.depends_on, defs: {},
            assumptions: { "ass:overlap": PROTO.assumptions[0].condition },
          },
          node: { ...frozen, status: "proved", proof_tex: "Settled proof of the frozen claim." },
        },
      },
      proposals: {
        statements: [{
          id: "thm:main", current: frozen.statement,
          proposed: proposedStatement, reason: "narrow the claim", direction: "narrow",
        }],
        definitions: [], assumptions: [],
        coreEdits: [{
          kind: "statement-replace", id: "thm:main",
          // The paired metadata is authored against the post-change claim while its
          // revision still pins the assembled settled view the solver saw.
          proposed: { ...frozen, statement: proposedStatement, status: "to-prove", consumer: "revised consumer" },
          reason: "synchronize structural metadata", direction: "correct",
        }],
        proofs: [],
      },
    });
    await expect(applyProposedChanges({ ctx })).resolves.toHaveLength(2);
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.statements.find((statement: any) => statement.id === "thm:main"))
      .toMatchObject({ statement: proposedStatement, consumer: "revised consumer", status: "to-prove" });
  });

  it("allows an exact reviewed cancellation to retire one mandate while preserving every other mandate", () => {
    const proto = structuredClone(PROTO) as any;
    const first = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: { kind: "statement-delete", id: "thm:main", reason: "rejected edit", direction: "delete-obsolete" },
      proposalRevision: "angle:0/version:1",
    });
    const second = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: { kind: "statement-delete", id: "prop:aux", reason: "accepted edit", direction: "delete-obsolete" },
      proposalRevision: "angle:0/version:1",
    });
    const cancellation = makeRequiredCoreEditMandateCancellation({
      mandateId: first.mandate_id,
      reason: "mandatory reviewer rejected stale metadata in the frozen edit",
    });
    expect(resolveRequiredCoreEditMandates({
      mandates: [first, second], cancellations: [cancellation], core: proto, working: null,
      proposalRevision: "angle:0/version:1",
    })).toEqual([second]);
  });

  it("refuses a cancellation that names no outstanding exact mandate", () => {
    const proto = structuredClone(PROTO) as any;
    const cancellation = makeRequiredCoreEditMandateCancellation({
      mandateId: `d0m:${"0".repeat(64)}`,
      reason: "attempt to clear an unrelated mandate",
    });
    expect(() => resolveRequiredCoreEditMandates({
      mandates: [], cancellations: [cancellation], core: proto, working: null,
      proposalRevision: "angle:0/version:1",
    })).toThrow(/names no outstanding mandate/i);
  });

  it("permits audited discard after the sole exact mandate is cancelled", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "statement-delete" as const, id: "thm:main",
      reason: "later review rejected this frozen edit", direction: "delete-obsolete" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
    });
    await saveWorkingState(ctx, {
      round: 2, proposal_revision: "angle:0/version:1", escalation_entries_consumed: 0, solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [edit], proofs: [] },
      required_core_edit_mandates: [mandate],
    });
    await appendEscalationLog(ctx, {
      round: 2, changed: [], provenance_only: true,
      cancelled_core_edit_mandates: [makeRequiredCoreEditMandateCancellation({
        mandateId: mandate.mandate_id,
        reason: "mandatory reviewer rejected stale metadata in the frozen edit",
      })],
    });
    await expect(discardAllProposedChanges({ ctx, note: "mandatory review rejected the stale bundle" }))
      .resolves.toBe(1);
    expect((await readEscalationLog(ctx)).at(-1)?.note).toMatch(/DISCARDED ALL 1/);
  });

  it("round-trips a mandate and its cancellation through the persisted escalation journal bytes", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: { kind: "statement-delete", id: "thm:main", reason: "rejected edit", direction: "delete-obsolete" },
      proposalRevision: "angle:0/version:1",
    });
    await appendEscalationLog(ctx, {
      round: 2, changed: [], provenance_only: true,
      required_core_edit_mandates: [mandate],
    });
    await appendEscalationLog(ctx, {
      round: 2, changed: [], provenance_only: true,
      cancelled_core_edit_mandates: [makeRequiredCoreEditMandateCancellation({
        mandateId: mandate.mandate_id,
        reason: "mandatory reviewer rejected the exact edit",
      })],
    });
    // Integrity hashes must verify against what was actually persisted and re-read,
    // not against the in-memory objects that produced them: writer/reader
    // canonicalization drift is exactly the live-resume failure class.
    const journal = await readEscalationLog(ctx);
    const persistedMandates = journal.flatMap((entry) => entry.required_core_edit_mandates ?? []);
    const persistedCancellations = journal.flatMap((entry) => entry.cancelled_core_edit_mandates ?? []);
    expect(persistedMandates).toHaveLength(1);
    expect(persistedCancellations).toHaveLength(1);
    expect(resolveRequiredCoreEditMandates({
      mandates: persistedMandates, cancellations: persistedCancellations, core: proto, working: null,
      proposalRevision: "angle:0/version:1",
    })).toEqual([]);
  });

  it("refuses to delete a mandated replacement endpoint in the same atomic bundle", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const mandatedDelete = {
      kind: "statement-delete" as const,
      id: "thm:main",
      replacement_id: "prop:aux",
      reason: "replace the obsolete headline by the canonical endpoint",
      direction: "delete-obsolete" as const,
    };
    const endpointDelete = {
      kind: "statement-delete" as const,
      id: "prop:aux",
      reason: "adversarial worker deletion of the endpoint",
      direction: "delete-obsolete" as const,
    };
    await saveWorkingState(ctx, {
      round: 2,
      proposal_revision: "angle:0/version:1",
      escalation_entries_consumed: 0,
      solved: {},
      proposals: {
        statements: [], definitions: [], assumptions: [],
        coreEdits: [mandatedDelete, endpointDelete], proofs: [],
      },
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto, working: null, edit: mandatedDelete,
        proposalRevision: "angle:0/version:1",
      })],
    });
    await expect(applyProposedChanges({ ctx }))
      .rejects.toThrow(/stable surviving replacement endpoint/i);
    const unchanged = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(unchanged.statements.some((statement: any) => statement.id === "thm:main")).toBe(true);
    expect(unchanged.statements.some((statement: any) => statement.id === "prop:aux")).toBe(true);
  });

  it("applies a mandated A-to-B deletion with the reviewed dependency cleanup of B", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const endpoint = proto.statements.find((statement: any) => statement.id === "prop:aux");
    endpoint.depends_on = ["thm:main"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const mandatedDelete = {
      kind: "statement-delete" as const, id: "thm:main", replacement_id: "prop:aux",
      reason: "replace obsolete headline", direction: "delete-obsolete" as const,
    };
    const endpointCleanup = {
      kind: "statement-replace" as const, id: "prop:aux",
      proposed: { ...endpoint, depends_on: [], consumer: "canonical downstream applications" },
      reason: "remove the obsolete predecessor edge", direction: "correct" as const,
    };
    delete endpointCleanup.proposed.proof_tex;
    await saveWorkingState(ctx, {
      round: 2, proposal_revision: "angle:0/version:1", escalation_entries_consumed: 0, solved: {},
      proposals: {
        statements: [], definitions: [], assumptions: [],
        // Mandates are seeded before worker cleanup in the live merge. Apply must
        // canonicalize the dependency order rather than trusting packet order.
        coreEdits: [mandatedDelete, endpointCleanup], proofs: [],
      },
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto, working: null, edit: mandatedDelete, proposalRevision: "angle:0/version:1",
      })],
    });
    await applyProposedChanges({ ctx });
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.statements.some((statement: any) => statement.id === "thm:main")).toBe(false);
    expect(applied.statements.find((statement: any) => statement.id === "prop:aux").depends_on).toEqual([]);
  });

  it("replays a pending apply transaction before an ordinary resumed solve", async () => {
    const ctx = makeCtx(repoRoot);
    const protoBytes = await readFile(protoCoreJsonPath(ctx), "utf8");
    const proto = JSON.parse(protoBytes);
    const carried = {
      id: "lem:carried-obsolete", kind: "lemma", statement: "obsolete helper",
      depends_on: [], status: "proved", proof_tex: "Old proof.",
    };
    const edit = {
      kind: "statement-delete" as const,
      id: carried.id,
      reason: "obsolete carried route",
      direction: "delete-obsolete" as const,
    };
    const working = {
      round: 3,
      proposal_revision: "angle:0/version:1",
      escalation_entries_consumed: 0,
      solved: { [carried.id]: { node: carried, proof_tex: carried.proof_tex, snapshot: snapshotMember(proto, carried as any) } },
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [edit], proofs: [] },
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto, working: { solved: { [carried.id]: { node: carried as any } } }, edit,
        proposalRevision: "angle:0/version:1",
      })],
    };
    await saveWorkingState(ctx, working as any);
    const transactionId = "d0apply:test-recovery";
    await writeFile(path.join(path.dirname(coreJsonPath(ctx)), "d0_apply_transaction.json"), JSON.stringify({
      version: 1,
      transaction_id: transactionId,
      proto_before: protoBytes,
      proto_after: protoBytes,
      working_after: {
        ...working,
        solved: {},
        proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
        required_core_edit_mandates: [],
      },
      escalation_entry: {
        transaction_id: transactionId,
        round: 3,
        changed: [{ id: carried.id, kind: "statement", from: JSON.stringify(carried), to: "<deleted>", reason: edit.reason }],
      },
    }), "utf8");
    await runStage0Solve({ ctx, state: makeVersionedState(), deps: solverDeps("prove") });
    const recoveredWorking = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(recoveredWorking.solved[carried.id]).toBeUndefined();
    expect(recoveredWorking.required_core_edit_mandates).toEqual([]);
    expect((await readEscalationLog(ctx)).filter((entry) => entry.transaction_id === transactionId)).toHaveLength(1);
    expect(existsSync(path.join(path.dirname(coreJsonPath(ctx)), "d0_apply_transaction.json"))).toBe(false);
  });

  it("cannot apply or discard a stale packet while a new journal mandate is pending", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "statement-delete" as const, id: "thm:main",
      reason: "new independent adjudication", direction: "delete-obsolete" as const,
    };
    await saveWorkingState(ctx, {
      round: 2, proposal_revision: "angle:0/version:1", escalation_entries_consumed: 0, solved: {},
      proposals: {
        statements: [], definitions: [], assumptions: [],
        coreEdits: [{
          kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
          reason: "stale packet", direction: "correct",
        }], proofs: [],
      },
    });
    await appendEscalationLog(ctx, {
      round: 2, changed: [], directive: "delete exact target", require_core_changes: true,
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
      })],
    });
    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/lost or altered exact required/i);
    await expect(discardAllProposedChanges({ ctx, note: "discard stale packet" }))
      .rejects.toThrow(/required core edits/i);
  });

  it("refuses a same-operation proposal whose rationale differs from its V2 mandate", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "statement-delete" as const, id: "thm:main",
      reason: "canonical adjudicated rationale", direction: "delete-obsolete" as const,
    };
    await saveWorkingState(ctx, {
      round: 1, proposal_revision: "angle:0/version:1", solved: {},
      proposals: {
        statements: [], definitions: [], assumptions: [],
        coreEdits: [{ ...edit, reason: "worker substituted rationale" }], proofs: [],
      },
      required_core_edit_mandates: [makeRequiredCoreEditMandate({
        core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
      })],
    });
    await expect(applyProposedChanges({ ctx }))
      .rejects.toThrow(/lost or altered exact required core-edit mandate/i);
    const unchanged = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(unchanged.statements.some((statement: any) => statement.id === "thm:main")).toBe(true);
  });

  it("refuses a durable required edit after its semantic target changes", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "statement-delete" as const,
      id: "thm:main",
      reason: "obsolete",
      direction: "delete-obsolete" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
    });
    await saveWorkingState(ctx, {
      round: 1,
      proposal_revision: "angle:0/version:1",
      escalation_entries_consumed: 0,
      solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [edit], proofs: [] },
      required_core_edit_mandates: [mandate],
    });
    proto.statements[0].statement = "an intervening reviewer changed the claim";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await expect(runStage0Solve({ ctx, state: makeVersionedState(), deps: solverDeps("prove") }))
      .rejects.toThrow(/target changed since adjudication/i);
  });

  it("refuses a durable required edit after the proposal revision advances", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const edit = {
      kind: "statement-delete" as const,
      id: "thm:main",
      reason: "obsolete",
      direction: "delete-obsolete" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto,
      working: null,
      edit,
      proposalRevision: "angle:0/version:1",
    });
    await saveWorkingState(ctx, {
      round: 1,
      proposal_revision: "angle:0/version:1",
      escalation_entries_consumed: 0,
      solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [edit], proofs: [] },
      required_core_edit_mandates: [mandate],
    });
    const state = makeState();
    state.proposed_from!.current_angle_index = 0;
    state.proposed_from!.current_version = 2;
    await expect(runStage0Solve({ ctx, state, deps: solverDeps("prove") }))
      .rejects.toThrow(/proposal revision.*not angle:0\/version:2/i);
  });

  it("refuses mutually exclusive required edits on one target", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const deletion = {
      kind: "statement-delete" as const,
      id: "thm:main",
      reason: "obsolete",
      direction: "delete-obsolete" as const,
    };
    const replacement = {
      kind: "statement-replace" as const,
      id: "thm:main",
      proposed: { ...proto.statements[0] },
      reason: "rewire instead",
      direction: "correct" as const,
    };
    delete replacement.proposed.proof_tex;
    await saveWorkingState(ctx, {
      round: 1,
      escalation_entries_consumed: 0,
      solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
      required_core_edit_mandates: [
        makeRequiredCoreEditMandate({ core: proto, working: null, edit: deletion, proposalRevision: "angle:0/version:1" }),
        makeRequiredCoreEditMandate({ core: proto, working: null, edit: replacement, proposalRevision: "angle:0/version:1" }),
      ],
    });
    await expect(runStage0Solve({ ctx, state: makeVersionedState(), deps: solverDeps("prove") }))
      .rejects.toThrow(/conflicting required core-edit mandates.*thm:main/i);
  });

  it("rejects a working-state mandate whose content-addressed id was forged", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const mandate = makeRequiredCoreEditMandate({
      core: proto,
      working: null,
      edit: {
        kind: "statement-delete",
        id: "thm:main",
        reason: "obsolete",
        direction: "delete-obsolete",
      },
      proposalRevision: "angle:0/version:1",
    });
    mandate.mandate_id = `d0m:${"0".repeat(64)}`;
    await writeFile(workingPath(ctx), JSON.stringify({
      round: 1,
      solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
      required_core_edit_mandates: [mandate],
    }), "utf8");
    await expect(runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") }))
      .rejects.toThrow(/mandate id\/content mismatch/i);
  });

  it("rejects a mandate whose adjudicated rationale was mutated at rest", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: { kind: "statement-delete", id: "thm:main", reason: "original rationale", direction: "delete-obsolete" },
      proposalRevision: "angle:0/version:1",
    });
    mandate.edit.reason = "tampered rationale";
    await writeFile(workingPath(ctx), JSON.stringify({
      round: 1, solved: {}, required_core_edit_mandates: [mandate],
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    }), "utf8");
    await expect(runStage0Solve({ ctx, state: makeVersionedState(), deps: solverDeps("prove") }))
      .rejects.toThrow(/sealed bytes diverge|mandate id\/content mismatch/i);
  });

  it("validates a durable pre-versioning mandate with its original operation digest", () => {
    const legacy = {
      mandate_id: "d0m:7b11a6cfd38e2a117f0c97c19f2890ef095fb8d638bec30c52dbac87d60d2410",
      edit: {
        kind: "assumption-replace" as const,
        id: "ass:strict-overlap",
        proposed: {
          id: "ass:strict-overlap",
          kind: "support" as const,
          condition: String.raw`\(c_\pi\le\pi(x)\le1-c_\pi\ \text{for }x\in\mathcal X\).`,
          free_symbols: ["c_\\pi", "\\pi", "x", "\\mathcal X"],
          standard: { name: "strict overlap", cite: "BonviniKennedyKeele2023MinimaxSubgroup" },
          used_by: [
            "def:smooth-model", "def:transverse-model", "lem:estimator-construction",
            "lem:local-gram", "thm:identified-version",
          ],
        },
        reason: "Byte-only LaTeX serialization correction: move the trailing domain qualifier inside inline math; the assumption is mathematically identical.",
        direction: "correct" as const,
      },
      proposal_revision: "angle:0/version:6",
      target_snapshot: "{\"id\":\"ass:strict-overlap\",\"kind\":\"support\",\"condition\":\"\\\\(c_\\\\pi\\\\le\\\\pi(x)\\\\le1-c_\\\\pi\\\\)\\\\ \\\\text{for }x\\\\in\\\\mathcal X.\",\"free_symbols\":[\"c_\\\\pi\",\"\\\\pi\",\"x\",\"\\\\mathcal X\"],\"standard\":{\"name\":\"strict overlap\",\"cite\":\"BonviniKennedyKeele2023MinimaxSubgroup\"},\"used_by\":[\"def:smooth-model\",\"def:transverse-model\",\"lem:estimator-construction\",\"lem:local-gram\",\"thm:identified-version\"]}",
    };
    expect(() => assertMandateIntegrity(legacy)).not.toThrow();
  });

  it("emits byte-anchored v3 mandates whose id is the hash of the persisted sealed bytes", () => {
    const proto = structuredClone(PROTO) as any;
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: { kind: "statement-delete", id: "thm:main", reason: "rejected edit", direction: "delete-obsolete" },
      proposalRevision: "angle:0/version:1",
    });
    expect(mandate.hash_version).toBe(3);
    expect(mandate.sealed).toBeTypeOf("string");
    const digest = createHash("sha256").update(mandate.sealed!).digest("hex");
    expect(mandate.mandate_id).toBe(`d0m:${digest}`);
    expect(JSON.parse(mandate.sealed!)).toEqual({
      edit: mandate.edit,
      proposal_revision: mandate.proposal_revision,
      target_snapshot: mandate.target_snapshot,
    });
  });

  it("verifies a v3 mandate from persisted bytes regardless of field key order, and rejects tampering", () => {
    const proto = structuredClone(PROTO) as any;
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: { kind: "statement-delete", id: "thm:main", reason: "rejected edit", direction: "delete-obsolete" },
      proposalRevision: "angle:0/version:1",
    });
    // Round-trip through JSON with reordered record keys: integrity must not
    // depend on any re-canonicalization of the parsed object.
    const reordered = JSON.parse(JSON.stringify({
      target_snapshot: mandate.target_snapshot,
      sealed: mandate.sealed,
      proposal_revision: mandate.proposal_revision,
      mandate_id: mandate.mandate_id,
      hash_version: mandate.hash_version,
      edit: mandate.edit,
    }));
    expect(() => assertMandateIntegrity(reordered)).not.toThrow();
    const tamperedEdit = structuredClone(reordered);
    tamperedEdit.edit.id = "prop:aux";
    expect(() => assertMandateIntegrity(tamperedEdit)).toThrow(/sealed|mismatch/i);
    const tamperedSealed = structuredClone(reordered);
    tamperedSealed.sealed = tamperedSealed.sealed.replace("thm:main", "prop:aux");
    expect(() => assertMandateIntegrity(tamperedSealed)).toThrow(/mismatch/i);
  });

  it("passes integrity before persistence even when an optional edit property is explicitly undefined", () => {
    const proto = structuredClone(PROTO) as any;
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: {
        kind: "statement-delete", id: "thm:main", reason: "rejected edit",
        direction: "delete-obsolete", replacement_id: undefined,
      } as any,
      proposalRevision: "angle:0/version:1",
    });
    // JSON.stringify drops explicitly-undefined keys from `sealed`; the record's
    // semantic fields must match those JSON semantics BEFORE any round-trip, or
    // a freshly minted mandate fails its own integrity check in memory.
    expect(() => assertMandateIntegrity(mandate)).not.toThrow();
    expect(() => assertMandateIntegrity(JSON.parse(JSON.stringify(mandate)))).not.toThrow();
  });

  it("emits v2 cancellations hashed over their persisted sealed bytes", () => {
    const cancellation = makeRequiredCoreEditMandateCancellation({
      mandateId: `d0m:${"1".repeat(64)}`,
      reason: "mandatory review rejected the exact edit",
    });
    expect(cancellation.hash_version).toBe(2);
    const digest = createHash("sha256").update(cancellation.sealed!).digest("hex");
    expect(cancellation.cancellation_id).toBe(`d0c:${digest}`);
    expect(JSON.parse(cancellation.sealed!)).toEqual({
      mandate_id: cancellation.mandate_id,
      reason: cancellation.reason,
    });
  });

  it("refuses to seal a mandate whose payload carries unsealable LaTeX", () => {
    const proto = structuredClone(PROTO) as any;
    expect(() => makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: {
        kind: "statement-delete", id: "thm:main",
        reason: "construction has \\(x\\in\\mathcal X outside math mode", direction: "delete-obsolete",
      },
      proposalRevision: "angle:0/version:1",
    })).toThrow(/cannot be sealed/);
  });

  it("canonicalizes a valid pre-versioning mandate cancellation without rewriting its journal row", () => {
    const mandateId = `d0m:${"1".repeat(64)}`;
    const reason = "mandatory review rejected the exact edit";
    const digest = createHash("sha256")
      .update(JSON.stringify({ mandate_id: mandateId, reason }))
      .digest("hex");
    expect(RequiredCoreEditMandateCancellationSchema.parse({
      cancellation_id: `d0mc:${digest}`,
      mandate_id: mandateId,
      reason,
    })).toEqual({
      cancellation_id: `d0c:${digest}`,
      hash_version: 1,
      mandate_id: mandateId,
      reason,
    });
  });

  it("fails closed on a consumed legacy raw required edit that never became durable", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "legacy delete",
      required_core_edits: [{
        kind: "statement-delete", id: "thm:main", reason: "legacy raw authority", direction: "delete-obsolete",
      }],
    });
    await saveWorkingState(ctx, {
      round: 1, escalation_entries_consumed: 1, proposal_revision: "angle:0/version:1", solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    });
    await expect(runStage0Solve({ ctx, state: makeVersionedState(), deps: solverDeps("prove") }))
      .rejects.toThrow(/legacy required_core_edits.*re-adjudicate/i);
  });

  it("refuses a delete mandate whose replacement is independently deleted", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const first = {
      kind: "statement-delete" as const, id: "thm:main", replacement_id: "prop:aux",
      reason: "replace headline", direction: "delete-obsolete" as const,
    };
    const second = {
      kind: "statement-delete" as const, id: "prop:aux",
      reason: "delete endpoint", direction: "delete-obsolete" as const,
    };
    await saveWorkingState(ctx, {
      round: 1, proposal_revision: "angle:0/version:1", solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
      required_core_edit_mandates: [
        makeRequiredCoreEditMandate({ core: proto, working: null, edit: first, proposalRevision: "angle:0/version:1" }),
        makeRequiredCoreEditMandate({ core: proto, working: null, edit: second, proposalRevision: "angle:0/version:1" }),
      ],
    });
    await expect(runStage0Solve({ ctx, state: makeVersionedState(), deps: solverDeps("prove") }))
      .rejects.toThrow(/replacement.*itself mandated for deletion/i);
  });

  it("applies typed assumption, deletion, symbol, bibliography, and reverse-edge edits", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.symbols[0].role = "open target";
    proto.assumptions[0].used_by = ["thm:stale"];
    proto.symbols.push({ name: "unused_handle", type: "scalar", role: "obsolete notation" });
    proto.definitions.push({ id: "def:obsolete-handle", name: "old", construction: "future program", inputs: [] });
    proto.target_estimand = "H_F: equality holds " + "\f" + "orall units";
    proto.bibliography[0].citation = "Wrong pages";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [
      {
        kind: "assumption-replace",
        id: "ass:overlap",
        proposed: {
          ...proto.assumptions[0],
          condition: "the propensity is bounded away from 0 and 1 and the randomizer is independent",
          free_symbols: ["tau"],
        },
        reason: "formalize the independence used by the proof",
        direction: "correct",
      },
      { kind: "definition-delete", id: "def:obsolete-handle", reason: "retired program", direction: "delete-obsolete" },
      {
        kind: "definition-add", id: "def:new-derived-object",
        proposed: { id: "def:new-derived-object", name: "new object", construction: "T=tau", inputs: ["ass:overlap"] },
        reason: "formalize a newly proved object", direction: "correct",
      },
      {
        kind: "symbol-add", name: "t_pi",
        proposed: { name: "t_pi", type: "positive constant", space: "(0,infinity)", role: "propensity smoothness" },
        reason: "declare a global constant used by the assumption", direction: "correct",
      },
      {
        kind: "symbol-add", name: "L_pi",
        proposed: { name: "L_pi", type: "positive constant", space: "(0,infinity)", role: "propensity radius" },
        reason: "declare a global constant used by the assumption", direction: "correct",
      },
      {
        kind: "symbol-replace", name: "tau",
        proposed: { ...proto.symbols[0], role: "resolved causal estimand" },
        reason: "the target is solved", direction: "correct",
      },
      {
        kind: "symbol-delete", name: "unused_handle",
        reason: "the symbol has no remaining consumer", direction: "delete-obsolete",
      },
      {
        kind: "bibliography-replace", key: "Rosenbaum1983",
        proposed: { key: "Rosenbaum1983", citation: "Correct publication metadata" },
        reason: "correct citation", direction: "correct",
      },
      {
        kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
        reason: "rebuild direct inverse", direction: "correct",
      },
    ] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.assumptions[0].condition).toContain("randomizer is independent");
    expect(updated.assumptions[0].free_symbols).toEqual(["tau"]);
    expect(updated.assumptions[0].used_by).toEqual(["def:class", "def:new-derived-object", "prop:aux", "thm:main"]);
    expect(updated.definitions.some((d: any) => d.id === "def:obsolete-handle")).toBe(false);
    expect(updated.definitions.some((d: any) => d.id === "def:new-derived-object")).toBe(true);
    expect(updated.symbols[0].role).toBe("resolved causal estimand");
    expect(updated.symbols).toEqual(expect.arrayContaining([
      expect.objectContaining({ name: "t_pi", role: "propensity smoothness" }),
      expect.objectContaining({ name: "L_pi", role: "propensity radius" }),
    ]));
    expect(updated.symbols.some((s: any) => s.name === "unused_handle")).toBe(false);
    expect(updated.bibliography[0].citation).toBe("Correct publication metadata");
    expect(updated.target_estimand).toContain("\\forall units");
    expect(updated.target_estimand).not.toContain("\f");
    expect(updated.assumptions[0].used_by).toContain("def:new-derived-object");
  });

  it("refuses an accepted symbol-add that closes a dependency cycle with an older symbol", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.symbols[0].refs = ["new_domain"];
    const before = JSON.stringify(proto);
    await writeFile(protoCoreJsonPath(ctx), before, "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "symbol-add",
      name: "new_domain",
      proposed: {
        name: "new_domain",
        type: "derived domain",
        role: "same-bundle prerequisite",
        refs: [proto.symbols[0].name],
      },
      reason: "declare the new domain used by the older symbol",
      direction: "correct",
    }] });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /fails the structural gate.*references symbol.*before it is defined/i,
    );
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
  });

  it("applies an atomic definition deletion closure independently of emitter order", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push(
      { id: "def:obsolete-domain", name: "old domain", construction: "the retired domain", inputs: [] },
      {
        id: "def:obsolete-loss",
        name: "old loss",
        construction: "loss on def:obsolete-domain",
        inputs: ["def:obsolete-domain"],
      },
    );
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [
      // Deliberately emit the dependency before its only dependent. The reviewed
      // transaction deletes both, so this order must not create a false live edge.
      {
        kind: "definition-delete", id: "def:obsolete-domain",
        reason: "renamed atomically", direction: "delete-obsolete",
      },
      {
        kind: "definition-delete", id: "def:obsolete-loss",
        reason: "renamed atomically", direction: "delete-obsolete",
      },
    ] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.definitions.some((d: any) => d.id === "def:obsolete-domain")).toBe(false);
    expect(updated.definitions.some((d: any) => d.id === "def:obsolete-loss")).toBe(false);
  });

  it("refuses a definition deletion while a surviving statement keeps a structured dependency", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push({
      id: "def:still-used", name: "used definition", construction: "a structured premise", inputs: [],
    });
    proto.statements[0].depends_on.push("def:still-used");
    const before = JSON.stringify(proto);
    await writeFile(protoCoreJsonPath(ctx), before, "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "definition-delete", id: "def:still-used",
      reason: "incorrectly thought obsolete", direction: "delete-obsolete",
    }] });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /structured references remain.*statement:thm:main/i,
    );
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
  });

  it("does not validate a selected definition delete against an unselected peer delete", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push(
      { id: "def:subset-a", name: "subset A", construction: "base object", inputs: [] },
      {
        id: "def:subset-b", name: "subset B",
        construction: "built from def:subset-a", inputs: ["def:subset-a"],
      },
    );
    const before = JSON.stringify(proto);
    await writeFile(protoCoreJsonPath(ctx), before, "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [
      { kind: "definition-delete", id: "def:subset-a", reason: "delete A", direction: "delete-obsolete" },
      { kind: "definition-delete", id: "def:subset-b", reason: "delete B", direction: "delete-obsolete" },
    ] });

    await expect(applyProposedChanges({
      ctx, ids: new Set(["core-edit:def:subset-a"]),
    })).rejects.toThrow(/definition|coherence|references remain/i);
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
  });

  it("orders an accepted definition-add before existing definition consumers", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push({
      id: "def:region",
      name: "region",
      construction: "The relative neighborhood inside def:constrained-model.",
      inputs: ["def:constrained-model"],
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "definition-add",
      id: "def:constrained-model",
      proposed: {
        id: "def:constrained-model",
        name: "constrained model",
        construction: "The finite-cell model satisfying the witness restrictions.",
        inputs: [],
      },
      reason: "name the model used by the existing region",
      direction: "correct",
    }] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const ids = updated.definitions.map((definition: { id: string }) => definition.id);
    expect(ids.indexOf("def:constrained-model")).toBeLessThan(ids.indexOf("def:region"));
  });

  it("rejects an accepted bundle whose final post-image has an unbalanced TeX group", async () => {
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "definition-add",
      id: "def:malformed-model",
      proposed: {
        id: "def:malformed-model",
        name: "malformed model",
        construction: String.raw`The family \(\operatorname{binary\).`,
        inputs: [],
      },
      reason: "name the accepted model family",
      direction: "correct",
    }] });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/unbalanced TeX grouping braces/);
  });

  it("does not reject legacy proto DSL while validating a newly selected edit", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    // Historical formal fields use set-difference notation whose escaped opening
    // brace is intentionally not a TeX grouping token. Strictly scanning the
    // whole proto would reject this old, renderer-supported DSL on every apply.
    proto.target_estimand = String.raw`E_n\{a,b}`;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "definition-add",
      id: "def:valid-new-model",
      proposed: {
        id: "def:valid-new-model",
        name: "valid new model",
        construction: String.raw`The family \(\mathcal M\).`,
        inputs: [],
      },
      reason: "exercise the selected-payload seal boundary",
      direction: "correct",
    }] });

    await expect(applyProposedChanges({ ctx })).resolves.toHaveLength(1);
    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.target_estimand).toBe(String.raw`E_n\{a,b}`);
    expect(updated.definitions.some((definition: any) => definition.id === "def:valid-new-model")).toBe(true);
  });

  it("rejects a malformed provisional proof selected for promotion", async () => {
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, {
      statements: [{
        id: "thm:main",
        current: PROTO.statements[0].statement,
        proposed: "tau is identified on the overlap region",
        reason: "narrow to the proved region",
        direction: "narrow",
      }],
      proofs: [{
        id: "thm:main",
        proof_tex: String.raw`By \(\operatorname{broken\).`,
        argues_proposed: true,
      }],
      coreEdits: [withCorrectionPairs({
        proposed_statement_changes: [{
          id: "thm:main",
          current: PROTO.statements[0].statement,
          proposed: "tau is identified on the overlap region",
        }],
      }).proposed_core_edits[0]],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/unbalanced TeX grouping braces/);
  });

  it("seals a standalone reviewed helper proof even without a same-id claim edit", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:sealed-helper", kind: "lemma", statement: "the helper claim",
      depends_on: [], status: "to-prove", free_symbols: [], consumer: "old route",
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        [helper.id]: {
          node: helper, owner: "thm:main", partial: true,
          proof_tex: String.raw`By \(\operatorname{broken\).`,
          snapshot: snapshotMember(PROTO as any, helper),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: helper.id, proof_tex: String.raw`By \(\operatorname{broken\).` }],
      coreEdits: [{
        kind: "statement-replace",
        id: helper.id,
        proposed: { ...helper, consumer: "reviewed route" },
        reason: "publish reviewed helper metadata",
        direction: "correct",
      }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/unbalanced TeX grouping braces/);
  });

  it("promotes every reviewed proof to a dependency fixpoint before clearing proposals", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const helper = {
      id: "lem:promotion-helper", kind: "lemma", statement: "the helper claim",
      depends_on: [], status: "to-prove", free_symbols: [],
    } as any;
    const consumer = {
      id: "thm:promotion-consumer", kind: "theorem", statement: "the consumer claim",
      depends_on: [helper.id], status: "to-prove", free_symbols: [], consumer: "old route",
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        [helper.id]: {
          node: helper, owner: consumer.id, partial: true,
          proof_tex: "Complete helper proof.", snapshot: snapshotMember(proto, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, partial: true,
          proof_tex: "Use lem:promotion-helper.", snapshot: snapshotMember(proto, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [
        { id: consumer.id, proof_tex: "Use lem:promotion-helper." },
        { id: helper.id, proof_tex: "Complete helper proof." },
      ],
      coreEdits: [{
        kind: "statement-replace",
        id: consumer.id,
        proposed: { ...consumer, consumer: "reviewed route" },
        reason: "publish reviewed consumer metadata",
        direction: "correct",
      }],
    });

    await applyProposedChanges({ ctx });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[helper.id].partial).toBeUndefined();
    expect(working.solved[consumer.id].partial).toBeUndefined();
    expect(working.solved[helper.id].proof_tex).toBe("Complete helper proof.");
    expect(working.solved[consumer.id].proof_tex).toBe("Use lem:promotion-helper.");
    expect(working.proposals.proofs).toEqual([]);
  });

  it("keeps a frozen theorem's proof and proved status exclusively in working state", async () => {
    const ctx = makeCtx(repoRoot);
    const proof = "Complete reviewed proof.";
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          partial: true,
          proof_tex: proof,
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: proof }],
      coreEdits: [{
        kind: "statement-replace",
        id: "thm:main",
        proposed: { ...PROTO.statements[0], consumer: "reviewed route" },
        reason: "publish reviewed theorem metadata",
        direction: "correct",
      }],
    });

    await applyProposedChanges({ ctx });
    const frozen = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const theorem = frozen.statements.find((node: any) => node.id === "thm:main");
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(theorem.status).toBe("to-prove");
    expect(theorem.proof_tex).toBeUndefined();
    expect(working.solved["thm:main"].node).toBeUndefined();
    expect(working.solved["thm:main"].partial).toBeUndefined();
    expect(working.solved["thm:main"].proof_tex).toBe(proof);
  });

  it("does not let an early metadata pairing bypass an unapplied global invalidator", async () => {
    const ctx = makeCtx(repoRoot);
    const proof = "Complete reviewed proof.";
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          partial: true,
          proof_tex: proof,
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: proof }],
      coreEdits: [
        {
          kind: "statement-replace",
          id: "thm:main",
          proposed: { ...PROTO.statements[0], consumer: "reviewed route" },
          reason: "publish reviewed theorem metadata",
          direction: "correct",
        },
        {
          kind: "symbol-replace",
          name: "tau",
          proposed: { ...PROTO.symbols[0], role: "reviewed target" },
          reason: "change the global proof basis",
          direction: "correct",
        },
      ],
    });

    await expect(applyProposedChanges({
      ctx,
      ids: new Set(["statement-replace:thm:main"]),
    })).rejects.toThrow(/reviewed provisional proof.*did not reach a complete exact postimage/i);
  });

  it("applies accepted semantics while an explicitly rejected proof stays partial", async () => {
    const ctx = makeCtx(repoRoot);
    const proof = "Reviewed proof rejected because one dependency is stale.";
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          proof_tex: proof,
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: proof }],
      coreEdits: [{
        kind: "statement-replace",
        id: "thm:main",
        proposed: {
          ...PROTO.statements[0], status: "proved", proof_tex: proof, consumer: "reviewed route",
        },
        reason: "publish reviewed theorem metadata",
        direction: "correct",
      }],
    });

    await applyProposedChanges({
      ctx,
      rejectedProofIds: new Set(["thm:main"]),
      note: "Proof rejected pending scoped dependency revalidation.",
    });

    const frozen = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(frozen.statements.find((node: any) => node.id === "thm:main").consumer).toBe("reviewed route");
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:main"].partial).toBe(true);
    const journal = await readEscalationLog(ctx);
    expect(journal.at(-1)?.rejected_proof_ids).toEqual(["thm:main"]);
  });

  it("demotes a frozen inline proof when its reviewed replacement proof is rejected", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].status = "proved";
    proto.statements[0].proof_tex = "Old frozen proof.";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: "Rejected reviewed proof." }],
      coreEdits: [{
        kind: "statement-replace",
        id: "thm:main",
        proposed: { ...proto.statements[0], consumer: "reviewed route" },
        reason: "publish reviewed theorem metadata",
        direction: "correct",
      }],
    });

    await applyProposedChanges({
      ctx,
      rejectedProofIds: new Set(["thm:main"]),
      note: "Proof rejected pending scoped dependency revalidation.",
    });

    const frozen = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const theorem = frozen.statements.find((node: any) => node.id === "thm:main");
    expect(theorem.status).toBe("to-prove");
    expect(theorem.proof_tex).toBeUndefined();
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(working.solved["thm:main"].proof_tex).toBe("Rejected reviewed proof.");
  });

  it("validates an already-settled exact reviewed proof against unapplied global edits", async () => {
    const ctx = makeCtx(repoRoot);
    const proof = "Already settled exact reviewed proof.";
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          proof_tex: proof,
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: proof }],
      coreEdits: [
        {
          kind: "statement-replace",
          id: "thm:main",
          proposed: { ...PROTO.statements[0], status: "proved", proof_tex: proof, consumer: "reviewed route" },
          reason: "publish reviewed theorem metadata",
          direction: "correct",
        },
        {
          kind: "symbol-replace",
          name: "tau",
          proposed: { ...PROTO.symbols[0], role: "reviewed target" },
          reason: "change the global proof basis",
          direction: "correct",
        },
      ],
    });

    await expect(applyProposedChanges({
      ctx,
      ids: new Set(["statement-replace:thm:main"]),
    })).rejects.toThrow(/reviewed provisional proof.*did not reach a complete exact postimage/i);
  });

  it("rejects a sealed non-definition proof bundle after its frozen basis drifts", async () => {
    const ctx = makeCtx(repoRoot);
    const proof = "Proof under the reviewed symbol meaning.";
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          partial: true,
          proof_tex: proof,
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: proof }],
      coreEdits: [{
        kind: "statement-replace",
        id: "thm:main",
        proposed: { ...PROTO.statements[0], consumer: "reviewed route" },
        reason: "publish reviewed theorem metadata",
        direction: "correct",
      }],
    });
    const drifted = structuredClone(PROTO) as any;
    drifted.symbols[0].def = "a different unreviewed target meaning";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(drifted), "utf8");

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/persisted assembled-core basis/);
  });

  it("orders promotion through proof-text-wired dependencies", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:wired-helper", kind: "lemma", statement: "the helper claim",
      depends_on: [], status: "to-prove", free_symbols: [],
    } as any;
    const consumer = {
      id: "thm:wired-consumer", kind: "theorem", statement: "the consumer claim",
      depends_on: [], status: "to-prove", free_symbols: [], consumer: "old route",
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        [helper.id]: {
          node: helper, owner: consumer.id, partial: true,
          proof_tex: "Incomplete helper.", snapshot: snapshotMember(PROTO as any, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, partial: true,
          proof_tex: "Use lem:wired-helper.", snapshot: snapshotMember(PROTO as any, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: consumer.id, proof_tex: "Use lem:wired-helper." }],
      coreEdits: [{
        kind: "statement-replace",
        id: consumer.id,
        proposed: { ...consumer, consumer: "reviewed route" },
        reason: "publish reviewed consumer metadata",
        direction: "correct",
      }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /reviewed provisional proof.*did not reach a complete exact postimage/i,
    );
  });

  it("rebases an applied symbol edit only after reopening unreviewed affected proofs", async () => {
    const ctx = makeCtx(repoRoot);
    const proof = "Reviewed proof under the corrected symbol meaning.";
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(PROTO as any),
      solved: {
        "thm:main": {
          partial: true,
          proof_tex: proof,
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
        "prop:aux": {
          proof_tex: "Old unreviewed proof.",
          snapshot: snapshotMember(PROTO as any, PROTO.statements[1] as any),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: "thm:main", proof_tex: proof }],
      coreEdits: [{
        kind: "symbol-replace",
        name: "tau",
        proposed: { ...PROTO.symbols[0], def: "the corrected target meaning" },
        reason: "correct the global target meaning",
        direction: "correct",
      }],
    });

    await applyProposedChanges({ ctx });
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.symbol_basis).toEqual(symbolBasis(proto));
    expect(working.solved["thm:main"].partial).toBeUndefined();
    expect(working.solved["prop:aux"].partial).toBe(true);
    expect(computeValidNodes(working, proto).has("thm:main")).toBe(true);
    expect(computeValidNodes(working, proto).has("prop:aux")).toBe(false);
  });

  it("lands a reviewed symbol correction while deferring its sibling-invalidated proof closure", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:symbol-helper", kind: "lemma", statement: "the helper proves tau",
      depends_on: [], status: "to-prove", free_symbols: ["tau"],
    } as any;
    const consumer = {
      id: "thm:symbol-consumer", kind: "theorem", statement: "the consumer proves tau",
      depends_on: [helper.id], status: "to-prove", free_symbols: ["tau"],
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        [helper.id]: {
          node: helper, owner: consumer.id, proof_tex: "Settled helper proof.",
          snapshot: snapshotMember(PROTO as any, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, proof_tex: "Use lem:symbol-helper.",
          snapshot: snapshotMember(PROTO as any, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: consumer.id, proof_tex: "Use lem:symbol-helper." }],
      coreEdits: [{
        kind: "symbol-replace",
        name: "tau",
        proposed: { ...PROTO.symbols[0], def: "the corrected target meaning" },
        reason: "correct the global target meaning",
        direction: "correct",
      }],
    });

    await applyProposedChanges({ ctx });
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.symbol_basis).toEqual(symbolBasis(proto));
    expect(working.solved[helper.id].partial).toBe(true);
    expect(working.solved[consumer.id].partial).toBe(true);
    expect(computeValidNodes(working, proto).has(helper.id)).toBe(false);
    expect(computeValidNodes(working, proto).has(consumer.id)).toBe(false);
    expect(working.proposals.proofs).toEqual([]);
  });

  it("does not let a genuine symbol edit adopt a pre-existing partial helper", async () => {
    const ctx = makeCtx(repoRoot);
    const helper = {
      id: "lem:preexisting-partial", kind: "lemma", statement: "the unresolved tau helper",
      depends_on: [], status: "to-prove", free_symbols: ["tau"],
    } as any;
    const consumer = {
      id: "thm:partial-consumer", kind: "theorem", statement: "the reviewed tau consumer",
      depends_on: [helper.id], status: "to-prove", free_symbols: ["tau"],
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(PROTO as any, [helper, consumer]),
      solved: {
        [helper.id]: {
          node: helper, owner: consumer.id, partial: true,
          proof_tex: "Still incomplete.", snapshot: snapshotMember(PROTO as any, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, partial: true,
          proof_tex: "Use lem:preexisting-partial.", snapshot: snapshotMember(PROTO as any, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: consumer.id, proof_tex: "Use lem:preexisting-partial." }],
      coreEdits: [{
        kind: "symbol-replace", name: "tau",
        proposed: { ...PROTO.symbols[0], def: "the corrected target meaning" },
        reason: "correct the global target meaning", direction: "correct",
      }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /reviewed provisional proof.*did not reach a complete exact postimage/i,
    );
    expect((JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as any).symbols[0].def)
      .toBe(PROTO.symbols[0].def);
  });

  it("does not let a definition label edit authorize semantic-symbol deferral", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push({
      id: "def:model", name: "old prose label", construction: "the formal model",
      inputs: [], free_symbols: [],
    });
    proto.symbols.push({ name: "M", type: "model_class", def: "the model", ref: "def:model" });
    const helper = {
      id: "lem:label-helper", kind: "lemma", statement: "the unresolved helper",
      depends_on: [], status: "to-prove", free_symbols: ["M"],
    } as any;
    const consumer = {
      id: "thm:label-consumer", kind: "theorem", statement: "the reviewed consumer",
      depends_on: [helper.id], status: "to-prove", free_symbols: ["M"],
    } as any;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto, [helper, consumer]),
      solved: {
        [helper.id]: {
          node: helper, owner: consumer.id, partial: true,
          proof_tex: "Incomplete helper.", snapshot: snapshotMember(proto, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, partial: true,
          proof_tex: "Use lem:label-helper.", snapshot: snapshotMember(proto, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: consumer.id, proof_tex: "Use lem:label-helper." }],
      coreEdits: [{
        kind: "definition-replace", id: "def:model",
        based_on_revision: definitionRevision(
          proto.definitions.find((definition: any) => definition.id === "def:model"),
          proto,
        ),
        proposed: {
          ...proto.definitions.find((definition: any) => definition.id === "def:model"),
          name: "new prose label",
        },
        reason: "clarify only the display label", direction: "correct",
      }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /reviewed provisional proof.*did not reach a complete exact postimage/i,
    );
    expect((JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as any).definitions
      .find((definition: any) => definition.id === "def:model").name)
      .toBe("old prose label");
  });

  it("uses the pre-edit assumption scope when the same bundle hides a changed symbol", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.assumptions[0].free_symbols = ["tau"];
    proto.statements[0].free_symbols = [];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto),
      solved: {
        "thm:main": {
          proof_tex: "Settled proof through ass:overlap.",
          snapshot: snapshotMember(proto, proto.statements[0]),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      coreEdits: [
        {
          kind: "assumption-replace",
          id: "ass:overlap",
          proposed: { ...proto.assumptions[0], free_symbols: [] },
          reason: "remove stale declaration metadata",
          direction: "correct",
        },
        {
          kind: "symbol-replace",
          name: "tau",
          proposed: { ...proto.symbols[0], def: "the corrected target meaning" },
          reason: "correct the global target meaning",
          direction: "correct",
        },
      ],
    });

    await applyProposedChanges({ ctx });
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.symbol_basis).toEqual(symbolBasis(updatedProto));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(computeValidNodes(working, updatedProto).has("thm:main")).toBe(false);
  });

  it("invalidates a legacy proof when statement replacement implicitly repoints a symbol ref", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.symbols.push({ name: "M", type: "named_result", def: "the referenced result", ref: "lem:old" });
    proto.statements.push(
      { id: "lem:old", kind: "lemma", statement: "the old result", depends_on: [], status: "to-prove", free_symbols: [] },
      { id: "lem:new", kind: "lemma", statement: "the replacement result", depends_on: [], status: "to-prove", free_symbols: [] },
    );
    proto.statements[0].free_symbols = ["M"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          proof_tex: "Settled proof under M.",
          snapshot: snapshotMember(proto, proto.statements[0]),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      coreEdits: [{
        kind: "statement-delete",
        id: "lem:old",
        replacement_id: "lem:new",
        reason: "replace the canonical referenced result",
        direction: "delete-obsolete",
      }],
    });

    await applyProposedChanges({ ctx });
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(updatedProto.symbols.find((symbol: any) => symbol.name === "M").ref).toBe("lem:new");
    expect(working.symbol_basis).toEqual(symbolBasis(updatedProto));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(computeValidNodes(working, updatedProto).has("thm:main")).toBe(false);
  });

  it("rejects a dependency-rewired helper as independent debt under a symbol change", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.assumptions[0].free_symbols = ["tau"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const helper = {
      id: "lem:agent-symbol-helper", kind: "lemma", statement: "the agent helper",
      depends_on: ["ass:overlap"], status: "to-prove", free_symbols: [],
    } as any;
    const consumer = {
      id: "thm:agent-symbol-consumer", kind: "theorem", statement: "the agent consumer",
      depends_on: [helper.id], status: "to-prove", free_symbols: [],
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto),
      solved: {
        [helper.id]: {
          node: helper, owner: consumer.id, proof_tex: "Proof using ass:overlap.",
          snapshot: snapshotMember(proto, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, proof_tex: "Use lem:agent-symbol-helper.",
          snapshot: snapshotMember(proto, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: consumer.id, proof_tex: "Use lem:agent-symbol-helper." }],
      coreEdits: [
        {
          kind: "statement-replace",
          id: helper.id,
          proposed: { ...helper, depends_on: [] },
          reason: "remove the carried assumption edge",
          direction: "correct",
        },
        {
          kind: "symbol-replace",
          name: "tau",
          proposed: { ...proto.symbols[0], def: "the corrected target meaning" },
          reason: "correct the global target meaning",
          direction: "correct",
        },
      ],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /reviewed provisional proof.*did not reach a complete exact postimage/i,
    );
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(updatedProto.symbols[0].def).toBe(proto.symbols[0].def);
    expect(working.solved[helper.id].node.depends_on).toEqual(["ass:overlap"]);
    expect(working.solved[helper.id].partial).toBeUndefined();
    expect(working.solved[consumer.id].partial).toBeUndefined();
  });

  it("invalidates consumers through a transitive symbol refs chain", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.symbols.push(
      { name: "b", type: "derived", def: "b = tau", refs: ["tau"] },
      { name: "a", type: "derived", def: "a = T(b)", refs: ["b"] },
    );
    proto.statements[0].free_symbols = ["a"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto),
      solved: {
        "thm:main": {
          proof_tex: "Settled proof about a.",
          snapshot: snapshotMember(proto, proto.statements[0]),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      coreEdits: [{
        kind: "symbol-replace",
        name: "tau",
        proposed: { ...proto.symbols[0], def: "the corrected target meaning" },
        reason: "correct the root symbol",
        direction: "correct",
      }],
    });

    await applyProposedChanges({ ctx });
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(computeValidNodes(working, updatedProto).has("thm:main")).toBe(false);
  });

  it("invalidates a symbol consumer when its stable ref target definition changes", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push({
      id: "def:model", name: "model", construction: "the old model class",
      inputs: [], free_symbols: [],
    });
    proto.symbols.push({ name: "M", type: "model_class", def: "the model", ref: "def:model" });
    proto.statements[0].free_symbols = ["M"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto),
      solved: {
        "thm:main": {
          proof_tex: "Settled proof over M.",
          snapshot: snapshotMember(proto, proto.statements[0]),
        },
      },
    });
    const change = {
      id: "def:model",
      current: "the old model class",
      proposed: "the corrected model class",
      reason: "correct the referenced model",
      direction: "correct",
      based_on_revision: definitionRevision(
        proto.definitions.find((definition: any) => definition.id === "def:model"),
        proto,
      ),
    };
    await seedWorkingProposals(ctx, {
      definitions: [change],
      coreEdits: [{
        kind: "definition-replace",
        id: "def:model",
        proposed: { ...proto.definitions.find((definition: any) => definition.id === "def:model"), construction: change.proposed },
        reason: "synchronize the corrected referenced model",
        direction: "correct",
        based_on_revision: change.based_on_revision,
      }],
    });

    await applyProposedChanges({ ctx });
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(computeValidNodes(working, updatedProto).has("thm:main")).toBe(false);
  });

  it("invalidates a symbol consumer when a nested referenced definition changes", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push(
      { id: "def:inner", name: "inner", construction: "the old inner object", inputs: [], free_symbols: [] },
      // The nested edge is intentionally authored only in construction prose. Real
      // cores use this shape, so snapshots must not rely solely on `inputs`.
      { id: "def:outer", name: "outer", construction: "the outer object built from def:inner", inputs: [], free_symbols: [] },
    );
    proto.symbols.push({ name: "M", type: "model_class", def: "the outer model", ref: "def:outer" });
    proto.statements[0].free_symbols = ["M"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto),
      solved: {
        "thm:main": {
          proof_tex: "Settled proof over nested M.",
          snapshot: snapshotMember(proto, proto.statements[0]),
        },
      },
    });
    const definition = proto.definitions.find((node: any) => node.id === "def:inner");
    const revision = definitionRevision(definition, proto);
    await seedWorkingProposals(ctx, {
      definitions: [{
        id: "def:inner", current: definition.construction, proposed: "the corrected inner object",
        reason: "correct the nested object", direction: "correct", based_on_revision: revision,
      }],
      coreEdits: [{
        kind: "definition-replace", id: "def:inner",
        proposed: { ...definition, construction: "the corrected inner object" },
        reason: "synchronize the nested correction", direction: "correct", based_on_revision: revision,
      }],
    });

    await applyProposedChanges({ ctx });
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(computeValidNodes(working, updatedProto).has("thm:main")).toBe(false);
  });

  it("invalidates a class-symbol consumer when a nested member assumption changes", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.definitions.push({
      id: "def:referenced-class", name: "referenced class", construction: "{ P : P satisfies overlap }",
      by_member_properties: ["ass:overlap"], free_symbols: [],
    });
    proto.symbols.push({ name: "M", type: "model_class", def: "the referenced class", ref: "def:referenced-class" });
    proto.statements[0].free_symbols = ["M"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto),
      solved: {
        "thm:main": {
          proof_tex: "Settled proof over the referenced class.",
          snapshot: snapshotMember(proto, proto.statements[0]),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      coreEdits: [{
        kind: "assumption-replace",
        id: "ass:overlap",
        proposed: { ...proto.assumptions[0], condition: "the corrected overlap condition" },
        reason: "correct the class member condition",
        direction: "correct",
      }],
    });

    await applyProposedChanges({ ctx });
    const updatedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:main"].partial).toBe(true);
    expect(computeValidNodes(working, updatedProto).has("thm:main")).toBe(false);
  });

  it("refuses to consume a claim-changing proof that lacks argues_proposed", async () => {
    const ctx = makeCtx(repoRoot);
    const proposed = "tau is identified on the reviewed overlap region";
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "thm:main": {
          partial: true,
          proof_tex: "Proof of the changed claim.",
          snapshot: snapshotMember(PROTO as any, PROTO.statements[0] as any),
        },
      },
    });
    const change = {
      id: "thm:main", current: PROTO.statements[0].statement, proposed,
      reason: "narrow to the reviewed region", direction: "narrow",
    };
    await seedWorkingProposals(ctx, {
      statements: [change],
      coreEdits: withCorrectionPairs({ proposed_statement_changes: [change] }).proposed_core_edits,
      proofs: [{ id: "thm:main", proof_tex: "Proof of the changed claim." }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/argues_proposed:true/i);
  });

  it("rejects a selector that splits a claim correction from its metadata pair", async () => {
    const ctx = makeCtx(repoRoot);
    const change = {
      id: "thm:main",
      current: PROTO.statements[0].statement,
      proposed: "tau is identified on the overlap region",
      reason: "narrow to the supported region",
      direction: "narrow",
    };
    await seedWorkingProposals(ctx, {
      statements: [change],
      coreEdits: withCorrectionPairs({ proposed_statement_changes: [change] }).proposed_core_edits,
    });

    await expect(applyProposedChanges({
      ctx,
      ids: new Set(["statement:thm:main"]),
    })).rejects.toThrow(/must be selected atomically/i);
  });

  it("validates the full assumption node that a selected proposal would persist", async () => {
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, { assumptions: [{
      id: "ass:malformed-tag",
      condition: "the overlap condition holds",
      standard_or_novel: String.raw`novel: justified by \(\operatorname{broken\).`,
      reason: "add the required scope restriction",
      not_crux: "technical regularity only",
      free_symbols: [],
    }] });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/unbalanced TeX grouping braces/);
  });

  it("rejects an apply bundle that leaves an assumption free symbol undeclared", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.assumptions[0].free_symbols = ["missing_constant"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "rebuild-reverse-dependencies",
      id: "metadata:reverse-dependencies",
      reason: "exercise post-bundle validation",
      direction: "correct",
    }] });
    const before = await readFile(protoCoreJsonPath(ctx), "utf8");

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/free symbols remain undeclared/);
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
    expect(((await readSurfacedProposals(ctx)).coreEdits ?? []).length).toBeGreaterThan(0);
  });

  it("uses bibliography-replace to add a newly required source key", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [
      {
        kind: "bibliography-replace",
        key: "NewComparator2026",
        proposed: { key: "NewComparator2026", citation: "A newly required comparator." },
        reason: "add a current source not present in the frozen proto",
        direction: "correct",
      },
    ] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.bibliography).toContainEqual({
      key: "NewComparator2026",
      citation: "A newly required comparator.",
    });
  });

  it("replaces the comparator promise table through a typed D0 core edit", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.comparator_promises = [{
      comparator_bibkey: "Rosenbaum1983",
      comparator_claim: "stale strict comparison",
      matched_by: "Theorem 1",
      match_kind: "strict_tightening",
    }];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const edit = {
      kind: "comparator-promise-table-replace",
      id: "metadata:comparator-promise-table",
      proposed: [{
        comparator_bibkey: "Rosenbaum1983",
        comparator_claim: "the source is background rather than a theorem-level target",
        matched_by: "unmatched",
        match_kind: "downgraded_to_informed_by",
      }],
      reason: "synchronize comparator positioning",
      direction: "correct",
    };
    expect(SolveUnitOutputSchema.parse({ proposed_core_edits: [edit] }).proposed_core_edits).toHaveLength(1);
    await seedWorkingProposals(ctx, { coreEdits: [edit] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.comparator_promise_table).toEqual(edit.proposed);
    expect(updated.comparator_promises).toBeUndefined();
  });

  it("qualifies target_estimand through the typed channel when `current` echoes the core", async () => {
    // Regression (stat_doseresponse_minimax_elbow, 2026-07-29): `target_estimand` had NO
    // edit channel, so a referee finding against the estimand line itself was unfixable —
    // the repair stage could not touch the field, and every in-core workaround (relocating
    // the causal claim into class membership) is laundering, because the counterfactual
    // mean then stops being a functional of the observed law.
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.target_estimand = "\\(\\theta_P(t_0)=\\int \\mu_P(t_0,x)p_X(x)dx = E[Y(t_0)]\\)";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const edit = {
      kind: "target-estimand-replace",
      id: "metadata:target-estimand",
      current: proto.target_estimand,
      proposed: "\\(\\theta_P(t_0)=\\int \\mu_P(t_0,x)p_X(x)dx\\), equal to \\(E[Y(t_0)]\\) under prop:causal-identification-at-t0",
      reason: "the causal equality holds only under the identification proposition",
      direction: "correct",
    };
    expect(SolveUnitOutputSchema.parse({ proposed_core_edits: [edit] }).proposed_core_edits).toHaveLength(1);
    await seedWorkingProposals(ctx, { coreEdits: [edit] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.target_estimand).toBe(edit.proposed);
  });

  it("refuses a target_estimand edit whose `current` does not echo the core", async () => {
    // The echo is the field's anti-drift guarantee: an edit that never saw the text it
    // overwrites cannot be distinguished from silently swapping the deliverable. The skip
    // then meets the apply stage's fail-closed rule — a round whose every selected proposal
    // was dropped throws rather than half-applying — so the estimand is left untouched and
    // the solver must re-emit against the text it actually read.
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.target_estimand = "\\(\\theta_P(t_0)=\\int \\mu_P(t_0,x)p_X(x)dx = E[Y(t_0)]\\)";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, {
      coreEdits: [{
        kind: "target-estimand-replace",
        id: "metadata:target-estimand",
        current: "\\(\\theta_P(t_0)=\\text{something the core never said}\\)",
        proposed: "\\(\\theta_P(t_0)=\\text{a different deliverable}\\)",
        reason: "stale echo",
        direction: "correct",
      }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/does not echo the core's target_estimand/);

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.target_estimand).toBe(proto.target_estimand);
  });

  it("rewrites estimand_functional through the typed channel, echo-guarded", async () => {
    // Regression (same run, one round later): clearing `target_estimand` immediately hit
    // the neighbouring frozen field. A class repair that drops a parameter leaves the
    // headline functional still advertising it — the referee's own objection, relocated
    // one line over — and the solver's escape was to keep the parameter as a decorative
    // index ("preserving the current notational parameter list").
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.estimand_functional = "\\(M_n(\\alpha,\\beta,s,d,\\bar p)\\)";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const edit = {
      kind: "estimand-functional-replace",
      id: "metadata:estimand-functional",
      current: proto.estimand_functional,
      proposed: "\\(M_n(\\alpha,\\beta,s,d)\\)",
      reason: "the dropped assumption no longer constrains this parameter",
      direction: "correct",
    };
    expect(SolveUnitOutputSchema.parse({ proposed_core_edits: [edit] }).proposed_core_edits).toHaveLength(1);
    await seedWorkingProposals(ctx, { coreEdits: [edit] });

    await applyProposedChanges({ ctx });

    expect(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")).estimand_functional).toBe(edit.proposed);
  });

  it("refuses an estimand_functional edit whose `current` does not echo the core", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.estimand_functional = "\\(M_n(\\alpha,\\beta,s,d,\\bar p)\\)";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, {
      coreEdits: [{
        kind: "estimand-functional-replace",
        id: "metadata:estimand-functional",
        current: "\\(M_n(\\text{never said this})\\)",
        proposed: "\\(M_n(\\alpha)\\)",
        reason: "stale echo",
        direction: "correct",
      }],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/does not echo the core's estimand_functional/);
    expect(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")).estimand_functional).toBe(proto.estimand_functional);
  });

  it("deletes a statement together with its sole symbol reference through preview, commit, and restart", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "downstream";
    proto.symbols.push({
      name: "main_witness", type: "derived_quantity", def: "the obsolete witness", ref: "thm:main",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const edits = [
      {
        kind: "statement-delete" as const, id: "thm:main",
        reason: "retire the obsolete theorem", direction: "delete-obsolete" as const,
      },
      {
        kind: "symbol-delete" as const, name: "main_witness",
        reason: "retire its sole symbol reference", direction: "delete-obsolete" as const,
      },
    ];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const ownsMain = targets.some(({ id }) => id === "thm:main");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter(({ id }) => id !== "thm:main")
            .map(({ id }) => ({ id, proof_tex: `QED ${id}.` })),
          proposed_core_edits: ownsMain ? edits : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const solve = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(solve).toMatchObject({ status: "checkpoint", advance: false });
    expect((await readSurfacedProposals(ctx)).coreEdits).toEqual(expect.arrayContaining(edits));

    const preview = await applyProposedChanges({ ctx, checkOnly: true });
    expect(preview).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: "thm:main" }),
      expect.objectContaining({ id: "sym:main_witness" }),
    ]));
    expect(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")).statements)
      .toContainEqual(expect.objectContaining({ id: "thm:main" }));

    await applyProposedChanges({ ctx });
    const applied = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(applied.statements.some((statement: any) => statement.id === "thm:main")).toBe(false);
    expect(applied.symbols.some((symbol: any) => symbol.name === "main_witness")).toBe(false);

    await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") });
    const restarted = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(restarted.statements.some((statement: any) => statement.id === "thm:main")).toBe(false);
    expect(restarted.symbols.some((symbol: any) => symbol.name === "main_witness")).toBe(false);
  });

  it("deletes an obsolete statement, remaps inbound edges, and prevents carried-state resurrection", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const obsolete = {
      ...proto.statements[0],
      id: "conj:obsolete-result",
      kind: "conjecture",
      statement: "the obsolete result holds",
      status: "to-prove",
    };
    proto.statements = [
      obsolete,
      { ...proto.statements[1], depends_on: ["ass:overlap", "conj:obsolete-result"] },
    ];
    proto.assumptions[0].used_by = ["conj:obsolete-result", "prop:aux"];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");

    const canonical = {
      ...obsolete,
      id: "thm:canonical-result",
      kind: "theorem",
      statement: "the canonical result holds",
      depends_on: ["ass:overlap"],
      status: "proved",
      proof_tex: "Canonical proof.",
    };
    await saveWorkingState(ctx, {
      round: 4,
      solved: {
        "conj:obsolete-result": {
          proof_tex: "Legacy duplicate.",
          snapshot: { stmt: obsolete.statement, depends_on: obsolete.depends_on, defs: {}, assumptions: {} },
          node: { ...obsolete, status: "proved", proof_tex: "Legacy duplicate." },
          partial: true,
        },
        "thm:canonical-result": {
          proof_tex: canonical.proof_tex,
          snapshot: { stmt: canonical.statement, depends_on: canonical.depends_on, defs: {}, assumptions: { "ass:overlap": proto.assumptions[0].condition } },
          node: canonical,
        },
        "prop:carried-consumer": {
          proof_tex: "Use the old name.",
          snapshot: { stmt: "a carried result", depends_on: ["conj:obsolete-result"], defs: {}, assumptions: {} },
          node: {
            id: "prop:carried-consumer",
            kind: "proposition",
            statement: "a carried result",
            depends_on: ["conj:obsolete-result"],
            status: "proved",
            proof_tex: "Use the old name.",
          },
        },
      },
    });
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "statement-delete",
      id: "conj:obsolete-result",
      replacement_id: "thm:canonical-result",
      reason: "canonical theorem supersedes the duplicate conjecture",
      direction: "delete-obsolete",
    }] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.statements.some((s: any) => s.id === "conj:obsolete-result")).toBe(false);
    expect(updated.statements.find((s: any) => s.id === "prop:aux").depends_on).toEqual([
      "ass:overlap",
      "thm:canonical-result",
    ]);
    // The replacement theorem is agent-added and therefore lives only in the working
    // cursor.  An unrelated delete must not erase it from the assumption's direct
    // reverse edges when rebuilding the frozen proto.
    expect(updated.assumptions[0].used_by).toEqual(["def:class", "prop:aux", "thm:canonical-result"]);

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["conj:obsolete-result"]).toBeUndefined();
    expect(working.solved["prop:carried-consumer"].node.depends_on).toEqual(["thm:canonical-result"]);
    expect(working.solved["prop:carried-consumer"].snapshot.depends_on).toEqual(["conj:obsolete-result"]);

    await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") });
    const rebuilt = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rebuilt.statements.some((s: any) => s.id === "conj:obsolete-result")).toBe(false);
    expect(rebuilt.statements.some((s: any) => s.id === "thm:canonical-result")).toBe(true);
  });

  it("does not classify a delete-and-replace dependency substitution as symbol-only debt", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    const obsolete = {
      ...proto.statements[0], id: "lem:old-basis", kind: "lemma",
      statement: "the old basis lemma", depends_on: [], status: "to-prove", free_symbols: ["tau"],
    };
    proto.statements = [obsolete];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const replacement = {
      ...obsolete, id: "lem:new-basis", statement: "the replacement basis lemma",
    };
    const helper = {
      id: "thm:rewired-helper", kind: "theorem", statement: "the helper conclusion",
      depends_on: [obsolete.id], status: "to-prove", free_symbols: ["tau"],
    } as any;
    const consumer = {
      id: "prop:rewired-consumer", kind: "proposition", statement: "the consumer conclusion",
      depends_on: [helper.id], status: "to-prove", free_symbols: ["tau"],
    } as any;
    await saveWorkingState(ctx, {
      round: 4,
      symbol_basis: symbolBasis(proto, [replacement, helper, consumer]),
      solved: {
        [obsolete.id]: {
          node: obsolete, owner: helper.id, proof_tex: "Old proof.", snapshot: snapshotMember(proto, obsolete),
        },
        [replacement.id]: {
          node: replacement, owner: helper.id, proof_tex: "Replacement proof.", snapshot: snapshotMember(proto, replacement),
        },
        [helper.id]: {
          node: helper, owner: consumer.id, proof_tex: "Helper proof.", snapshot: snapshotMember(proto, helper),
        },
        [consumer.id]: {
          node: consumer, owner: consumer.id, proof_tex: "Consumer proof.", snapshot: snapshotMember(proto, consumer),
        },
      },
    });
    await seedWorkingProposals(ctx, {
      proofs: [{ id: consumer.id, proof_tex: "Consumer proof." }],
      coreEdits: [
        {
          kind: "statement-delete", id: obsolete.id, replacement_id: replacement.id,
          reason: "replace the proof basis", direction: "delete-obsolete",
        },
        {
          kind: "symbol-replace", name: "tau",
          proposed: { ...proto.symbols[0], def: "the corrected target meaning" },
          reason: "correct the global target meaning", direction: "correct",
        },
      ],
    });

    await expect(applyProposedChanges({ ctx })).rejects.toThrow(
      /reviewed provisional proof.*did not reach a complete exact postimage/i,
    );
    const unchanged = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(unchanged.statements.some((node: any) => node.id === obsolete.id)).toBe(true);
    expect(unchanged.symbols[0].def).toBe(proto.symbols[0].def);
  });

  it("deletes a helper and its sole consumer as one atomic bundle", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements = [
      {
        ...proto.statements[0], id: "lem:bundle-helper", kind: "lemma",
        statement: "an intermediate fact", depends_on: ["ass:overlap"], status: "to-prove",
      },
      {
        ...proto.statements[1], id: "thm:bundle-consumer", kind: "theorem",
        statement: "a result using the intermediate fact", depends_on: ["lem:bundle-helper"], status: "to-prove",
      },
    ];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [
      {
        kind: "statement-delete", id: "lem:bundle-helper",
        reason: "remove rejected helper", direction: "delete-obsolete",
      },
      {
        kind: "statement-delete", id: "thm:bundle-consumer",
        reason: "remove rejected consumer", direction: "delete-obsolete",
      },
    ] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(updated.statements.some((statement: any) => statement.id === "lem:bundle-helper")).toBe(false);
    expect(updated.statements.some((statement: any) => statement.id === "thm:bundle-consumer")).toBe(false);
  });

  it("applies a metadata-only statement replacement while preserving the frozen claim", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "statement-replace",
      id: "prop:aux",
      proposed: {
        ...proto.statements[1],
        depends_on: ["ass:overlap", "def:env"],
        consumer: "thm:main and the exact finite certificate",
      },
      reason: "declare the dependency and synchronized consumer metadata",
      direction: "correct",
    }] });

    await applyProposedChanges({ ctx });

    const updated = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const statement = updated.statements.find((s: any) => s.id === "prop:aux");
    expect(statement.statement).toBe(PROTO.statements[1].statement);
    expect(statement.depends_on).toEqual(["ass:overlap", "def:env"]);
    expect(statement.consumer).toContain("exact finite certificate");
  });

  it("atomically composes a claim change with a metadata replacement on one carried node", async () => {
    const ctx = makeCtx(repoRoot);
    const node = {
      id: "lem:composed-agent-node",
      kind: "lemma",
      statement: "The old combined claim holds.",
      depends_on: ["ass:overlap"],
      status: "proved",
      proof_tex: "Old proof.",
    } as any;
    await saveWorkingState(ctx, {
      round: 5,
      solved: {
        [node.id]: {
          proof_tex: node.proof_tex,
          snapshot: { stmt: node.statement, depends_on: node.depends_on, defs: {}, assumptions: { "ass:overlap": PROTO.assumptions[0].condition } },
          node,
          owner: "thm:main",
        },
      },
    });
    await seedWorkingProposals(ctx, { statements: [{
      id: node.id,
      current: node.statement,
      proposed: "The narrowed transport-only claim holds.",
      reason: "separate estimator-side content",
      direction: "narrow",
    }] });
    await seedWorkingProposals(ctx, { coreEdits: [{
      kind: "statement-replace",
      id: node.id,
      proposed: {
        ...node,
        statement: "The narrowed transport-only claim holds.",
        status: "to-prove",
        depends_on: ["ass:overlap", "def:env"],
      },
      reason: "declare the corrected dependency spine",
      direction: "correct",
    }] });

    await applyProposedChanges({ ctx });

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[node.id]).toMatchObject({
      partial: true,
      node: {
        statement: "The narrowed transport-only claim holds.",
        depends_on: ["ass:overlap", "def:env"],
        status: "to-prove",
      },
    });
  });

  it("keeps a corrected carried citation schema-valid while marking it for revalidation", async () => {
    const ctx = makeCtx(repoRoot);
    const node = {
      id: "lem:carried-comparator",
      kind: "lemma",
      statement: "The old comparator claim.",
      depends_on: [],
      status: "cited",
      source: {
        cite: "Rosenbaum1983",
        locator: "Section 1",
        verbatim_statement: "Old source claim.",
      },
    } as any;
    await saveWorkingState(ctx, {
      round: 5,
      solved: {
        [node.id]: {
          proof_tex: "",
          snapshot: { stmt: node.statement, depends_on: [], defs: {}, assumptions: {} },
          node,
        },
      },
    });
    await seedWorkingProposals(ctx, { statements: [{
      id: node.id,
      current: node.statement,
      proposed: "The corrected comparator claim.",
      reason: "align the source claim",
      direction: "narrow",
    }] });
    await seedWorkingProposals(ctx, { coreEdits: [withCorrectionPairs({
      proposed_statement_changes: [{ id: node.id, proposed: "The corrected comparator claim." }],
    }, { ...PROTO, statements: [...PROTO.statements, node] }).proposed_core_edits[0]] });

    await applyProposedChanges({ ctx });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[node.id]).toMatchObject({
      partial: true,
      node: {
        statement: "The corrected comparator claim.",
        status: "cited",
        source: { cite: "Rosenbaum1983" },
      },
    });
  });

  it("fails before proto mutation when the stage pointer cannot be durably rewound", async () => {
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, { statements: [{
      id: "thm:main",
      current: "tau is identified",
      proposed: "tau is identified under overlap",
      reason: "scope correction",
      direction: "narrow",
    }] });
    const sp = statePath(repoRoot, QID, SPEC);
    await mkdir(path.dirname(sp), { recursive: true });
    await writeFile(sp, "{truncated", "utf8");
    const before = await readFile(protoCoreJsonPath(ctx), "utf8");

    await expect(applyProposedChanges({ ctx })).rejects.toThrow();
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
    // the un-applied proposal survives on the carrier
    expect((await readSurfacedProposals(ctx)).statements).toHaveLength(1);
    await rm(sp, { force: true });
  });

  it("rejects a stale carried-node correction without mutating frozen proto provenance", async () => {
    const ctx = makeCtx(repoRoot);
    const carriedStatement = "A fully formatted corrected solver-added lemma.";
    await writeFile(workingPath(ctx), JSON.stringify({
      round: 7,
      solved: {
        "lem:solver-added": {
          proof_tex: "The claimed inequality follows.",
          snapshot: {
            stmt: carriedStatement,
            depends_on: ["ass:overlap"],
            defs: {},
            assumptions: { "ass:overlap": PROTO.assumptions[0].condition },
          },
          node: {
            id: "lem:solver-added",
            kind: "lemma",
            statement: carriedStatement,
            depends_on: ["ass:overlap"],
            status: "proved",
            proof_tex: "The claimed inequality follows.",
          },
          owner: "thm:main",
        },
      },
    }), "utf8");
    await seedWorkingProposals(ctx, { statements: [{
      id: "lem:solver-added",
      current: "An older weak version.",
      proposed: "A concise rendering of the corrected lemma.",
      reason: "approve the proved solver-added correction",
      direction: "correct",
    }] });
    await seedWorkingProposals(ctx, { coreEdits: [withCorrectionPairs({
      proposed_statement_changes: [{
        id: "lem:solver-added",
        proposed: "A concise rendering of the corrected lemma.",
      }],
    }, {
      ...PROTO,
      statements: [{
        id: "lem:solver-added",
        kind: "lemma",
        statement: carriedStatement,
        depends_on: ["ass:overlap"],
        status: "proved",
        proof_tex: "The claimed inequality follows.",
      }],
    }).proposed_core_edits[0]] });
    const pair = (await readSurfacedProposals(ctx)).coreEdits[0];
    await seedWorkingProposals(ctx, { coreEdits: [pair, {
      kind: "rebuild-reverse-dependencies",
      id: "metadata:reverse-dependencies",
      reason: "must not mask the stale selected statement variant",
      direction: "correct",
    }] });

    const before = await readFile(protoCoreJsonPath(ctx), "utf8");
    await expect(applyProposedChanges({ ctx, ids: new Set(["lem:solver-added"]) })).rejects.toThrow(
      /Refusing partial D0 apply/,
    );
    const after = await readFile(protoCoreJsonPath(ctx), "utf8");
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));

    expect(JSON.parse(after)).toEqual(JSON.parse(before));
        expect(working.solved["lem:solver-added"].node.statement).toBe(carriedStatement);
    expect((await readSurfacedProposals(ctx)).statements).toHaveLength(1);
  });

  it("fails closed on a corrupt working cursor instead of silently dropping carried nodes", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(workingPath(ctx), "{truncated", "utf8");
    await expect(runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") })).rejects.toThrow(
      /working cursor is corrupt.*refusing to discard carried nodes/i,
    );
  });

  it("resolves an AGENT-ADDED oeq without crashing on the source fingerprint", async () => {
    // The resolution fingerprint used to be computed from `sourceById`, which is built
    // from the FROZEN proto alone. A previous round can create an `oeq:` node in WORKING
    // state (an honest out-of-scope question surfaced while proving something else), and
    // resolving it in a later round then looked up a node no surviving map contained —
    // the `source!` assertion turned that into `TypeError: ... reading 'kind'` AFTER the
    // whole solve had been paid for. The frozen-oeq test above never covered this,
    // because a frozen oeq is in the proto by construction.
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(PROTO), "utf8");
    const oeqStatement = "Does the converse extend to nonvanishing schedules?";
    await writeFile(workingPath(ctx), JSON.stringify({
      round: 3,
      solved: {
        "oeq:agent-added-open-question": {
          proof_tex: "",
          snapshot: {
            stmt: oeqStatement,
            depends_on: ["ass:overlap"],
            defs: {},
            assumptions: { "ass:overlap": PROTO.assumptions[0].condition },
          },
          node: {
            id: "oeq:agent-added-open-question",
            kind: "openendedquestion",
            statement: oeqStatement,
            depends_on: ["ass:overlap"],
            status: "to-prove",
          },
          owner: "thm:main",
        },
      },
    }), "utf8");

    // The solve fans out over units; emit the resolution from exactly ONE of them, or
    // the duplicate-resolution guard fires before the code under test is reached.
    let emittedResolution = false;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const targetBlock = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "")
          .split("SOLVE_OUTPUT_PATH")[0];
        const mine = targetBlock.includes('"id": "oeq:agent-added-open-question"') && !emittedResolution;
        if (mine) emittedResolution = true;
        await writeFile(outPath, JSON.stringify({
          proofs: [],
          resolved_oeqs: mine ? [{
            source_id: "oeq:agent-added-open-question",
            theorem: {
              id: "thm:agent-added-answer",
              kind: "theorem",
              statement: "It does not extend; the witness fails off the vanishing regime.",
              depends_on: ["ass:overlap"],
              status: "proved",
              proof_tex: "Direct argument.",
            },
          }] : [],
          added_lemmas: [],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
          proposed_assumptions: [],
          proposed_core_edits: [],
          open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const invariantWarnings: string[] = [];
    const warnSpy = vi.spyOn(console, "warn").mockImplementation((...args: unknown[]) => {
      invariantWarnings.push(args.map(String).join(" "));
    });
    try {
      await runStage0Solve({ ctx, state: makeState(), deps });
    } finally {
      warnSpy.mockRestore();
    }
    expect(invariantWarnings.join("\n")).not.toContain("silent-node-loss");

    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.some((s: any) => s.id === "oeq:agent-added-open-question")).toBe(false);
    expect(core.statements.find((s: any) => s.id === "thm:agent-added-answer"))
      .toMatchObject({ status: "proved" });
    // The fingerprint must be RECORDED, not merely survive: it is what lets a later round
    // detect that the answered question itself changed underneath the answer.
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.resolved_oeqs["oeq:agent-added-open-question"]).toMatchObject({
      theorem_id: "thm:agent-added-answer",
    });
    expect(working.resolved_oeqs["oeq:agent-added-open-question"].source_fingerprint).toContain(
      "openendedquestion",
    );

    // A later directive may need the RESOLVED semantic owner again. The source no
    // longer exists in proto or solved; recover it only from its canonical fingerprint
    // and dispatch it under the same OEQ -> theorem capability.
    await appendEscalationLog(ctx, {
      round: working.round,
      changed: [],
      directive: "revalidate the resolved agent-authored answer without reopening it",
      require_core_changes: true,
      required_core_targets: ["oeq:agent-added-open-question"],
    });
    emittedResolution = false;
    await runStage0Solve({ ctx, state: makeState(), deps });
    const resumed = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(resumed.resolved_oeqs["oeq:agent-added-open-question"]).toMatchObject({
      theorem_id: "thm:agent-added-answer",
    });
    expect(JSON.parse(resumed.resolved_oeqs["oeq:agent-added-open-question"].source_fingerprint))
      .toMatchObject({ kind: "openendedquestion", statement: oeqStatement });
  });

  it("refuses a recovered cited-source substitution through added_lemmas", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [
        { id: "thm:main", kind: "theorem", statement: "tau is identified", depends_on: ["ass:overlap"], status: "to-prove", justification: "core ID", gap: "vs prior", consumer: "applied" },
      ],
    }), "utf8");
    let calls = 0;
    const citedNode = {
      id: "lem:current-comparator",
      kind: "lemma",
      statement: "The current comparator studies a distinct regular regime.",
      depends_on: [],
      status: "cited",
      source: {
        cite: "Rosenbaum1983",
        locator: "Section 1",
        verbatim_statement: "A distinct regular regime.",
      },
      proof_tex: null,
    };
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        calls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const recoveringCitedTarget = prompt.includes('"id": "lem:current-comparator"');
        const emittedCitedNode = recoveringCitedTarget
          ? { ...citedNode, source: { ...citedNode.source, locator: "Section 2" } }
          : citedNode;
        await writeFile(outPath, JSON.stringify({
          proofs: recoveringCitedTarget ? [] : [{ id: "thm:main", proof_tex: "QED." }],
          added_lemmas: [emittedCitedNode],
          resolved_oeqs: [],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
          proposed_assumptions: [],
          proposed_core_edits: [],
          open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")).statements.find(
      (s: any) => s.id === citedNode.id,
    ).status).toBe("cited");

    // Reproduce a claim-change invalidation: the agent-authored cited lemma exists
    // only in the working catalog, is partial, and its snapshot names the old claim.
    // A required-target directive must recover this lemma as a dispatch root even
    // though ordinary stale helper lemmas are reached only through result roots.
    const staleWorking = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    staleWorking.solved[citedNode.id].partial = true;
    staleWorking.solved[citedNode.id].snapshot.stmt = "The comparator's previous claim.";
    await writeFile(workingPath(ctx), JSON.stringify(staleWorking), "utf8");

    await appendEscalationLog(ctx, {
      round: 2,
      changed: [],
      directive: "refresh the current comparator source object",
      require_core_changes: true,
      required_core_targets: [citedNode.id],
    });
    const collision = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(collision).toMatchObject({ status: "checkpoint", advance: false });
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toContainEqual(expect.objectContaining({
      category: "statement", target: citedNode.id,
      reason: "conflicted-dependency-consumer",
      payload: expect.objectContaining({ source: expect.objectContaining({ locator: "Section 2" }) }),
    }));
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);

    const rebuilt = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const rebuiltTarget = rebuilt.statements.find((s: any) => s.id === citedNode.id);
    expect(rebuiltTarget).toMatchObject({ status: "to-prove" });
    expect(rebuiltTarget.source?.locator).not.toBe("Section 2");
    expect(calls).toBe(2);
  });

  it("rediscovers a partial agent cited lemma consumed directly by a frozen statement", async () => {
    const ctx = makeCtx(repoRoot);
    const citedNode: CoreStatement = {
      id: "lem:carried-comparator",
      kind: "lemma",
      statement: "The cited comparator proves the conditional upper bound.",
      depends_on: [],
      status: "cited",
      source: {
        cite: "Rosenbaum1983",
        locator: "Section 1",
        verbatim_statement: "A conditional upper bound.",
      },
    };
    const proto = structuredClone(PROTO) as any;
    proto.statements[0].depends_on = ["ass:overlap", citedNode.id];
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 3,
      solved: {
        "thm:main": {
          proof_tex: "Use the cited comparator.",
          snapshot: {
            stmt: proto.statements[0].statement,
            depends_on: proto.statements[0].depends_on,
            defs: {},
            assumptions: { "ass:overlap": proto.assumptions[0].condition },
          },
        },
        [citedNode.id]: {
          proof_tex: "",
          snapshot: { stmt: citedNode.statement, depends_on: [], defs: {}, assumptions: {} },
          node: citedNode,
          partial: true,
        },
      },
    });
    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        prompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter(({ id }) => id !== citedNode.id).map(({ id }) => ({ id, proof_tex: "QED." })),
          added_lemmas: targets.some(({ id }) => id === citedNode.id) ? [citedNode] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });

    expect(prompts.some((prompt) => prompt.includes(`"id": "${citedNode.id}"`))).toBe(true);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[citedNode.id].partial).toBeUndefined();
    expect(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")).statements.find(
      (statement: any) => statement.id === citedNode.id,
    )).toMatchObject({ status: "cited" });
  });

  it("documents byte-faithful added_lemmas revalidation for reopened cited targets", async () => {
    const prompt = await readFile(
      new URL("../../src/discovery/prompts/D0/stage0_solve.txt", import.meta.url),
      "utf8",
    );
    expect(prompt).toMatch(/REVALIDATING A REOPENED CITED TARGET/);
    expect(prompt).toMatch(/re-emit that COMPLETE cited node byte-faithfully in `added_lemmas`/);
    expect(prompt).toMatch(/clears its carried `partial` snapshot/);
  });

  it("assigns directive-authorized paper prose to exactly one deterministic solve unit", async () => {
    const ctx = makeCtx(repoRoot);
    const routedProto = structuredClone(PROTO) as any;
    routedProto.statements.forEach((statement: any, index: number) => {
      statement.route = `Use the frozen proof route for target ${index + 1}.`;
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(routedProto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "synchronize the paper-wide summary after solving all targets",
    });
    const prompts: string[] = [];
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        prompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const owner = prompt.includes("You are the ONLY solve unit allowed to emit `prose_updates`");
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
          ...(owner ? { prose_updates: {
            tldr: "One canonical summary for the solved paper.",
            statement_notes: [{
              id: "thm:prior-round-answer",
              consumer: "This stale note must not abort the current structured solve.",
            }],
          } } : {}),
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });

    expect(prompts).toHaveLength(2);
    expect(prompts.filter((p) => p.includes("You are the ONLY solve unit allowed"))).toHaveLength(1);
    expect(prompts.filter((p) => p.includes("OMIT `prose_updates` entirely"))).toHaveLength(1);
    expect(prompts.every((p) => !p.includes("validate_output.ts"))).toBe(true);
    const ownerPrompt = prompts.find((p) => p.includes("You are the ONLY solve unit allowed"))!;
    const localPrompt = prompts.find((p) => p.includes("OMIT `prose_updates` entirely"))!;
    expect(ownerPrompt).toContain('"mode": "projected"');
    expect(localPrompt).toContain('"mode": "projected"');
    expect(localPrompt).toContain("CORE_SNAPSHOT_PATH:");
    expect(localPrompt).toContain("inspect that id selectively");
    const localTargetBlock = (localPrompt.split("=== TARGET STATEMENT(S) TO SOLVE")[1] ?? "")
      .split("SOLVE_OUTPUT_PATH")[0];
    expect(localTargetBlock).not.toContain('"statement":');
    expect(localTargetBlock).toContain('"route": "Use the frozen proof route for target');
    expect(localPrompt.split("=== FROZEN CORE SNAPSHOT")[0]).toContain('"statement":');
    const snapshotPath = /CORE_SNAPSHOT_PATH:\s*(\S+)/.exec(localPrompt)![1];
    expect(/CORE_SNAPSHOT_PATH:\s*(\S+)/.exec(ownerPrompt)![1]).toBe(snapshotPath);
    const snapshot = JSON.parse(await readFile(snapshotPath, "utf8"));
    expect(snapshot.statements.map((statement: any) => statement.id)).toEqual(["thm:main", "prop:aux"]);
    expect(snapshot.statements.every((statement: any) => /^rev:[a-f0-9]{64}$/.test(statement.revision))).toBe(true);
    expect(ownerPrompt).toContain(
      "sibling-only ids",
    );
    expect(ownerPrompt).toContain("inspect only the necessary prose or result records");
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.tldr).toBe("One canonical summary for the solved paper.");
    expect(core.statements.some((s: any) => s.id === "thm:prior-round-answer")).toBe(false);
  });

  it("invalidates all carried outputs when D-1.2 advances the proposal revision", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    const v1 = makeState();
    v1.proposed_from!.current_angle_index = 0;
    v1.proposed_from!.current_version = 1;
    const firstDeps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const body = {
          proofs: [{ id: "thm:a", proof_tex: "QED." }],
          added_lemmas: [{
            id: "lem:old-source-artifact",
            kind: "lemma",
            statement: "An agent-added route used only by the old source revision.",
            depends_on: [],
            status: "proved",
            proof_tex: "QED.",
          }],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
        };
        await writeFile(outPath, JSON.stringify(body), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStage0Solve({ ctx, state: v1, deps: firstDeps });
    expect(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")).statements.some(
      (s: any) => s.id === "lem:old-source-artifact",
    )).toBe(true);

    // The frozen claim text happens to be unchanged, but D-1.2 authored a new
    // proposal version that intentionally removed the old proof route.
    const v2 = makeState();
    v2.proposed_from!.current_angle_index = 0;
    v2.proposed_from!.current_version = 2;
    const second = countingDeps();
    await runStage0Solve({ ctx, state: v2, deps: second.deps });

    expect(second.calls()).toEqual([["thm:a"]]);
    const rebuilt = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rebuilt.statements.some((s: any) => s.id === "lem:old-source-artifact")).toBe(false);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.proposal_revision).toBe("angle:0/version:2");
  });

  it("reuses unchanged proofs (no agent on an identical re-run) and re-solves only the dependency-invalidated group", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");

    // round 1: solves thm:a from scratch.
    const c1 = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: c1.deps });
    expect(c1.calls()).toEqual([["thm:a"]]);

    // round 2: identical proto → fully reused, NO agent dispatched.
    const c2 = countingDeps();
    const r2 = (await runStage0Solve({ ctx, state: makeState(), deps: c2.deps })) as any;
    expect(c2.calls()).toEqual([]);
    expect(r2.message).toMatch(/reused/i);

    // round 3: correct def:env → thm:a (which depends on it) is invalidated → re-solved.
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    proto.definitions.find((d: any) => d.id === "def:env").construction = "U = a + b";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const c3 = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: c3.deps });
    expect(c3.calls()).toEqual([["thm:a"]]);
  });

  it("delivers a new standalone directive through one real dispatch, then resumes reuse", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...REUSE_PROTO,
      sampling_model: {
        design: "The old overbroad design description.",
        units: "Independent replicated units; this sibling must survive a design-only update.",
      },
    }), "utf8");

    const first = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: first.deps });
    expect(first.calls()).toEqual([["thm:a"]]);

    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "derive the sharp operational threshold before advancing",
    });
    const directedPrompts: string[] = [];
    const directed: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        directedPrompts.push(prompt);
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
          added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
          prose_updates: {
            tldr: "The sharp operational threshold is now proved.",
            honest_scope: "The finite threshold is settled; only sampling inference remains outside scope.",
            sampling_model: { design: "The corrected scoped design description." },
            statement_notes: [{ id: "thm:a", consumer: "Operational design screening." }],
          },
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStage0Solve({ ctx, state: makeState(), deps: directed });
    expect(directedPrompts).toHaveLength(1);
    expect(directedPrompts[0]).toContain("derive the sharp operational threshold before advancing");
    const directedCore = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const directedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    // Phase 1: prose lands in the rendered core (via the working overlay); the
    // frozen proto is NEVER written mid-round.
    expect(directedCore.tldr).toBe("The sharp operational threshold is now proved.");
    expect(directedCore.honest_scope).toContain("threshold is settled");
    expect(directedCore.sampling_model).toEqual({
      design: "The corrected scoped design description.",
      units: "Independent replicated units; this sibling must survive a design-only update.",
    });
    expect(directedCore.statements.find((s: any) => s.id === "thm:a").consumer).toBe("Operational design screening.");
    expect(directedProto.tldr).not.toBe("The sharp operational threshold is now proved.");
    expect(directedProto.statements.find((s: any) => s.id === "thm:a").consumer).not.toBe("Operational design screening.");

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.escalation_entries_consumed).toBe(1);
    const reused = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: reused.deps });
    expect(reused.calls()).toEqual([]);
  });

  // two theorems whose ONLY connection is a shared prop.
  const HUB_PROTO = {
    ...PROTO,
    statements: [
      { id: "prop:shared", kind: "proposition", statement: "S", depends_on: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      { id: "thm:a", kind: "theorem", statement: "A", depends_on: ["prop:shared", "def:env"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      { id: "thm:b", kind: "theorem", statement: "B", depends_on: ["prop:shared", "def:env"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ],
  };

  it("a proved-stable SHARED prop stops coupling its consumers — they re-solve as separate parallel groups (hub-prop fix)", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(HUB_PROTO), "utf8");

    // round 1: prop:shared is OPEN, so it couples thm:a and thm:b into ONE group/agent.
    const c1 = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: c1.deps });
    expect(c1.calls().length).toBe(1);
    expect([...c1.calls()[0]].sort()).toEqual(["prop:shared", "thm:a", "thm:b"]);

    // round 2: invalidate ONLY thm:a and thm:b (change def:env, which prop:shared does
    // not depend on). prop:shared stays valid → no longer couples a and b → TWO agents.
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    proto.definitions.find((d: any) => d.id === "def:env").construction = "U = a + b";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const c2 = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: c2.deps });
    expect(c2.calls().length).toBe(2);
    expect(c2.calls().map((c) => c.join()).sort()).toEqual(["thm:a", "thm:b"]);
  });

  // two coupled statements (prop:aux depends on thm:main → one group).
  const INCOMPLETE_PROTO = {
    ...PROTO,
    statements: [
      { id: "thm:main", kind: "theorem", statement: "M", depends_on: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      { id: "prop:aux", kind: "proposition", statement: "X", depends_on: ["thm:main"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ],
  };

  // agent that proves ONLY thm:main and leaves prop:aux open (no proposed change).
  function partialDeps(): StageDeps {
    return {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const body = { proofs: [{ id: "thm:main", proof_tex: "QED." }], added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [] };
        await writeFile(outPath, JSON.stringify(body), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
  }

  it("an incomplete round (some targets unproved, no proposal) checkpoints-and-continues instead of throwing", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(INCOMPLETE_PROTO), "utf8");
    const res = (await runStage0Solve({ ctx, state: makeState(), deps: partialDeps() })) as any;
    expect(res.status).toBe("checkpoint");
    expect(res.advance).toBe(false);
    expect(res.message).toMatch(/incomplete/i);
    expect(res.message).toMatch(/prop:aux/); // names the still-open target
    // partial progress is saved for reuse next round.
    const w = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(w.solved["thm:main"]).toBeDefined();
    expect(w.solved["prop:aux"]).toBeUndefined();
  });

  it("does NOT invalidate a statement when an UNRELATED def changes", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(REUSE_PROTO), "utf8");
    await runStage0Solve({ ctx, state: makeState(), deps: countingDeps().deps }); // round 1

    // change def:class (thm:a does NOT depend on it) → thm:a stays valid → no agent.
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    proto.definitions.find((d: any) => d.id === "def:class").construction = "{ P : different }";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    const c2 = countingDeps();
    await runStage0Solve({ ctx, state: makeState(), deps: c2.deps });
    expect(c2.calls()).toEqual([]);
  });
});

describe("records-only merge (Batch B constructions)", () => {
  it("a frozen claim CANNOT be silently altered: the emission is withheld and the render keeps the proto text", async () => {
    // The old `silentAlterationViolations` guard policed this after the fact;
    // with a records-only merge the state is unrepresentable — an added_lemmas
    // emission under a frozen id with a different claim is a withheld collision.
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          // An ALTERED frozen claim smuggled through added_lemmas:
          added_lemmas: targets.some((t) => t.id === "thm:main") ? [{
            id: "thm:main", kind: "theorem", statement: "a silently weakened claim",
            depends_on: ["ass:overlap"], status: "proved", proof_tex: "bogus",
          }] : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    // The collision is surfaced for adjudication, never applied.
    expect(result.status).toBe("checkpoint");
    expect(result.message).toMatch(/WITHHELD/);
    const published = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const main = published.statements.find((s: any) => s.id === "thm:main");
    expect(main.statement).toBe("tau is identified");
    expect(main.status).toBe("to-prove");
  });

  it("every published agent node has a working record — nothing exists outside the cursor", async () => {
    // The deleted checkpoint-withheld recording loop's guarantee, now structural:
    // installs ARE records, so render ⊆ proto ∪ cursor on any halt.
    const ctx = makeCtx(repoRoot);
    const result = await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("propose") }) as any;
    expect(result.status).toBe("checkpoint");
    const published = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const cursor = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const protoIds = new Set(PROTO.statements.map((s) => s.id));
    for (const s of published.statements) {
      expect(protoIds.has(s.id) || cursor.solved[s.id] !== undefined).toBe(true);
    }
  });
});

describe("Stage 0-SOLVE (per thm/conj + props; proofs + lemmas + statement-change escalation)", () => {
  it("rewires an assumption's used_by reverse edge onto the replacement theorem", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      assumptions: [{ ...PROTO.assumptions[0], used_by: ["oeq:sharp-rate", "thm:consumer"] }],
      statements: [
        { id: "oeq:sharp-rate", kind: "openendedquestion", statement: "What is the sharp rate?", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "thm:consumer" },
        { id: "thm:consumer", kind: "theorem", statement: "The procedure uses the sharp rate", depends_on: ["oeq:sharp-rate", "ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      ],
    }), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:consumer", proof_tex: "By thm:sharp-rate-answer." }],
          resolved_oeqs: [{ source_id: "oeq:sharp-rate", theorem: {
            id: "thm:sharp-rate-answer", kind: "theorem", statement: "The sharp rate is n^{-1/2}",
            depends_on: [], status: "proved", proof_tex: "Directly from ass:overlap.",
          } }],
          added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
          proposed_assumptions: [], open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    // The OEQ node is gone, so a `used_by` still naming it dangles at the D->F boundary.
    expect(core.assumptions.find((a: any) => a.id === "ass:overlap").used_by)
      .toEqual(["def:class", "thm:consumer", "thm:sharp-rate-answer"]);
    expect(core.statements.find((s: any) => s.id === "thm:sharp-rate-answer").depends_on)
      .toContain("ass:overlap");

    // A resume rebuilds the core from the frozen proto (whose `used_by` still names the
    // OEQ) and re-applies the PERSISTED replacement, so it must remap the reverse edge too.
    await runStage0Solve({ ctx, state: makeState(), deps });
    const resumed = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(resumed.statements.some((s: any) => s.id === "oeq:sharp-rate")).toBe(false);
    expect(resumed.assumptions.find((a: any) => a.id === "ass:overlap").used_by)
      .toEqual(["def:class", "thm:consumer", "thm:sharp-rate-answer"]);
  });

  it("an answer theorem that cites the question it settles inherits the question's edges (no self-cycle, no dangling id)", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [
        { id: "oeq:sharp-rate", kind: "openendedquestion", statement: "What is the sharp rate?", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "thm:consumer" },
        { id: "thm:consumer", kind: "theorem", statement: "The procedure uses the sharp rate", depends_on: ["oeq:sharp-rate"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      ],
    }), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:consumer", proof_tex: "By thm:sharp-rate-answer." }],
          resolved_oeqs: [{ source_id: "oeq:sharp-rate", theorem: {
            id: "thm:sharp-rate-answer", kind: "theorem", statement: "The sharp rate is n^{-1/2}",
            // The answer names the question it settles — the realistic worker shape.
            depends_on: ["oeq:sharp-rate"], status: "proved", proof_tex: "Directly from ass:overlap.",
          } }],
          added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
          proposed_assumptions: [], open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const check = async () => {
      const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
      const answer = core.statements.find((s: any) => s.id === "thm:sharp-rate-answer");
      expect(answer.depends_on).toEqual(["ass:overlap"]);
      expect(core.statements.find((s: any) => s.id === "thm:consumer").depends_on).toEqual(["thm:sharp-rate-answer"]);
      expect(core.statements.some((s: any) => s.id === "oeq:sharp-rate")).toBe(false);
    };
    await expect(runStage0Solve({ ctx, state: makeState(), deps })).resolves.toBeDefined();
    await check();
    await runStage0Solve({ ctx, state: makeState(), deps }); // resume is idempotent
    await check();
  });

  it("replaces a proved OEQ, rewires consumers, and preserves the replacement on retry", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [
        { id: "oeq:sharp-rate", kind: "openendedquestion", statement: "What is the sharp rate?", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "thm:consumer" },
        { id: "thm:consumer", kind: "theorem", statement: "The procedure uses the sharp rate", depends_on: ["oeq:sharp-rate"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      ],
    }), "utf8");
    let calls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        calls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: "thm:consumer", proof_tex: "By thm:sharp-rate-answer." }],
          resolved_oeqs: [{ source_id: "oeq:sharp-rate", theorem: {
            id: "thm:sharp-rate-answer", kind: "theorem", statement: "The sharp rate is n^{-1/2}",
            depends_on: ["ass:overlap"], status: "proved", proof_tex: "Direct calculation.",
          } }],
          added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
          proposed_assumptions: [], open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.some((s: any) => s.id === "oeq:sharp-rate")).toBe(false);
    expect(core.statements.find((s: any) => s.id === "thm:sharp-rate-answer")).toMatchObject({
      kind: "theorem", status: "proved", statement: "The sharp rate is n^{-1/2}",
    });
    expect(core.statements.find((s: any) => s.id === "thm:consumer").depends_on).toContain("thm:sharp-rate-answer");

    // A D0 retry rebuilds from proto_core.json. First remove the new mapping to
    // exercise compatibility with working states written before this field existed.
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    delete working.resolved_oeqs;
    await writeFile(workingPath(ctx), JSON.stringify(working), "utf8");

    // Legacy state has no source fingerprint, so it is conservatively re-solved;
    // its stale theorem must not collide with the freshly emitted answer.
    await runStage0Solve({ ctx, state: makeState(), deps });
    const retried = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(calls).toBe(2);
    expect(retried.statements.some((s: any) => s.id === "oeq:sharp-rate")).toBe(false);
    expect(retried.statements.filter((s: any) => s.id === "thm:sharp-rate-answer")).toHaveLength(1);
    expect(retried.statements.find((s: any) => s.id === "thm:consumer").depends_on).toContain("thm:sharp-rate-answer");

    // Changing the frozen OEQ itself invalidates its old answer. It must be
    // dispatched and normalized again, not silently retained by the mapping.
    const changedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    changedProto.statements.find((s: any) => s.id === "oeq:sharp-rate").statement = "What is the sharp adaptive rate?";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(changedProto), "utf8");
    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls).toBe(3);
  });

  it("preserves additional theorem helpers emitted by an OEQ-led solve unit", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [
        { id: "oeq:sharp-rate", kind: "openendedquestion", statement: "What is the sharp rate?", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      ],
    }), "utf8");
    let calls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        calls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const reproveAgentNodes = prompt.includes('"id": "thm:independent-corollary"');
        await writeFile(outPath, JSON.stringify(reproveAgentNodes ? {
          proofs: [
            { id: "lem:auxiliary-bound", proof_tex: "Elementary under the corrected definition." },
            { id: "thm:independent-corollary", proof_tex: "Apply the re-proved auxiliary bound." },
          ],
          resolved_oeqs: [], added_lemmas: [], proposed_statement_changes: [],
          proposed_definition_changes: [], proposed_assumptions: [], open_obligations: [],
        } : {
          proofs: [],
          resolved_oeqs: [{ source_id: "oeq:sharp-rate", theorem: {
            id: "thm:sharp-rate-answer", kind: "theorem", statement: "The sharp rate is n^{-1/2}.",
            depends_on: ["ass:overlap"], status: "proved", proof_tex: "Direct calculation.",
          } }],
          added_lemmas: [
            {
              id: "lem:auxiliary-bound", kind: "lemma", statement: "An auxiliary bound holds.",
              depends_on: ["def:class"], status: "proved", proof_tex: "Elementary.",
            },
            {
              id: "thm:independent-corollary", kind: "theorem", statement: "A separate corollary holds.",
              depends_on: ["lem:auxiliary-bound"], status: "proved", proof_tex: "Apply the auxiliary bound.",
            },
          ],
          proposed_statement_changes: [], proposed_definition_changes: [],
          proposed_assumptions: [], open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    await runStage0Solve({ ctx, state: makeState(), deps });
    const firstWorking = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(firstWorking.solved["thm:independent-corollary"].owner).toBe("oeq:sharp-rate");

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls).toBe(1);
    const resumed = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(resumed.statements.some((s: any) => s.id === "thm:independent-corollary")).toBe(true);
    expect(resumed.statements.some((s: any) => s.id === "lem:auxiliary-bound")).toBe(true);

    const changedProto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    changedProto.definitions.find((d: any) => d.id === "def:class").construction = "{ P : corrected class }";
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(changedProto), "utf8");
    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls).toBe(2);
    const reproved = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(reproved.statements.find((s: any) => s.id === "lem:auxiliary-bound").proof_tex)
      .toContain("corrected definition");
    expect(reproved.statements.find((s: any) => s.id === "thm:independent-corollary").proof_tex)
      .toContain("re-proved auxiliary bound");

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls).toBe(2);
  });

  it("applies directive-authorized prose notes to a resolved OEQ theorem id", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [{
        id: "oeq:sharp-rate", kind: "openendedquestion", statement: "What is the sharp rate?",
        depends_on: ["ass:overlap"], status: "to-prove", justification: "open",
        gap: "unknown", consumer: "future work",
      }],
    }), "utf8");
    await appendEscalationLog(ctx, {
      round: 0,
      changed: [],
      directive: "solve the question and synchronize its theorem note",
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, JSON.stringify({
          proofs: [],
          resolved_oeqs: [{ source_id: "oeq:sharp-rate", theorem: {
            id: "thm:sharp-rate-answer", kind: "theorem", statement: "The sharp rate is n^{-1/2}",
            depends_on: ["ass:overlap"], status: "proved", proof_tex: "Direct calculation.",
          } }],
          added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
          prose_updates: {
            statement_notes: [{
              id: "thm:sharp-rate-answer",
              justification: "This closes the rate question.",
              consumer: "Use the exact rate for inference.",
            }],
          },
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    await runStage0Solve({ ctx, state: makeState(), deps });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const answer = core.statements.find((s: any) => s.id === "thm:sharp-rate-answer");
    expect(answer.justification).toBe("This closes the rate question.");
    expect(answer.consumer).toBe("Use the exact rate for inference.");
    // Batch B (records-only merge): the ONE durable carrier of prose notes is
    // the working overlay — every render re-applies it, so the note survives
    // re-opens without a per-record copy to keep in sync.
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.prose_overlay.statement_notes["thm:sharp-rate-answer"].consumer)
      .toBe("Use the exact rate for inference.");
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.statements.some((s: any) => s.id === "thm:sharp-rate-answer")).toBe(false);
  });

  it("proves all targets, discharges the gate, and writes the solved core", async () => {
    const ctx = makeCtx(repoRoot);
    const res = (await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") })) as any;
    expect(existsSync(coreJsonPath(ctx))).toBe(true);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.every((s: any) => s.status === "proved")).toBe(true);
    expect(res.solved).toBe(2);
    // frozen claims unchanged (no silent edit)
    expect(core.statements.find((s: any) => s.id === "thm:main").statement).toBe("tau is identified");
  });

  it("escalates a proposed statement change as a checkpoint (no silent change)", async () => {
    const ctx = makeCtx(repoRoot);
    const res = (await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("propose") })) as any;
    expect(res.status).toBe("checkpoint");
    expect(res.advance).toBe(false);
    expect(res.message).toMatch(/STATEMENT change/i);
    // the change is NOT applied — the core keeps the original claim
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:main").statement).toBe("tau is identified");
    const surfaced = await readSurfacedProposals(ctx);
    expect(surfaced.statements.length).toBeGreaterThan(0);
    const packet = JSON.parse(await readFile(proposalReviewPacketPath(ctx), "utf8"));
    expect(packet.durable_working_state.proposals).toEqual(surfaced);
  });

  it("pipeline-pins an omitted proposal revision and repairs non-whitespace current serialization", async () => {
    const ctx = makeCtx(repoRoot);
    const deps = solverDeps("propose");
    const originalRunCodex = deps.runCodex;
    deps.runCodex = async (args: any) => {
      const result = await originalRunCodex(args);
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(args.prompt)![1];
      const output = JSON.parse(await readFile(outPath, "utf8"));
      const change = output.proposed_statement_changes?.find((candidate: any) => candidate.id === "thm:main");
      if (change) {
        expect(change.based_on_revision).toBeUndefined();
        change.current = String.raw`tau is identifi\"ed`;
        await writeFile(outPath, JSON.stringify(output), "utf8");
      }
      return result;
    };

    const res = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(res.status).toBe("checkpoint");
    expect((await readSurfacedProposals(ctx)).statements).toContainEqual(
      expect.objectContaining({
        id: "thm:main",
        current: "tau is identified",
        based_on_revision: expect.stringMatching(/^rev:[a-f0-9]{64}$/),
      }),
    );
  });

  it("pipeline-pins one complete-definition revision onto both members of a correction pair", async () => {
    const ctx = makeCtx(repoRoot);
    const deps = solverDeps("propose-def");
    const runCodex = deps.runCodex;
    let displayedRevision: string | undefined;
    deps.runCodex = async (args: any) => {
      const snapshotPath = /CORE_SNAPSHOT_PATH:\s*(\S+)/.exec(args.prompt)?.[1];
      if (snapshotPath !== undefined) {
        const snapshot = JSON.parse(await readFile(snapshotPath, "utf8"));
        displayedRevision = snapshot.definitions.find((definition: any) => definition.id === "def:env")?.revision;
      }
      return runCodex(args);
    };
    const res = await runStage0Solve({ ctx, state: makeState(), deps }) as any;
    expect(res.status).toBe("checkpoint");
    const proposals = await readSurfacedProposals(ctx);
    const change = proposals.definitions.find((candidate: any) => candidate.id === "def:env");
    const replacement = proposals.coreEdits.find(
      (candidate: any) => candidate.kind === "definition-replace" && candidate.id === "def:env",
    );
    expect(displayedRevision).toMatch(/^rev:[a-f0-9]{64}$/);
    expect(change.based_on_revision).toBe(displayedRevision);
    expect(change.based_on_revision).toMatch(/^rev:[a-f0-9]{64}$/);
    expect(replacement.based_on_revision).toBe(change.based_on_revision);
    const surfacedCore = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(proposals.basis_revision).toBe(coreRevision(surfacedCore));
    await applyProposedChanges({ ctx });
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.definitions.find((definition: any) => definition.id === "def:env").construction)
      .toBe("U = a + b");
  });

  it("rejects a definition correction after the persisted assembled round basis drifts", async () => {
    const ctx = makeCtx(repoRoot);
    const res = await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("propose-def") }) as any;
    expect(res.status).toBe("checkpoint");
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    working.solved["prop:aux"].proof_tex = "A different durable proof.";
    await writeFile(workingPath(ctx), JSON.stringify(working), "utf8");
    await expect(applyProposedChanges({ ctx })).rejects.toThrow(/persisted assembled-core basis/);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.definitions.find((definition: any) => definition.id === "def:env").construction)
      .toBe("U = a");
  });

  it("escalates a GENUINE OPEN GAP as an orchestrator-guidance checkpoint (not auto-looped)", async () => {
    const ctx = makeCtx(repoRoot);
    // proto with one theorem that the solver will declare genuinely open.
    const openProto = {
      ...PROTO,
      statements: [
        { id: "thm:hard", kind: "theorem", statement: "the matched lower bound holds", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      ],
    };
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(openProto), "utf8");
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const body = {
          proofs: [],
          added_lemmas: [],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
          open_obligations: [{ node_id: "thm:hard", what_is_open: "bounded chi-square construction", obstruction: "does not close from L2 rates", attempted: "joint four-point family" }],
        };
        await writeFile(outPath, JSON.stringify(body), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    // runStage0Typed (the loop) must return the open-gap checkpoint immediately, NOT churn.
    let calls = 0;
    const countingWrap: StageDeps = { ...deps, runCodex: async (a: any) => { calls += 1; return deps.runCodex(a); } };
    const res = await runStage0Typed({ ctx, state: makeState(), deps: countingWrap });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/OPEN GAP/i);
    expect(res.message).toMatch(/guidance/i);
    expect(calls).toBe(1); // did NOT auto-loop on the open gap
    const obPath = path.join(path.dirname(coreJsonPath(ctx)), "open_obligations.json");
    expect(existsSync(obPath)).toBe(true);
  });

  it("escalates a proposed CONSTRUCTED-OBJECT definition change as a checkpoint (not applied)", async () => {
    const ctx = makeCtx(repoRoot);
    const res = (await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("propose-def") })) as any;
    expect(res.status).toBe("checkpoint");
    expect(res.advance).toBe(false);
    expect(res.message).toMatch(/DEFINITION change/i);
    // the def is NOT applied — core keeps the original construction
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.definitions.find((d: any) => d.id === "def:env").construction).toBe("U = a");
    expect((await readSurfacedProposals(ctx)).definitions.length).toBeGreaterThan(0);
  });

  it("IGNORES a proposed change targeting a CLASS definition (A6 firewall — not a formula fix)", async () => {
    const ctx = makeCtx(repoRoot);
    // clear any carrier payload left by a prior test in the shared repoRoot.
    await rm(workingPath(ctx), { force: true });
    const res = (await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("propose-def-class") })) as any;
    expect("status" in res ? res.status : "clean").not.toBe("checkpoint");
    expect(res.message).toMatch(/discharged/i);
    expect(res.message).toMatch(/ignored .*illegal class\/unknown def/i);
    expect(((await readSurfacedProposals(ctx)).definitions ?? []).length).toBe(0);
    expect(((await readSurfacedProposals(ctx)).coreEdits ?? []).length).toBe(0);
    expect(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")).definitions).toEqual(PROTO.definitions);
  });
});

describe("findingKeys (D0.5 loop non-convergence detection)", () => {
  it("keys findings by code@node and detects a finding surviving a D0.R edit", () => {
    const r0 = [{ findings: [{ code: "open-converse", node_id: "conj:tlb" }, { code: "x", node_id: "prop:p" }] }];
    const r1 = [{ findings: [{ code: "open-converse", node_id: "conj:tlb" }] }]; // same finding persists
    const k0 = findingKeys(r0 as any);
    const k1 = findingKeys(r1 as any);
    expect(k0.has("open-converse@conj:tlb")).toBe(true);
    const persistent = [...k1].filter((k) => k0.has(k));
    expect(persistent).toEqual(["open-converse@conj:tlb"]); // survived the edit → loop escalates
  });
  it("no persistence when the next round's findings are all different", () => {
    const k0 = findingKeys([{ findings: [{ code: "a", node_id: "n1" }] }] as any);
    const k1 = findingKeys([{ findings: [{ code: "b", node_id: "n2" }] }] as any);
    expect([...k1].filter((k) => k0.has(k))).toEqual([]); // genuine progress → keep iterating
  });
});

describe("partitionProposedChanges (all proposals checkpoint)", () => {
  const proto = {
    statements: [
      { id: "thm:head", kind: "theorem" },
      { id: "conj:c", kind: "conjecture" },
      { id: "prop:p", kind: "proposition" },
    ],
  } as any;

  it("GATES an assume-the-crux narrowing on a conjecture (adds a 'suppose … such that' premise)", () => {
    const stmts = [
      // legitimate scope narrowing still requires adjudication
      { id: "conj:c", current: "inf sup >= c R* over W_n.", proposed: "inf sup >= c R* over the subclass W_n^lb.", direction: "narrow" },
      // assume-the-crux → gate: promotes the hard property into a hypothesis
      { id: "prop:p", current: "The handle can be completed into a bounded-chi-square family and inf sup >= c R*.", proposed: "Suppose the handle is completed into a family such that the pairwise chi-square is < 4. Then inf sup >= c R*.", direction: "narrow" },
    ];
    const { auto, gated } = partitionProposedChanges(proto, stmts as any, []);
    expect([...auto]).toEqual([]);
    expect(gated.map((g) => g.id)).toEqual(["conj:c", "prop:p"]);
    expect(gated[1].why).toMatch(/assume-the-crux/i);
  });

  it("GATES a result-class degradation (drops the load-bearing lower bound to a fragment)", () => {
    const stmts = [
      // drops "inf sup ... >= c R_n^*" down to just a tau-diameter computation → gate
      { id: "conj:c", current: "H can be completed into a bounded-chi-square family with inf_{hat_tau} sup_{P} E_P|hat_tau - tau| >= c R_n^*.", proposed: "For every base law P, the family has tau(P_{s,t}) = tau(P) + s delta. The chi-square construction remains open.", direction: "narrow" },
    ];
    const { auto, gated } = partitionProposedChanges(proto, stmts as any, []);
    expect([...auto]).toEqual([]);
    expect(gated.map((g) => g.id)).toEqual(["conj:c"]);
    expect(gated[0].why).toMatch(/result-class degradation/i);
  });

  it("gates definition corrections and every faithful narrowing, including theorem headlines", () => {
    const defs = [
      { id: "def:env", proposed: "U=a+b", direction: "correct" },
      { id: "def:bad", proposed: "x", direction: "weaken" }, // wrong direction → gate
    ];
    const stmts = [
      { id: "conj:c", proposed: "...", direction: "narrow" },
      { id: "prop:p", proposed: "...", direction: "narrow" },
      { id: "thm:head", proposed: "...", direction: "narrow" },
    ];
    const { auto, gated } = partitionProposedChanges(proto, stmts as any, defs as any);
    expect([...auto]).toEqual([]);
    expect(gated.map((g) => g.id).sort()).toEqual(["conj:c", "def:bad", "def:env", "prop:p", "thm:head"]);
  });

  it("gates a proposed new assumption", () => {
    const { auto, gated } = partitionProposedChanges(
      proto,
      [],
      [],
      [{ id: "ass:new", condition: "the score envelope is bounded", standard_or_novel: "standard: DML, Chernozhukov2018" }] as any,
    );
    expect([...auto]).toEqual([]);
    expect(gated.map((g) => g.id)).toEqual(["ass:new"]);
  });

  it("STILL gates an assume-the-crux narrowing on a THEOREM (the laundering guard survives the theorem-auto change)", () => {
    const stmts = [
      { id: "thm:head", current: "inf sup >= c R* over W.", proposed: "Suppose the family is completed such that the pairwise chi-square is < 4. Then inf sup >= c R*.", direction: "narrow" },
    ];
    const { auto, gated } = partitionProposedChanges(proto, stmts as any, []);
    expect([...auto]).toEqual([]);
    expect(gated.map((g) => g.id)).toEqual(["thm:head"]);
    expect(gated[0].why).toMatch(/assume-the-crux/i);
  });

  it("GATES proof-object premises even when they contain generic bounded/family words", () => {
    const stmts = [
      {
        id: "prop:p",
        current: "Then the minimax lower bound holds.",
        proposed: "Suppose a bounded chi-square least-favorable family exists. Then the minimax lower bound holds.",
        direction: "narrow",
      },
    ];
    const { auto, gated } = partitionProposedChanges(proto, stmts as any, []);
    expect([...auto]).toEqual([]);
    expect(gated.map((g) => g.id)).toEqual(["prop:p"]);
  });
});

describe("auto-wire depends_on from proof citations", () => {
  // proto where the proof will cite a lemma + a def NOT pre-listed in depends_on.
  const WIRE_PROTO = {
    ...PROTO,
    statements: [
      { id: "thm:w", kind: "theorem", statement: "W", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ],
  };
  function citingDeps(): StageDeps {
    return {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const body = {
          // proof cites lem:helper (added) + def:env (existing) by literal id, but neither is in depends_on.
          proofs: [{ id: "thm:w", proof_tex: "By `lem:helper` and `def:env`, the bound follows." }],
          added_lemmas: [{ id: "lem:helper", kind: "lemma", statement: "H", depends_on: [], status: "proved", proof_tex: "trivial." }],
          proposed_statement_changes: [],
          proposed_definition_changes: [],
        };
        await writeFile(outPath, JSON.stringify(body), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
  }

  it("unions cited node ids into depends_on so the core discharges from declared deps", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(WIRE_PROTO), "utf8");
    await runStage0Solve({ ctx, state: makeState(), deps: citingDeps() });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const dep = core.statements.find((s: any) => s.id === "thm:w").depends_on;
    expect(dep).toContain("lem:helper"); // added lemma it cites
    expect(dep).toContain("def:env"); // existing def it cites
    expect(dep).toContain("ass:overlap"); // original edge preserved
  });
});

describe("groupToProveByComponent (dependency-aware unit grouping)", () => {
  const mk = (id: string, kind: string, depends_on: string[]) =>
    ({ id, kind, statement: id, depends_on, status: "to-prove" }) as any;

  it("puts independent statements in separate units (parallelizes)", () => {
    const units = groupToProveByComponent([
      mk("thm:a", "theorem", ["ass:x"]),
      mk("thm:b", "theorem", ["ass:y"]),
    ]);
    expect(units.map((u) => u.label).sort()).toEqual(["thm:a", "thm:b"]);
  });

  it("co-locates a prop that depends on a thm into one unit, led by the headline", () => {
    const units = groupToProveByComponent([
      mk("thm:main", "theorem", ["ass:x"]),
      mk("prop:aux", "proposition", ["thm:main"]),
    ]);
    expect(units).toHaveLength(1);
    expect(units[0].label).toBe("thm:main");
    expect(units[0].targets.map((t: any) => t.id).sort()).toEqual(["prop:aux", "thm:main"]);
  });

  it("merges a whole tightly-coupled cluster (conj↔prop↔thm) into one unit", () => {
    // mirrors the overlap-decay core: one weakly-connected component.
    const units = groupToProveByComponent([
      mk("thm:upper", "theorem", []),
      mk("prop:reduction", "proposition", []),
      mk("conj:lower", "conjecture", []),
      mk("conj:frontier", "conjecture", ["thm:upper", "prop:reduction", "conj:lower"]),
      mk("prop:phase", "proposition", ["conj:frontier"]),
    ]);
    expect(units).toHaveLength(1);
    expect(units[0].targets).toHaveLength(5);
    // lead is a headline (first thm/conj by original order)
    expect(units[0].label).toBe("thm:upper");
  });

  it("a dependency on an already-proved statement does NOT couple (only to-prove edges)", () => {
    // prop:aux depends on thm:done, but thm:done is not in the to-prove set → no edge.
    const units = groupToProveByComponent([mk("prop:aux", "proposition", ["thm:done"])]);
    expect(units).toHaveLength(1);
    expect(units[0].label).toBe("prop:aux");
  });

  it("does not stage three groups merely because they read one immutable dependency", () => {
    const roots = [
      mk("thm:a", "theorem", ["lem:shared"]),
      mk("thm:b", "theorem", ["lem:shared"]),
      mk("thm:c", "theorem", ["lem:shared"]),
    ];
    const dispatch = groupToProveByComponent(roots)
      .map((unit) => ({ ...unit, priorContext: "" }));
    const plan = planStagedSolveDispatch({
      dispatch,
      hasPendingDirective: false,
      requiredCoreTargets: new Set(),
    });
    expect(plan.upstream).toBeNull();
    expect(plan.downstream).toHaveLength(3);
    expect(plan.ordered).toEqual(dispatch);
    expect(plan.sharedTargetIds).toEqual([]);
  });

  it("does not stage an explicit target that has one local component owner", () => {
    const roots = [
      mk("thm:large", "theorem", []),
      mk("prop:required", "proposition", []),
      mk("lem:other", "lemma", []),
    ];
    const dispatch = [
      { targets: [roots[0], mk("lem:large-child", "lemma", [])], label: "thm:large", priorContext: "" },
      { targets: [roots[1]], label: "prop:required", priorContext: "" },
      { targets: [roots[2]], label: "lem:other", priorContext: "" },
    ];
    const plan = planStagedSolveDispatch({
      dispatch,
      hasPendingDirective: true,
      requiredCoreTargets: new Set(["prop:required"]),
    });
    expect(plan.upstream).toBeNull();
    expect(plan.sharedTargetIds).toEqual([]);
    expect(plan.ordered).toEqual(dispatch);
  });

  it("keeps two exact statement targets local to their two component owners", () => {
    const roots = [
      mk("thm:first", "theorem", []),
      mk("prop:second", "proposition", []),
    ];
    const dispatch = roots.map((target) => ({ targets: [target], label: target.id, priorContext: "" }));
    const plan = planStagedSolveDispatch({
      dispatch,
      hasPendingDirective: true,
      requiredCoreTargets: new Set(roots.map((target) => target.id)),
    });
    expect(plan.upstream).toBeNull();
    expect(plan.sharedTargetIds).toEqual([]);
    expect(plan.ordered).toEqual(dispatch);
  });

  it("leaves genuinely disjoint groups parallel", () => {
    const roots = [
      mk("thm:a", "theorem", ["ass:a"]),
      mk("thm:b", "theorem", ["ass:b"]),
    ];
    const dispatch = groupToProveByComponent(roots)
      .map((unit) => ({ ...unit, priorContext: "" }));
    const plan = planStagedSolveDispatch({
      dispatch,
      hasPendingDirective: false,
      requiredCoreTargets: new Set(),
    });
    expect(plan.upstream).toBeNull();
    expect(plan.downstream).toEqual(dispatch);
    expect(plan.sharedTargetIds).toEqual([]);
  });
});

describe("pruneOrphanLemmas (maximality-checkpoint dead-lemma cleanup)", () => {
  const stmt = (id: string, kind: string, depends_on: string[]) =>
    ({ id, kind, statement: id, depends_on, status: "proved" }) as any;
  const member = (node: any, isLemma: boolean) =>
    ({ proof_tex: "qed", snapshot: { stmt: node.statement, defs: {}, assumptions: {} }, ...(isLemma ? { node } : {}) }) as any;

  it("drops an agent lemma unreachable from any non-lemma claim; keeps reachable ones", () => {
    const live = stmt("lem:live", "lemma", []);
    const dead = stmt("lem:dead", "lemma", []);
    const core: any = {
      ...PROTO,
      statements: [stmt("thm:main", "theorem", ["lem:live"]), live, dead],
    };
    const working: any = {
      round: 3,
      solved: { "thm:main": member(stmt("thm:main","theorem",[]), false), "lem:live": member(live, true), "lem:dead": member(dead, true) },
    };
    const { pruned, protoOrphans } = pruneOrphanLemmas(core, working, PROTO as any);
    expect(pruned).toEqual(["lem:dead"]);
    expect(protoOrphans).toEqual([]); // lem:dead is agent-added, not in proto
    expect(core.statements.map((s: any) => s.id).sort()).toEqual(["lem:live", "thm:main"]);
    expect(Object.keys(working.solved).sort()).toEqual(["lem:live", "thm:main"]);
  });

  it("prunes transitively (a lemma reachable only through another dead lemma)", () => {
    const dead1 = stmt("lem:dead1", "lemma", ["lem:dead2"]);
    const dead2 = stmt("lem:dead2", "lemma", []);
    const core: any = { ...PROTO, statements: [stmt("thm:main", "theorem", ["ass:overlap"]), dead1, dead2] };
    const working: any = {
      round: 1,
      solved: { "thm:main": member(stmt("thm:main","theorem",[]), false), "lem:dead1": member(dead1, true), "lem:dead2": member(dead2, true) },
    };
    const { pruned } = pruneOrphanLemmas(core, working, PROTO as any);
    expect(pruned.sort()).toEqual(["lem:dead1", "lem:dead2"]);
  });

  it("keeps an unconsumed cited comparator lemma as a D0.5 literature deliverable", () => {
    const cited = {
      ...stmt("lem:current-comparator", "lemma", []),
      status: "cited",
      source: {
        cite: "Rosenbaum1983",
        locator: "Section 1",
        verbatim_statement: "Comparator statement.",
      },
    };
    const core: any = {
      ...PROTO,
      statements: [stmt("thm:main", "theorem", ["ass:overlap"]), cited],
    };
    const working: any = {
      round: 1,
      solved: { "lem:current-comparator": member(cited, true) },
    };

    const { pruned } = pruneOrphanLemmas(core, working, PROTO as any);
    expect(pruned).toEqual([]);
    expect(core.statements.map((s: any) => s.id)).toContain("lem:current-comparator");
    expect(working.solved["lem:current-comparator"]).toBeDefined();
  });

  it("flags a pruned lemma that also lives in the proto (needs a proto edit)", () => {
    const protoLemma = stmt("lem:spec", "lemma", []);
    const proto: any = { ...PROTO, statements: [...PROTO.statements, protoLemma] };
    const core: any = { ...proto, statements: [stmt("thm:main", "theorem", ["ass:overlap"]), protoLemma] };
    const working: any = { round: 1, solved: { "lem:spec": member(protoLemma, true) } };
    const { pruned, protoOrphans } = pruneOrphanLemmas(core, working, proto);
    expect(pruned).toEqual(["lem:spec"]);
    expect(protoOrphans).toEqual(["lem:spec"]);
  });

  it("no-op when every lemma is reachable", () => {
    const live = stmt("lem:live", "lemma", []);
    const core: any = { ...PROTO, statements: [stmt("thm:main", "theorem", ["lem:live"]), live] };
    const working: any = { round: 1, solved: { "lem:live": member(live, true) } };
    const { pruned } = pruneOrphanLemmas(core, working, PROTO as any);
    expect(pruned).toEqual([]);
    expect(core.statements).toHaveLength(2);
  });
});

describe("runStage0Typed proposed-change checkpoint", () => {
  // thm depends on a constructed-object def the solver must first correct.
  const LOOP_PROTO = {
    ...PROTO,
    statements: [
      { id: "thm:loop", kind: "theorem", statement: "T = O(U)", depends_on: ["def:env"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ],
  };
  // round 1 (def:env still 'U = a'): propose the correction, prove nothing.
  // round 2 (def:env now 'U = a + b'): prove the target cleanly.
  function loopDeps(): StageDeps {
    return {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        const corrected = prompt.includes("U = a + b");
        const body = corrected
          ? { proofs: targets.map((t) => ({ id: t.id, proof_tex: "By `def:env`, QED." })), added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [] }
          : { proofs: [], added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [{ id: "def:env", current: "U = a", proposed: "U = a + b", reason: "omits b", direction: "correct" }] };
        await writeFile(outPath, JSON.stringify(withCorrectionPairs(body, LOOP_PROTO)), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
  }

  it("halts on a def correction without mutating the proto", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(LOOP_PROTO), "utf8");
    const res = await runStage0Typed({ ctx, state: makeState(), deps: loopDeps() });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/no proposal was auto-applied/i);
    expect(res.advance).toBe(false);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.definitions.find((d: any) => d.id === "def:env").construction).toBe("U = a");
  });
});

describe("runStage0Typed (D0-SOLVE → D0-RENDER wiring)", () => {
  it("solves then renders the .tex and halts at the D0 maximality checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    const res = await runStage0Typed({ ctx, state: makeState(), deps: solverDeps("prove") });
    expect(res.status).toBe("checkpoint"); // clean discharge → maximality review gate before D0.5
    expect(res.message).toMatch(/MAXIMALITY CHECKPOINT/);
    expect(res.advance).not.toBe(false); // stage_completed advances to "0"; --resume → D0.5
    expect((res.artifacts ?? []).some((a) => a.endsWith(".tex"))).toBe(true);
    const tex = await readFile((res.artifacts ?? []).find((a) => a.endsWith(".tex"))!, "utf8");
    expect(tex).toContain("\\begin{document}");
  });

  it("passes a proposed-statement-change checkpoint straight through (no render)", async () => {
    const ctx = makeCtx(repoRoot);
    const res = await runStage0Typed({ ctx, state: makeState(), deps: solverDeps("propose") });
    expect(res.status).toBe("checkpoint");
    expect(res.advance).toBe(false);
  });

  it("checkpoints a structured core edit without mutating the proto", async () => {
    const ctx = makeCtx(repoRoot);
    const before = await readFile(protoCoreJsonPath(ctx), "utf8");
    const res = await runStage0Typed({ ctx, state: makeState(), deps: solverDeps("core-edit") });
    expect(res.status).toBe("checkpoint");
    expect(res.advance).toBe(false);
    expect(res.message).toMatch(/no proposal was auto-applied/i);
    expect(await readFile(protoCoreJsonPath(ctx), "utf8")).toBe(before);
    expect(((await readSurfacedProposals(ctx)).coreEdits ?? []).length).toBeGreaterThan(0);
  });
});

describe("add-prove-approve-later: assumptions, theorem narrowings, OEQ residuals, dangling-drop", () => {
  function depsReturning(makeBody: (targets: Array<{ id: string }>, prompt: string) => Record<string, unknown>): StageDeps {
    return {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify(withCorrectionPairs(makeBody(targets, prompt))), "utf8");
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
  }

  it("SURFACES a proposed new assumption as a checkpoint (NOT silently applied to the core)", async () => {
    const ctx = makeCtx(repoRoot);
    const deps = depsReturning((targets) => ({
      proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
      added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
      proposed_assumptions: [{ id: "ass:bounded-score", condition: "the clipped score envelope is O(1/q)", reason: "variance step", standard_or_novel: "standard: DML", not_crux: "estimator-side truncation" }],
    }));
    const res = (await runStage0Solve({ ctx, state: makeState(), deps })) as any;
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/NEW ASSUMPTION/i);
    expect((await readSurfacedProposals(ctx)).assumptions.length).toBeGreaterThan(0);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.assumptions.some((a: any) => a.id === "ass:bounded-score")).toBe(false); // not applied to core
  });

  it("applyProposedChanges adds a proposed assumption node to the PROTO with a parsed tag", async () => {
    const ctx = makeCtx(repoRoot);
    await seedWorkingProposals(ctx, { assumptions: [{ id: "ass:newone", condition: "X holds", standard_or_novel: "standard: overlap, Rosenbaum1983", reason: "needed" }] });
    await applyProposedChanges({ ctx, ids: new Set(["ass:newone"]), note: "test" });
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    const a = proto.assumptions.find((x: any) => x.id === "ass:newone");
    expect(a).toBeTruthy();
    expect(a.condition).toBe("X holds");
    expect(a.standard?.cite).toBe("Rosenbaum1983"); // bib key recognized from the tag
  });

  it("halts on a theorem narrowing and leaves the proto unchanged", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({ ...PROTO, statements: [
      { id: "thm:t", kind: "theorem", statement: "strong claim", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ] }), "utf8");
    const deps = depsReturning((targets, prompt) =>
      prompt.includes("narrowed honest claim")
        ? { proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })), added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [] }
        : { proofs: [], added_lemmas: [], proposed_definition_changes: [], proposed_statement_changes: [{ id: "thm:t", current: "strong claim", proposed: "narrowed honest claim", reason: "too strong as stated", direction: "narrow" }] },
    );
    const res = await runStage0Typed({ ctx, state: makeState(), deps });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/no proposal was auto-applied/i);
    const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(proto.statements.find((s: any) => s.id === "thm:t").statement).toBe("strong claim");
  });

  it("treats an open obligation on an OEQ node as a RESIDUAL (clean discharge, not a halt)", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({ ...PROTO, statements: [
      { id: "thm:main", kind: "theorem", statement: "main", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      { id: "oeq:tight", kind: "openendedquestion", statement: "is it tight?", depends_on: ["thm:main"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ] }), "utf8");
    let leaveOpen = true;
    const deps = depsReturning((targets) => ({
      proofs: targets.filter((t) => t.id !== "oeq:tight").map((t) => ({ id: t.id, proof_tex: "QED." })),
      added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
      open_obligations: leaveOpen && targets.some((t) => t.id === "oeq:tight") ? [{ node_id: "oeq:tight", what_is_open: "tightness", obstruction: "open", attempted: "x" }] : [],
    }));
    const state = makeState();
    const res = (await runStage0Solve({ ctx, state, deps })) as any;
    expect("status" in res).toBe(false); // Stage0SolveResult = clean discharge (OEQ residual did NOT halt)
    expect(state.design_decisions.d0_open_oeq_residuals).toMatch(/oeq:tight/);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:main").status).toBe("proved");
    expect(core.statements.find((s: any) => s.id === "oeq:tight").status).toBe("to-prove"); // legitimately left open

    leaveOpen = false;
    await runStage0Solve({ ctx, state, deps });
    expect(state.design_decisions.d0_open_oeq_residuals).toBeUndefined();
  });

  it("seals a residual OEQ against its authored source rather than proof-wired dependencies", async () => {
    const ctx = makeCtx(repoRoot);
    const question = {
      id: "oeq:tight", kind: "openendedquestion", statement: "is it tight?",
      depends_on: ["thm:main"], status: "to-prove", justification: "j", gap: "g", consumer: "c",
    } as any;
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({ ...PROTO, statements: [
      { id: "thm:main", kind: "theorem", statement: "main", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      { id: "prop:extra", kind: "proposition", statement: "extra", depends_on: [], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
      question,
    ] }), "utf8");
    await saveWorkingState(ctx, {
      round: 1,
      solved: {
        [question.id]: {
          proof_tex: "Partial progress also uses Proposition~\\ref{prop:extra}.",
          snapshot: { stmt: question.statement, depends_on: ["thm:main", "prop:extra"], defs: {}, assumptions: {} },
          node: question,
          partial: true,
        },
      },
    });
    const calls: string[][] = [];
    const deps = depsReturning((targets) => {
      calls.push(targets.map((target) => target.id));
      const hasQuestion = targets.some((target) => target.id === question.id);
      return {
        proofs: targets.filter((target) => target.id !== question.id)
          .map((target) => ({ id: target.id, proof_tex: "QED." })),
        added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
        open_obligations: hasQuestion ? [{
          node_id: question.id,
          what_is_open: "tightness",
          obstruction: "the extra proposition does not close the converse",
          attempted: "combined the known upper and lower arguments",
        }] : [],
      };
    });
    const state = makeState();
    await runStage0Solve({ ctx, state, deps });
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[question.id].snapshot.depends_on).toContain("prop:extra");
    expect(working.sealed_open_oeqs[question.id]).toBe(oeqSourceFingerprint(question));

    await appendEscalationLog(ctx, {
      round: 3,
      changed: [],
      directive: "revalidate only the separate theorem root",
    });
    calls.length = 0;
    await runStage0Solve({ ctx, state, deps });
    expect(calls.flat()).not.toContain(question.id);
  });

  it("fails cheaply instead of erasing a dangling depends_on edge", async () => {
    const ctx = makeCtx(repoRoot);
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({ ...PROTO, statements: [
      { id: "thm:d", kind: "theorem", statement: "d", depends_on: ["ass:overlap"], status: "to-prove", justification: "j", gap: "g", consumer: "c" },
    ] }), "utf8");
    const deps = depsReturning(() => ({
      proofs: [{ id: "thm:d", proof_tex: "QED." }],
      added_lemmas: [{ id: "lem:x", kind: "lemma", statement: "x", depends_on: ["ass:phantom"], status: "proved", proof_tex: "trivial." }],
      proposed_statement_changes: [], proposed_definition_changes: [],
    }));
    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /unresolved dependency target.*lem:x->ass:phantom.*refusing to erase/i,
    );
    expect(existsSync(coreJsonPath(ctx))).toBe(false);
  });
});

describe("D0 merge — quarantine scope and structured-directive fulfillment", () => {
  /** Two-unit dispatch (thm:main owner ranks as directive owner; prop:aux is the sibling). */
  function twoUnitDeps(
    emit: (targets: Array<{ id: string }>) => Record<string, unknown>,
  ): StageDeps {
    return {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify(emit(targets)), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
  }

  it("an incompatible sibling version of an existing node withholds that node, not an unrelated unit's consumer", async () => {
    const ctx = makeCtx(repoRoot);
    const proto: any = structuredClone(PROTO);
    proto.statements.find((statement: any) => statement.id === "prop:aux").consumer = "independent downstream use";
    // A third, independent unit whose node the sibling will contest.
    proto.statements.push({
      id: "lem:side", kind: "lemma", statement: "a side fact", depends_on: [], status: "to-prove",
      justification: "side", gap: "vs prior", consumer: "thm:main",
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(proto), "utf8");
    await appendEscalationLog(ctx, {
      round: 1, changed: [], directive: "settle every exact target",
      required_core_targets: ["thm:main", "prop:aux", "lem:side"],
    });
    const deps = twoUnitDeps((targets) => {
      const ownsAux = targets.some(({ id }) => id === "prop:aux");
      return {
        proofs: targets.map(({ id }) => ({
          id, proof_tex: id === "thm:main" ? "Combine ass:overlap with lem:side." : `Owner proof for ${id}.`,
        })),
        // The sibling emits an INCOMPATIBLE settled version of the existing lem:side.
        // Its canonical (unproved) version survives; only lem:side itself is in dispute.
        added_lemmas: ownsAux ? [{
          ...proto.statements[2], statement: "INCOMPATIBLE SIDE CLAIM", status: "proved",
          proof_tex: "Sibling incompatible side proof.",
        }] : [],
      };
    });

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((statement: any) => statement.id === "lem:side")).toMatchObject({
      statement: "a side fact", status: "to-prove",
    });
    expect(core.statements.find((statement: any) => statement.id === "prop:aux")?.status).toBe("proved");
    // The unrelated unit's proof merely cites the canonical lem:side; it is not a
    // consumer of the withheld variant and must land.
    expect(core.statements.find((statement: any) => statement.id === "thm:main")?.status).toBe("proved");
    const withheld = JSON.parse(await readFile(
      path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json"), "utf8",
    ));
    expect(withheld.withheld_payloads).toEqual(expect.arrayContaining([
      expect.objectContaining({ target: "lem:side", payload: expect.objectContaining({ statement: "INCOMPATIBLE SIDE CLAIM" }) }),
    ]));
    expect(withheld.withheld_payloads).not.toEqual(expect.arrayContaining([
      expect.objectContaining({ target: "thm:main", reason: "conflicted-dependency-consumer" }),
    ]));
  });

  it("keeps a target-less structured directive pending when only noise was withheld", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1, changed: [],
      directive: "replace the stale formal assumption node",
      require_core_changes: true,
    });
    const deps = twoUnitDeps((targets) => ({
      proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof for ${id}.` })),
      // No structural change anywhere; a stray paper-wide prose write from every unit
      // is the only withheld content.
      prose_updates: { tldr: "stray narrative" },
    }));

    // The stray prose is a capability quarantine, so the round checkpoints instead
    // of aborting; the directive must remain pending (cursor not advanced).
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });
  it("a prose-only statement note on a non-target cannot satisfy a structured directive", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1, changed: [],
      directive: "replace the stale formal assumption node",
      require_core_changes: true,
    });
    const deps = twoUnitDeps((targets) => ({
      proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof for ${id}.` })),
      // Substantive note metadata, but no structural change and no exact target.
      prose_updates: { statement_notes: [{ id: targets[0].id, consumer: "freshly edited consumer text" }] },
    }));
    let outcome: unknown;
    try { outcome = await runStage0Solve({ ctx, state: makeState(), deps }); } catch (err) { outcome = err; }
    const blocked = outcome instanceof Error
      ? /STRUCTURED CORE CHANGES REQUIRED/.test(outcome.message)
      : (outcome as { advance?: boolean }).advance === false;
    expect(blocked, `round must not advance past the directive: ${JSON.stringify(outcome)}`).toBe(true);
    expect(JSON.parse(await readFile(workingPath(ctx), "utf8")).escalation_entries_consumed ?? 0).toBe(0);
  });
});
