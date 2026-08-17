import { describe, expect, it } from "vitest";
import { CoreSchema, coreNodeIds, type Core } from "../../src/discovery/core/schema.js";
import {
  saveWorkingState,
  snapshotMember,
  symbolBasis,
  type WorkingState,
} from "../../src/discovery/stages/d0_working.js";
import {
  prepareD0BaselineRebase,
  prepareD0ExtensionRebase,
} from "../../src/discovery/stages/d0_rebase_baseline.js";
import {
  consumePendingIncrementalRewind,
  legacyCrossBoundaryRewindGuard,
} from "../../src/discovery/stages/d0_cross_boundary_rewind.js";
import { applyInterventionRoute } from "../../src/shared/intervention_routing.js";
import type { Intervention } from "../../src/judgment.js";
import { createDStageHarness } from "./d_stage_harness.js";

const PROOF = "The accepted proof bytes are preserved exactly.";

function core(id: string, proved: boolean): Core {
  return CoreSchema.parse({
    qid: "stat_rebase_fixture",
    specialization: "v1",
    cluster: "stat",
    symbols: [],
    assumptions: [],
    definitions: [{ id: `def:${id}`, name: id, construction: `${id} construction`, inputs: [] }],
    statements: [{
      id: `thm:${id}`,
      kind: "theorem",
      statement: `${id} claim`,
      depends_on: [`def:${id}`],
      status: proved ? "proved" : "to-prove",
      ...(proved ? { proof_tex: PROOF } : {}),
    }],
    target_estimand: id,
    bibliography: [],
  });
}

function cursor(c: Core, revision: string, round: number, proved: boolean): WorkingState {
  const statement = c.statements[0];
  return {
    round,
    proposal_revision: revision,
    symbol_basis: symbolBasis(c),
    solved: proved ? { [statement.id]: { proof_tex: PROOF, snapshot: snapshotMember(c, statement) } } : {},
    proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    required_core_edit_mandates: [],
    escalation_entries_consumed: 12,
    store_format: 2,
  };
}

function prepare(overrides: Partial<{
  sourceWorking: WorkingState;
  currentWorking: WorkingState;
  currentPendingEscalations: Array<{ round: number; changed: []; note?: string; directive?: string }>;
  sourceIds: string[];
  currentIds: string[];
}> = {}) {
  const sourceCore = core("kept", true);
  const currentProto = core("stale", false);
  const sourceWorking = overrides.sourceWorking ?? cursor(sourceCore, "angle:0/version:7", 39, true);
  const currentWorking = overrides.currentWorking ?? cursor(currentProto, "angle:0/version:8", 40, false);
  return prepareD0BaselineRebase({
    sourceCore,
    sourceProto: sourceCore,
    sourceWorking,
    currentProto,
    currentWorking,
    currentPendingEscalations: overrides.currentPendingEscalations,
    expectations: {
      sourceRevision: "angle:0/version:7",
      sourceRound: 39,
      sourceIds: overrides.sourceIds ?? [...coreNodeIds(sourceCore)],
      sourceProtoIds: [...coreNodeIds(sourceCore)],
      currentRevision: "angle:0/version:8",
      currentRound: 40,
      currentEscalationEntries: 12,
      currentIds: overrides.currentIds ?? [...coreNodeIds(currentProto)],
      discardCurrentIds: [...coreNodeIds(currentProto)],
      discardCurrentSolvedIds: [],
      qid: "stat_rebase_fixture",
      specialization: "v1",
    },
  });
}

describe("prepareD0BaselineRebase", () => {
  it("freezes the accepted claims and carries the proof bytes onto the current revision", () => {
    const plan = prepare();
    expect(plan.proto.statements).toEqual([
      expect.objectContaining({ id: "thm:kept", status: "to-prove" }),
    ]);
    expect(plan.proto.statements[0]).not.toHaveProperty("proof_tex");
    expect(plan.working).toMatchObject({ round: 40, proposal_revision: "angle:0/version:8" });
    expect(plan.working.solved["thm:kept"]).toMatchObject({ proof_tex: PROOF });
    expect(plan.working.solved["thm:kept"]).not.toHaveProperty("node");
    expect(plan.renderedCore.statements[0]).toMatchObject({ status: "proved", proof_tex: PROOF });
  });

  it("fails closed on an unadjudicated current proposal bundle", () => {
    const currentProto = core("stale", false);
    const dirty = cursor(currentProto, "angle:0/version:8", 40, false);
    dirty.proposals!.coreEdits.push({ kind: "statement-delete", id: "thm:stale" });
    expect(() => prepare({ currentWorking: dirty })).toThrow(/unadjudicated proposal/);
  });

  it("fails closed on a stale revision or round", () => {
    const sourceCore = core("kept", true);
    const stale = cursor(sourceCore, "angle:0/version:6", 38, true);
    expect(() => prepare({ sourceWorking: stale })).toThrow(/source cursor mismatch/);

    const currentProto = core("stale", false);
    const pendingJournal = cursor(currentProto, "angle:0/version:8", 40, false);
    pendingJournal.escalation_entries_consumed = 11;
    expect(() => prepare({ currentWorking: pendingJournal })).toThrow(/escalation cursor mismatch/);
    expect(() => prepare({
      currentWorking: pendingJournal,
      currentPendingEscalations: [{ round: 40, changed: [], note: "discard receipt" }],
    })).not.toThrow();
    expect(() => prepare({
      currentWorking: pendingJournal,
      currentPendingEscalations: [{ round: 40, changed: [], directive: "still actionable" }],
    })).toThrow(/pending actionable escalation/);
  });

  it("requires exact source and current node-id sets", () => {
    expect(() => prepare({ sourceIds: ["thm:kept"] })).toThrow(/source core: id set mismatch/);
    expect(() => prepare({ currentIds: ["def:stale", "thm:not-stale"] })).toThrow(/current proto: id set mismatch/);
  });
});

describe("prepareD0ExtensionRebase", () => {
  it("carries a matching D0-added node but rejects an old embedded claim with a matching old snapshot", () => {
    const accepted = core("d0-added-record", true);
    const extension = CoreSchema.parse({
      ...structuredClone(accepted),
      statements: accepted.statements.map((statement) => ({
        ...statement,
        status: "to-prove",
        proof_tex: undefined,
        route: undefined,
      })),
    });
    const matchingWorking = cursor(accepted, "angle:0/version:7", 39, true);
    matchingWorking.solved["thm:d0-added-record"].node = structuredClone(accepted.statements[0]);

    const plan = prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking: matchingWorking,
      extensionProto: extension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    });
    expect(plan.renderedCore.statements[0]).toEqual(accepted.statements[0]);
    expect(plan.working.solved["thm:d0-added-record"]).not.toHaveProperty("node");

    // Exact auditor reproducer: the accepted core has the new claim, but the
    // D0-added working record still embeds and snapshots an older claim while
    // reusing the same proof bytes. Snapshot-only validation used to accept it.
    const staleWorking = structuredClone(matchingWorking);
    staleWorking.solved["thm:d0-added-record"].node!.statement = "the older, narrower claim";
    staleWorking.solved["thm:d0-added-record"].snapshot = snapshotMember(
      accepted,
      staleWorking.solved["thm:d0-added-record"].node!,
    );
    expect(() => prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking: staleWorking,
      extensionProto: extension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/accepted carried node thm:d0-added-record has stale claim metadata/);
  });

  it("round-trips a banked-style open OEQ without laundering or carrying a proof", () => {
    const accepted = core("proved-anchor", true);
    accepted.statements.push({
      id: "oeq:open-frontier",
      kind: "openendedquestion",
      statement: "Can the remaining logarithmic frontier be characterized?",
      depends_on: ["thm:proved-anchor"],
      route: "Investigate the unresolved endpoint without presenting it as established.",
      status: "to-prove",
    });
    const sealed = CoreSchema.parse(accepted);
    const extension = CoreSchema.parse({
      ...structuredClone(sealed),
      statements: sealed.statements.map((statement) => ({
        ...statement,
        status: "to-prove",
        proof_tex: undefined,
        route: undefined,
        source: undefined,
      })),
    });
    const sourceWorking = cursor(sealed, "angle:0/version:7", 39, true);
    const plan = prepareD0ExtensionRebase({
      sourceCore: sealed,
      sourceWorking,
      extensionProto: extension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    });

    expect(plan.proto.statements.find((s) => s.id === "oeq:open-frontier")).toEqual(
      sealed.statements[1],
    );
    expect(plan.renderedCore.statements.find((s) => s.id === "oeq:open-frontier")).toEqual(
      sealed.statements[1],
    );
    expect(plan.working.solved["oeq:open-frontier"]).toBeUndefined();
    expect(plan.renderedCore.statements.find((s) => s.id === "thm:proved-anchor")?.status).toBe("proved");

    const launderedStatus = structuredClone(extension);
    launderedStatus.statements[1].status = "proved";
    launderedStatus.statements[1].proof_tex = "A fabricated proof.";
    expect(() => prepareD0ExtensionRebase({
      sourceCore: sealed,
      sourceWorking,
      extensionProto: launderedStatus,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/accepted statement oeq:open-frontier must use the GP2 to-prove proposal form/);

    const inconsistentWorking = structuredClone(sourceWorking);
    inconsistentWorking.solved["oeq:open-frontier"] = {
      proof_tex: "A stale proof that must not convert the open OEQ.",
      snapshot: snapshotMember(sealed, sealed.statements[1]),
    };
    expect(() => prepareD0ExtensionRebase({
      sourceCore: sealed,
      sourceWorking: inconsistentWorking,
      extensionProto: extension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/accepted open statement oeq:open-frontier has inconsistent proof\/citation state/);
  });

  it("round-trips a banked-style proved route while keeping additive statements open", () => {
    const accepted = core("routed", true);
    accepted.statements[0].route =
      "Reduce the boundary supremum to separated half-disc alternatives and apply Assouad.";
    const sealed = CoreSchema.parse(accepted);
    const extension = CoreSchema.parse({
      ...structuredClone(sealed),
      definitions: [
        ...sealed.definitions,
        { id: "def:new-route-free", name: "new-route-free", construction: "new construction", inputs: [] },
      ],
      statements: [
        { ...sealed.statements[0], status: "to-prove", proof_tex: undefined, route: undefined },
        {
          id: "thm:new-route-free",
          kind: "theorem",
          statement: "new additive claim",
          depends_on: ["def:new-route-free"],
          status: "to-prove",
        },
      ],
    });
    const plan = prepareD0ExtensionRebase({
      sourceCore: sealed,
      sourceWorking: cursor(sealed, "angle:0/version:7", 39, true),
      extensionProto: extension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    });

    expect(plan.proto.statements.find((s) => s.id === "thm:routed")).toMatchObject({
      status: "to-prove",
      route: sealed.statements[0].route,
    });
    expect(plan.renderedCore.statements.find((s) => s.id === "thm:routed")).toEqual(
      sealed.statements[0],
    );
    expect(plan.proto.statements.find((s) => s.id === "thm:new-route-free")).toEqual(
      expect.objectContaining({ status: "to-prove" }),
    );
    expect(plan.proto.statements.find((s) => s.id === "thm:new-route-free")).not.toHaveProperty("route");
    expect(plan.renderedCore.statements.find((s) => s.id === "thm:new-route-free")).toEqual(
      expect.objectContaining({ status: "to-prove" }),
    );

    const mutated = structuredClone(extension);
    mutated.statements[0].statement = "changed mathematical claim hidden behind the accepted route";
    expect(() => prepareD0ExtensionRebase({
      sourceCore: sealed,
      sourceWorking: cursor(sealed, "angle:0/version:7", 39, true),
      extensionProto: mutated,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/accepted statement thm:routed was changed/);

    const injected = structuredClone(extension);
    injected.statements[1].route = "pretend this extension theorem is already planned";
    expect(() => prepareD0ExtensionRebase({
      sourceCore: sealed,
      sourceWorking: cursor(sealed, "angle:0/version:7", 39, true),
      extensionProto: injected,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/new statement thm:new-route-free must remain in the open GP2 proposal form/);
  });

  it("preserves an accepted D0-added node and leaves only additive proposal nodes open", () => {
    const accepted = core("d0-added", true);
    const extension = CoreSchema.parse({
      ...structuredClone(accepted),
      definitions: [
        ...accepted.definitions,
        { id: "def:new", name: "new", construction: "new construction", inputs: [] },
      ],
      statements: [
        { ...accepted.statements[0], status: "to-prove", proof_tex: undefined },
        {
          id: "thm:new",
          kind: "theorem",
          statement: "new additive claim",
          depends_on: ["def:new"],
          status: "to-prove",
        },
      ],
    });
    const plan = prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking: cursor(accepted, "angle:0/version:7", 39, true),
      extensionProto: extension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    });

    expect(plan.preservedIds).toContain("thm:d0-added");
    expect(plan.addedIds).toEqual(["def:new", "thm:new"]);
    expect(plan.renderedCore.statements.find((s) => s.id === "thm:d0-added")).toMatchObject({
      status: "proved",
      proof_tex: PROOF,
    });
    expect(plan.renderedCore.statements.find((s) => s.id === "thm:new")).toMatchObject({
      status: "to-prove",
    });
    expect(plan.working.proposal_revision).toBe("angle:0/version:8");
  });

  it("fails closed if an extension silently omits or changes an accepted node", () => {
    const accepted = core("d0-added", true);
    const sourceWorking = cursor(accepted, "angle:0/version:7", 39, true);
    const omitted = core("different", false);
    expect(() => prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking,
      extensionProto: omitted,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/accepted definition def:d0-added was omitted/);

    const changed = structuredClone(accepted);
    changed.statements[0].status = "to-prove";
    delete changed.statements[0].proof_tex;
    changed.statements[0].statement = "silently changed claim";
    expect(() => prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking,
      extensionProto: changed,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/accepted statement thm:d0-added was changed/);

    const laundered = structuredClone(accepted);
    laundered.bibliography = [{ key: "FakeSource" }];
    laundered.statements[0] = {
      ...laundered.statements[0],
      status: "cited",
      proof_tex: undefined,
      source: { cite: "FakeSource", locator: "Theorem 1" },
    };
    expect(() => prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking,
      extensionProto: CoreSchema.parse(laundered),
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/must use the GP2 to-prove proposal form/);

    const staleBasis = structuredClone(sourceWorking);
    staleBasis.symbol_basis = { ghost: "stale-hash" };
    const validExtension = structuredClone(accepted);
    validExtension.statements[0].status = "to-prove";
    delete validExtension.statements[0].proof_tex;
    expect(() => prepareD0ExtensionRebase({
      sourceCore: accepted,
      sourceWorking: staleBasis,
      extensionProto: validExtension,
      sourceRevision: "angle:0/version:7",
      extensionRevision: "angle:0/version:8",
      escalationEntries: 12,
    })).toThrow(/source symbol basis is stale/);
  });

  it("preserves an accepted cited leaf and restores its sealed attestation after GP2 normalization", () => {
    const accepted = core("cited-input", false);
    accepted.bibliography = [{ key: "Source2026" }];
    accepted.statements[0] = {
      ...accepted.statements[0],
      status: "cited",
      source: {
        cite: "Source2026",
        locator: "Theorem 4",
        verbatim_statement: "The cited bound holds uniformly.",
        attestation: { by: "main", note: "transcribed from the source of record" },
      },
    };
    const parsedAccepted = CoreSchema.parse(accepted);
    const extension = structuredClone(parsedAccepted);
    extension.statements[0] = {
      ...extension.statements[0],
      status: "to-prove",
      source: undefined,
    };
    const plan = prepareD0ExtensionRebase({
      sourceCore: parsedAccepted,
      sourceWorking: cursor(parsedAccepted, "angle:0/version:3", 8, false),
      extensionProto: CoreSchema.parse(extension),
      sourceRevision: "angle:0/version:3",
      extensionRevision: "angle:0/version:4",
      escalationEntries: 2,
    });
    const restored = plan.proto.statements[0];
    expect(restored.status).toBe("cited");
    expect(restored.source).toEqual(parsedAccepted.statements[0].source);
    expect(plan.renderedCore.statements[0].source?.attestation?.by).toBe("main");
  });
});

describe("typed cross-boundary rewind provenance", () => {
  it("consumes an incremental receipt without falsely blocking a later legitimate angle pivot", async () => {
    const accepted = core("kept", true);
    const harness = await createDStageHarness({
      qid: "stat_rebase_fixture",
      specialization: "v1",
      proto: accepted,
    });
    try {
      const state = harness.state();
      state.stage_completed = "4";
      state.proposed_from = {
        topic: "fixture",
        novelty_target: "field",
        pivot_budget_used: 0,
        final_verdict: "ACCEPT",
        proposal_path: "fixture-proto.json",
        novelty_justification: "fixture",
        chosen_qid: "stat_rebase_fixture",
        chosen_specialization: "v1",
        cluster: "stat",
        current_angle_index: 0,
        current_version: 7,
        current_mode: "revise",
        exhausted_angles: [],
      };
      await saveWorkingState(harness.ctx(), cursor(accepted, "angle:0/version:7", 39, true));

      expect(applyInterventionRoute(state, {
        route: "stage_0",
        reason: "repair the accepted argument",
        proposed_action: "repair in place",
        action_kind: "re_derive",
        d0_rewind_intent: "incremental_repair",
      } as Intervention)).toBe(true);
      expect(state.flags.d0_cross_boundary_rewind?.intent).toBe("incremental_repair");
      expect(state.flags.rewound_from_stage0).toBe("repair the accepted argument");

      await consumePendingIncrementalRewind({ ctx: harness.ctx(), state });
      expect(state.flags.d0_cross_boundary_rewind).toBeUndefined();
      expect(state.flags.rewound_from_stage0).toBeNull();

      expect(applyInterventionRoute(state, {
        route: "stage_neg1",
        reason: "the repaired angle is genuinely exhausted",
        action_kind: "redraft_proposal",
      } as Intervention)).toBe(true);
      expect(state.stage_completed).toBe("-1.2");
      expect(state.flags.d0_cross_boundary_rewind).toBeUndefined();
      expect(state.flags.rewound_from_stage0).toBeNull();
      expect(legacyCrossBoundaryRewindGuard(state)).toBeNull();
    } finally {
      await harness.dispose();
    }
  });
});
