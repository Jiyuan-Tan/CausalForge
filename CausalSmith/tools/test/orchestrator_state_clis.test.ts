import { mkdir, mkdtemp, writeFile, readFile, access } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { beforeEach, describe, expect, it } from "vitest";
import { createInitialState, loadState, saveState } from "../src/state.js";
import {
  appendEscalationLog,
  escalationLogPath,
  loadWorkingState,
  readEscalationLog,
  saveWorkingState,
} from "../src/discovery/stages/d0_working.js";
import type { PipelineContext } from "../src/types.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import { makeRequiredCoreEditMandate } from "../src/discovery/solve/mandates.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { coreRevision, statementRevision } from "../src/discovery/core/revision.js";
import { assembleCore } from "../src/discovery/core/assemble.js";
import { wiredSnapshot } from "../src/discovery/working_writer.js";
import type { CoreStatement } from "../src/discovery/core/schema.js";

const exec = promisify(execFile);
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");
const BIN = (name: string): string => path.resolve(__TOOLS_ROOT, "bin", name);

const QID = "panel_minimal_basis";
const SPEC = "p1_bernoulli";

let repoRoot: string;

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "orch-clis-"));
  // CausalSmith package marker so each bin's findRepoRoot resolves to repoRoot.
  await writeFile(path.join(repoRoot, "lakefile.toml"), `name = "CausalSmith"\n`);
  await saveState(repoRoot, QID, SPEC, createInitialState(QID));
});

function run(bin: string, args: string[]): Promise<{ stdout: string; stderr: string }> {
  return exec(TSX_CLI, [BIN(bin), QID, SPEC, ...args], { cwd: repoRoot, env: { ...process.env } });
}

describe("add_assumption.ts", () => {
  it("appends a schema-valid assumption + a design decision (no hand-edit)", async () => {
    await run("add_assumption.ts", [
      "--label",
      "reg_measurable",
      "--statement",
      "the estimator is measurable in n",
      "--classification",
      "regularity-bookkeeping",
      "--decision",
      "why=discharged from the construction's large-n regime",
    ]);
    const state = await loadState(repoRoot, QID, SPEC);
    expect(state.added_assumptions).toHaveLength(1);
    expect(state.added_assumptions[0]).toMatchObject({
      label: "reg_measurable",
      statement: "the estimator is measurable in n",
      classification: "regularity-bookkeeping",
    });
    expect(state.design_decisions.why).toMatch(/large-n regime/);
  });

  it("replaces an entry with the same label rather than duplicating", async () => {
    await run("add_assumption.ts", ["--label", "a1", "--statement", "first"]);
    await run("add_assumption.ts", ["--label", "a1", "--statement", "second"]);
    const state = await loadState(repoRoot, QID, SPEC);
    expect(state.added_assumptions).toHaveLength(1);
    expect(state.added_assumptions[0].statement).toBe("second");
  });

  it("rejects a bad classification", async () => {
    await expect(
      run("add_assumption.ts", ["--label", "x", "--statement", "y", "--classification", "nonsense"]),
    ).rejects.toThrow();
  });

  // ONE WRITER PER CONCEPT: a substrate-gate needs plan+graph registration, which only gate.ts does.
  // Letting this CLI record the disclosure alone is what stranded `EnvelopeLineC2Data` as a gate
  // that no store knew was a gate (banked `accepted` with undischarged proof-step debt).
  it("REFUSES --classification substrate-gate and routes the caller to gate.ts", async () => {
    await expect(
      run("add_assumption.ts", [
        "--label", "thm:x:SomeGate", "--statement", "y", "--classification", "substrate-gate",
      ]),
    ).rejects.toThrow();
    const state = await loadState(repoRoot, QID, SPEC);
    expect(state.added_assumptions ?? []).toHaveLength(0); // nothing written
  });
});

describe("d0_directive.ts", () => {
  it("refuses before appending when the qid pipeline lock is held", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await withRunHeartbeat(repoRoot, QID, SPEC, async () => {
      await expect(run("d0_directive.ts", [
        "--directive", "must not race an active pipeline",
      ])).rejects.toThrow();
    });
    expect(await readEscalationLog(ctx)).toEqual([]);
  });

  it("appends a standalone directive to the D0 escalation log (no hand-append)", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });

    await run("d0_directive.ts", ["--directive", "use the plug-in estimator with a Nadaraya-Watson smoother"]);

    const entries = await readEscalationLog(ctx);
    expect(entries).toHaveLength(1);
    expect(entries[0].changed).toEqual([]);
    expect(entries[0].directive).toMatch(/Nadaraya-Watson/);
  });

  it("persists schema-validated exact core edits and makes them structured-change requirements", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    const proto = JSON.parse(
      await readFile(path.resolve(__TOOLS_ROOT, "test/fixtures/stat_ate_overlap_decay_proto_core.json"), "utf8"),
    );
    proto.assumptions[0].condition = String.raw`\(Y=A Y^1+(1-A)Y^0\)`;
    await writeFile(protoPath, JSON.stringify(proto), "utf8");
    const state = await loadState(repoRoot, QID, SPEC);
    state.proposed_from = {
      topic: "test",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "ACCEPT",
      proposal_path: protoPath,
      novelty_justification: "test fixture",
      chosen_qid: QID,
      chosen_specialization: SPEC,
      current_angle_index: 0,
      current_version: 1,
    };
    await saveState(repoRoot, QID, SPEC, state);

    await run("d0_directive.ts", [
      "--directive", "carry the independently adjudicated deletion into the next atomic bundle",
      "--require-core-edit", JSON.stringify({
        kind: "assumption-replace",
        id: "ass:consistency",
        proposed: {
          ...proto.assumptions[0],
          condition: String.raw`\(Y=A Y^1+(1-A)Y^0\ \text{a.s.}\)`,
        },
        reason: "reviewer confirmed the exact serialization repair",
        direction: "correct",
      }),
    ]);

    const entry = (await readEscalationLog(ctx))[0];
    expect(entry.require_core_changes).toBe(true);
    expect(entry.required_core_edits).toBeUndefined();
    expect(entry.required_core_edit_mandates).toEqual([expect.objectContaining({
      mandate_id: expect.stringMatching(/^d0m:[a-f0-9]{64}$/),
      hash_version: 3,
      sealed: expect.any(String),
      edit: expect.objectContaining({ kind: "assumption-replace", id: "ass:consistency" }),
    })]);
  });

  it("rejects malformed exact core edits before writing the directive journal", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });
    await expect(run("d0_directive.ts", [
      "--directive", "bad edit",
      "--require-core-edit", JSON.stringify({ kind: "statement-delete", id: "not-an-id" }),
    ])).rejects.toThrow();
    expect(await readEscalationLog(ctx)).toHaveLength(0);
  });

  it("refuses an exact core edit without a versioned accepted proposal basis", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    await writeFile(
      protoPath,
      await readFile(path.resolve(__TOOLS_ROOT, "test/fixtures/stat_ate_overlap_decay_proto_core.json"), "utf8"),
    );
    await expect(run("d0_directive.ts", [
      "--directive", "delete obsolete route",
      "--require-core-edit", JSON.stringify({
        kind: "statement-delete",
        id: "lem:obsolete-route",
        reason: "obsolete",
        direction: "delete-obsolete",
      }),
    ])).rejects.toThrow();
    expect(await readEscalationLog(ctx)).toHaveLength(0);
  });

  it("refuses an exact core edit when the working cursor belongs to another proposal revision", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    await writeFile(
      protoPath,
      await readFile(path.resolve(__TOOLS_ROOT, "test/fixtures/stat_ate_overlap_decay_proto_core.json"), "utf8"),
    );
    const state = await loadState(repoRoot, QID, SPEC);
    state.proposed_from = {
      topic: "test", novelty_target: "field", pivot_budget_used: 0, final_verdict: "ACCEPT",
      proposal_path: protoPath, novelty_justification: "fixture", chosen_qid: QID,
      chosen_specialization: SPEC, current_angle_index: 0, current_version: 2,
    };
    await saveState(repoRoot, QID, SPEC, state);
    await saveWorkingState(ctx, {
      round: 1, proposal_revision: "angle:0/version:1", solved: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    });
    await expect(run("d0_directive.ts", [
      "--directive", "delete stale target",
      "--require-core-edit", JSON.stringify({
        kind: "statement-delete", id: "thm:oracle-rate",
        reason: "obsolete", direction: "delete-obsolete",
      }),
    ])).rejects.toThrow();
    expect(await readEscalationLog(ctx)).toHaveLength(0);
  });
});

describe("d0_cancel_mandate.ts", () => {
  it("persists one content-addressed, provenance-only cancellation for an outstanding mandate", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    const proto = JSON.parse(
      await readFile(path.resolve(__TOOLS_ROOT, "test/fixtures/stat_ate_overlap_decay_proto_core.json"), "utf8"),
    );
    await writeFile(protoPath, JSON.stringify(proto), "utf8");
    const state = await loadState(repoRoot, QID, SPEC);
    state.proposed_from = {
      topic: "test", novelty_target: "field", pivot_budget_used: 0, final_verdict: "ACCEPT",
      proposal_path: protoPath, novelty_justification: "fixture", chosen_qid: QID,
      chosen_specialization: SPEC, current_angle_index: 0, current_version: 1,
    };
    await saveState(repoRoot, QID, SPEC, state);
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: {
        kind: "statement-delete", id: proto.statements[0].id,
        reason: "initial adjudication", direction: "delete-obsolete",
      },
      proposalRevision: "angle:0/version:1",
    });
    await saveWorkingState(ctx, {
      round: 4, proposal_revision: "angle:0/version:1", escalation_entries_consumed: 0, solved: {},
      required_core_edit_mandates: [mandate],
    });

    await run("d0_cancel_mandate.ts", [
      "--mandate-id", mandate.mandate_id,
      "--reason", "mandatory reviewer rejected the stale metadata snapshot",
    ]);

    const entry = (await readEscalationLog(ctx))[0];
    expect(entry.provenance_only).toBe(true);
    expect(entry.cancelled_core_edit_mandates).toEqual([expect.objectContaining({
      cancellation_id: expect.stringMatching(/^d0c:[a-f0-9]{64}$/),
      mandate_id: mandate.mandate_id,
      reason: "mandatory reviewer rejected the stale metadata snapshot",
    })]);
  });

  it("can retire one rejected mandate while the pending set contains conflicts", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    const proto = JSON.parse(
      await readFile(path.resolve(__TOOLS_ROOT, "test/fixtures/stat_ate_overlap_decay_proto_core.json"), "utf8"),
    );
    await writeFile(protoPath, JSON.stringify(proto), "utf8");
    const state = await loadState(repoRoot, QID, SPEC);
    state.proposed_from = {
      topic: "test", novelty_target: "field", pivot_budget_used: 0, final_verdict: "ACCEPT",
      proposal_path: protoPath, novelty_justification: "fixture", chosen_qid: QID,
      chosen_specialization: SPEC, current_angle_index: 0, current_version: 1,
    };
    await saveState(repoRoot, QID, SPEC, state);
    const first = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: {
        kind: "statement-delete", id: proto.statements[0].id,
        reason: "first adjudication", direction: "delete-obsolete",
      },
      proposalRevision: "angle:0/version:1",
    });
    const conflicting = makeRequiredCoreEditMandate({
      core: proto, working: null,
      edit: {
        kind: "statement-delete", id: proto.statements[0].id,
        reason: "superseding adjudication", direction: "delete-obsolete",
      },
      proposalRevision: "angle:0/version:1",
    });
    await saveWorkingState(ctx, {
      round: 4, proposal_revision: "angle:0/version:1", escalation_entries_consumed: 0, solved: {},
      required_core_edit_mandates: [first, conflicting],
    });

    await run("d0_cancel_mandate.ts", [
      "--mandate-id", first.mandate_id,
      "--reason", "mandatory reviewer superseded this exact operation",
    ]);

    const entry = (await readEscalationLog(ctx))[0];
    expect(entry.cancelled_core_edit_mandates).toEqual([expect.objectContaining({
      mandate_id: first.mandate_id,
    })]);
  });
});

describe("d0_narrow_pending_directive.ts", () => {
  it("atomically narrows exactly one unconsumed directive and preserves its prose", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });
    await saveWorkingState(ctx, { round: 4, escalation_entries_consumed: 1, solved: {}, proposals: {
      statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [],
    } });
    await writeFile(escalationLogPath(ctx), [
      JSON.stringify({ round: 3, changed: [], directive: "already consumed", required_core_targets: ["oeq:x", "thm:x"] }),
      JSON.stringify({ round: 4, changed: [], note: "keep me", directive: "resolve exactly", require_core_changes: true,
        required_core_targets: ["oeq:x", "thm:x", "oeq:residual"] }),
      "",
    ].join("\n"));

    await run("d0_narrow_pending_directive.ts", ["--owner", "oeq:x", "--drop-target", "thm:x"]);

    const entries = await readEscalationLog(ctx);
    expect(entries[0].required_core_targets).toEqual(["oeq:x", "thm:x"]);
    expect(entries[1]).toMatchObject({ note: "keep me", directive: "resolve exactly", require_core_changes: true });
    expect(entries[1].required_core_targets).toEqual(["oeq:x", "oeq:residual"]);
    expect((await loadWorkingState(ctx))?.escalation_entries_consumed).toBe(1);
  });

  it("refuses to rewrite a consumed or ambiguous directive", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });
    await saveWorkingState(ctx, { round: 4, escalation_entries_consumed: 1, solved: {}, proposals: {
      statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [],
    } });
    await writeFile(escalationLogPath(ctx), JSON.stringify({ round: 3, changed: [], directive: "consumed",
      required_core_targets: ["oeq:x", "thm:x"] }) + "\n");
    await expect(run("d0_narrow_pending_directive.ts", ["--owner", "oeq:x", "--drop-target", "thm:x"]))
      .rejects.toThrow();
  });
});

describe("D0 opaque serialized fields", () => {
  it("does not decode canonical JSON inside a resolved-OEQ fingerprint", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const fingerprint = JSON.stringify({
      kind: "openendedquestion",
      statement: "Does \\(x\\) satisfy the bound?\n\\[x\\le 1\\]",
      depends_on: ["def:x"],
    });
    await saveWorkingState(ctx, {
      round: 2,
      // The write boundary now enforces that a resolution's theorem is held by
      // the store (Phase 1 single-store invariant), so the fixture carries it.
      solved: {
        "thm:x": {
          proof_tex: "P",
          snapshot: { stmt: "S", depends_on: [], defs: {}, assumptions: {} },
          node: { id: "thm:x", kind: "theorem", statement: "S", depends_on: [], status: "proved" } as never,
        },
      },
      resolved_oeqs: { "oeq:x": { theorem_id: "thm:x", source_fingerprint: fingerprint } },
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    });
    const loaded = await loadWorkingState(ctx);
    const stored = loaded?.resolved_oeqs?.["oeq:x"];
    expect(typeof stored === "string" ? stored : stored?.source_fingerprint).toBe(fingerprint);
    expect(() => JSON.parse(typeof stored === "string" ? stored : stored!.source_fingerprint)).not.toThrow();
  });
});

describe("d0_apply_change.ts", () => {
  it("discards an all-rejected bundle without mutating the proto", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const protoBytes = await readFile(protoSrc, "utf8");
    const proto = JSON.parse(protoBytes);
    await writeFile(path.join(dir, "proto_core.json"), protoBytes, "utf8");
    await writeFile(path.join(dir, "core.json"), protoBytes, "utf8");
    const target = proto.statements[0];
    await saveWorkingState(ctx, {
      round: 7,
      solved: {},
      proposals: {
        statements: [{
          id: target.id, current: target.statement, proposed: `${target.statement} rejected`,
          reason: "review rejected it", direction: "narrow",
        }],
        definitions: [], assumptions: [], coreEdits: [],
        proofs: [{ id: target.id, proof_tex: "rejected provisional proof", argues_proposed: true }],
      },
    });

    await run("d0_apply_change.ts", ["--discard-all", "--note", "Codex rejected every selector"]);

    expect(await readFile(path.join(dir, "proto_core.json"), "utf8")).toBe(protoBytes);
    await expect(access(path.join(dir, "core.json"))).rejects.toThrow();
    expect((await loadWorkingState(ctx))?.proposals).toEqual({
      statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [],
    });
    const entries = await readEscalationLog(ctx);
    expect(entries).toHaveLength(1);
    expect(entries[0].changed).toEqual([]);
    expect(entries[0].note).toMatch(/DISCARDED ALL 1.*Codex rejected every selector/);
  });

  // A rejected apply used to be reported AFTER the real apply had already rewound
  // stage_completed, rewritten the proto, appended the escalation entry, and run
  // clearRoundOutputs — deleting core.json, every proposed_*.json, and the round's
  // solve_*.json — while telling the operator "nothing was mutated". Recovering a
  // discarded round costs a full xhigh solve, so pin the non-mutation guarantee.
  //
  // Uses a REAL proto fixture: a hand-minimised core does not satisfy CoreSchema, so
  // applyProposedChanges throws during parse and the test passes vacuously against
  // the buggy build (verified — the first version of this test did exactly that).
  it("mutates NOTHING when a requested id matches no proposal", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });

    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    await writeFile(path.join(dir, "core.json"), JSON.stringify(proto), "utf8");

    const target = proto.statements[0];
    await writeFile(
      path.join(dir, "proposed_statement_changes.json"),
      JSON.stringify([{
        id: target.id, current: target.statement, proposed: `${target.statement} MUTATED`,
        reason: "r", direction: "narrow",
      }]),
      "utf8",
    );
    const before = await loadState(repoRoot, QID, SPEC);

    // One real id + one typo'd id: the whole invocation must be refused, untouched.
    await expect(run("d0_apply_change.ts", ["--ids", `${target.id},thm:typo`])).rejects.toThrow();

    const protoAfter = JSON.parse(await readFile(path.join(dir, "proto_core.json"), "utf8"));
    expect(protoAfter.statements[0].statement).not.toContain("MUTATED");
    await expect(access(path.join(dir, "core.json"))).resolves.toBeUndefined();
    await expect(access(path.join(dir, "proposed_statement_changes.json"))).resolves.toBeUndefined();
    expect((await loadState(repoRoot, QID, SPEC)).stage_completed).toBe(before.stage_completed);
    expect(await readEscalationLog(ctx)).toHaveLength(0);
  });
});

describe("d0_rebuild_review_packet.ts", () => {
  async function sealLiveProposalBasis(ctx: PipelineContext, proto: any): Promise<void> {
    const working = await loadWorkingState(ctx);
    if (!working?.proposals) throw new Error("test fixture has no live proposal carrier to seal");
    working.proposals.basis_revision = coreRevision(assembleCore(proto, working));
    await saveWorkingState(ctx, working);
  }

  async function seedUnpairedRecoveryFixture(
    proofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>,
  ): Promise<{ ctx: PipelineContext; solvePath: string; target: any }> {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const target = proto.statements[0];
    const proposed = `${target.statement} Corrected.`;
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    await writeFile(path.join(dir, "core.json"), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, { round: 2, solved: {} });
    const solvePath = path.join(dir, "solve_recovery.json");
    await writeFile(solvePath, JSON.stringify({
      proofs,
      proposed_core_edits: [{
        kind: "statement-replace", id: target.id,
        proposed: { ...target, statement: proposed, free_symbols: [] },
        reason: "correct the claim", direction: "correct",
      }],
    }), "utf8");
    return { ctx, solvePath, target };
  }

  it("refuses unauthenticated lost-bundle reconstruction from a raw solve file", async () => {
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const target = proto.statements[0];
    const { ctx, solvePath } = await seedUnpairedRecoveryFixture([
      { id: target.id, proof_tex: "Proof of the old claim.", argues_proposed: false },
    ]);

    await expect(run("d0_rebuild_review_packet.ts", [
      "--solve-json", solvePath, "--repair-unpaired-claim-edits",
    ])).rejects.toMatchObject({ stderr: expect.stringMatching(/only augment an existing capability-projected live bundle/i) });

    expect((await loadWorkingState(ctx))?.proposals?.proofs ?? []).toEqual([]);
    const unchanged = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(unchanged.statements[0].statement).toBe(target.statement);
  });

  it("rejects duplicate same-id proof intent before augmenting a live bundle", async () => {
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const target = proto.statements[0];
    const { ctx, solvePath } = await seedUnpairedRecoveryFixture([
      { id: target.id, proof_tex: "First proof payload." },
      { id: target.id, proof_tex: "First proof payload.", argues_proposed: true },
    ]);
    const raw = JSON.parse(await readFile(solvePath, "utf8"));
    raw.proposed_statement_changes = [{
      id: target.id, current: target.statement, proposed: raw.proposed_core_edits[0].proposed.statement,
      reason: "correct the claim", direction: "correct",
    }];
    await writeFile(solvePath, JSON.stringify(raw), "utf8");
    const working = await loadWorkingState(ctx);
    working!.proposals = {
      statements: raw.proposed_statement_changes, definitions: [], assumptions: [],
      coreEdits: raw.proposed_core_edits,
      proofs: [{ id: target.id, proof_tex: "First proof payload.", argues_proposed: true }],
    };
    await saveWorkingState(ctx, working!);
    await sealLiveProposalBasis(ctx, proto);

    await expect(run("d0_rebuild_review_packet.ts", [
      "--solve-json", solvePath, "--augment-live-proposals",
    ])).rejects.toMatchObject({ stderr: expect.stringMatching(/duplicate proof id/i) });

    expect((await loadWorkingState(ctx))?.proposals?.proofs).toEqual([
      { id: target.id, proof_tex: "First proof payload.", argues_proposed: true },
    ]);
    const unchanged = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8"));
    expect(unchanged.statements[0].statement).toBe(target.statement);
  });

  it("retains live solver proofs and exact cited receipts without promoting unrelated partial context", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const main = proto.statements[0];
    const support = proto.statements[1];
    const cited: CoreStatement = {
      id: "lem:cited-support", kind: "lemma", statement: "A cited support fact.",
      depends_on: [], status: "cited", source: { cite: proto.bibliography[0].key, locator: "Theorem 1" },
      free_symbols: [],
    };
    const unfinished: CoreStatement = {
      id: "lem:unfinished-context", kind: "lemma", statement: "An unfinished contextual claim.",
      depends_on: [], status: "to-prove", free_symbols: [],
    };
    const mainProof = "Fresh proof against the metadata postimage.";
    const supportProof = "Previously reviewed durable support proof.";
    proto.statements.push(cited);
    const settledSupport = Object.fromEntries(
      proto.statements
        .filter((statement: CoreStatement) => statement.id !== main.id && statement.id !== cited.id)
        .map((statement: CoreStatement) => [
          statement.id,
          {
            proof_tex: statement.id === support.id ? supportProof : `Durable proof for ${statement.id}.`,
            snapshot: wiredSnapshot(
              proto,
              statement,
              statement.id === support.id ? supportProof : `Durable proof for ${statement.id}.`,
            ),
          },
        ]),
    );
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    await writeFile(path.join(dir, "core.json"), JSON.stringify(proto), "utf8");
    const metadataEdit = {
      kind: "statement-replace" as const, id: main.id,
      proposed: {
        ...main,
        depends_on: [...main.depends_on, cited.id],
        consumer: `${main.consumer ?? "consumer"} (clarified)`,
      },
      reason: "metadata clarification", direction: "correct" as const,
    };
    await saveWorkingState(ctx, {
      round: 2,
      solved: {
        ...settledSupport,
        [main.id]: { proof_tex: mainProof, snapshot: wiredSnapshot(proto, main, "Old proof."), partial: true },
        [cited.id]: {
          proof_tex: "", snapshot: wiredSnapshot(proto, cited, ""),
        },
        [unfinished.id]: {
          node: unfinished,
          owner: main.id,
          proof_tex: "Only a partial argument, not a completed proof.",
          snapshot: wiredSnapshot(proto, unfinished, "Only a partial argument, not a completed proof."),
          partial: true,
        },
      },
      proposals: {
        statements: [], definitions: [], assumptions: [], coreEdits: [metadataEdit],
        proofs: [{ id: main.id, proof_tex: mainProof }],
        citationRevalidations: [cited],
      },
    });
    await sealLiveProposalBasis(ctx, proto);
    const solvePath = path.join(dir, "solve_recovery.json");
    await writeFile(solvePath, JSON.stringify({
      proofs: [{ id: main.id, proof_tex: mainProof }],
      added_lemmas: [cited],
      proposed_core_edits: [metadataEdit],
    }), "utf8");

    await expect(run("d0_rebuild_review_packet.ts", [
      "--solve-json", solvePath,
      "--augment-live-proposals",
    ])).rejects.toMatchObject({
      stderr: expect.stringMatching(/cannot recover cited-source receipts.*normal D0 solve\/merge path/i),
    });

    const rebuiltRun = await run("d0_rebuild_review_packet.ts", []);
    const rebuilt = await loadWorkingState(ctx);
    expect(rebuilt?.proposals?.proofs).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: main.id, proof_tex: mainProof }),
    ]));
    expect(rebuilt?.proposals?.proofs.some((proof) => proof.id === support.id)).toBe(false);
    expect(rebuilt?.proposals?.proofs.some((proof) => proof.id === unfinished.id)).toBe(false);
    expect(rebuilt?.solved[support.id]?.partial).not.toBe(true);
    expect(rebuilt?.proposals?.citationRevalidations).toEqual([cited]);
    const packet = JSON.parse(await readFile(JSON.parse(rebuiltRun.stdout).packet, "utf8"));
    expect(packet.citation_revalidations).toEqual([cited]);
    expect(packet.recovery.explicitly_included_durable_proof_ids).toEqual([]);

    await run("d0_apply_change.ts", ["--all", "--check"]);
    await run("d0_apply_change.ts", ["--all"]);
    const applied = await loadWorkingState(ctx);
    expect(applied?.solved[main.id]?.partial).not.toBe(true);
    expect(applied?.solved[support.id]?.partial).not.toBe(true);
    expect(applied?.solved[cited.id]?.partial).not.toBe(true);
  });

  it("repins whitespace-equivalent proposal guards to durable bytes", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const target = proto.statements[0];
    target.statement = "Claim introduction.\n\\[\n x = 1.\n\\]\nConclusion.";
    const proposed = `${target.statement} Narrowed.`;
    const proof = "Proof of the proposed totalized claim.";
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    await writeFile(path.join(dir, "core.json"), JSON.stringify(proto), "utf8");
    await saveWorkingState(ctx, {
      round: 2, solved: {},
      proposals: {
        statements: [{
          id: target.id,
          current: "Claim introduction. \\[ x = 1. \\] Conclusion.",
          proposed,
          reason: "totalize the claim", direction: "narrow",
        }],
        definitions: [], assumptions: [], coreEdits: [],
        proofs: [{ id: target.id, proof_tex: proof, argues_proposed: true }],
      },
    });
    await sealLiveProposalBasis(ctx, proto);

    const rebuiltRun = await run("d0_rebuild_review_packet.ts", []);

    const rebuilt = await loadWorkingState(ctx);
    expect(rebuilt?.proposals?.basis_revision).toBe(coreRevision(assembleCore(proto, rebuilt!)));
    expect(rebuilt?.proposals?.statements).toContainEqual(
      expect.objectContaining({ id: target.id, current: target.statement, proposed }),
    );
    expect(rebuilt?.proposals?.proofs).toContainEqual(
      expect.objectContaining({ id: target.id, proof_tex: proof, argues_proposed: true }),
    );
    const report = JSON.parse(rebuiltRun.stdout);
    const packet = JSON.parse(await readFile(report.packet, "utf8"));
    expect(packet.proposed_statement_changes).toContainEqual(
      expect.objectContaining({ id: target.id, current: target.statement, proposed }),
    );
    expect(packet.provisional_proofs).toContainEqual(
      expect.objectContaining({ id: target.id, proof_tex: proof, argues_proposed: true }),
    );
  });

  it("never validates an old published-core revision then repins to newer durable bytes", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const target = proto.statements[0];
    const oldStatement = target.statement;
    const staleRevision = statementRevision(target);
    target.statement = `${oldStatement} New durable qualification.`;
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    const stalePublished = structuredClone(proto);
    stalePublished.statements[0].statement = oldStatement;
    await writeFile(path.join(dir, "core.json"), JSON.stringify(stalePublished), "utf8");
    await saveWorkingState(ctx, {
      round: 2, solved: {},
      proposals: {
        statements: [{
          id: target.id,
          current: oldStatement,
          based_on_revision: staleRevision,
          proposed: `${oldStatement} Narrowed.`,
          reason: "authored against the old published view", direction: "narrow",
        }],
        definitions: [], assumptions: [], coreEdits: [], proofs: [],
      },
    });

    // The old revision must never authorize a repin onto the newer durable
    // bytes — but one defective guard is a per-change defect: the rebuild
    // succeeds, warns, and leaves the guard untouched for apply's exact-guard
    // skip instead of blocking the whole mechanical recovery lane.
    const rebuilt = await run("d0_rebuild_review_packet.ts", []);
    expect(rebuilt.stderr).toMatch(/matches no current view/);
    expect(JSON.parse(rebuilt.stdout).normalized_current_echo_ids).toEqual([]);
    const unchanged = await loadWorkingState(ctx);
    expect((unchanged?.proposals?.statements[0] as { current?: string } | undefined)?.current)
      .toBe(oldStatement);
  });

  it("retires durable-proof inclusion because preimage bytes cannot certify a semantic postimage", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    const target = proto.statements[0];
    const support = proto.statements[2];
    const supportProof = "Previously settled proof under the pre-mandate symbol basis.";
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    await writeFile(path.join(dir, "core.json"), JSON.stringify(proto), "utf8");
    const metadataEdit = {
      kind: "statement-replace" as const,
      id: target.id,
      proposed: { ...target, consumer: `${target.consumer ?? "consumer"} clarified` },
      reason: "clarify metadata",
      direction: "correct" as const,
    };
    await saveWorkingState(ctx, {
      round: 2,
      proposal_revision: "angle:0/version:1",
      escalation_entries_consumed: 0,
      solved: {
        [support.id]: { proof_tex: supportProof, snapshot: wiredSnapshot(proto, support, supportProof) },
      },
      proposals: {
        statements: [], definitions: [], assumptions: [], coreEdits: [metadataEdit], proofs: [],
      },
    });
    await sealLiveProposalBasis(ctx, proto);
    const state = await loadState(repoRoot, QID, SPEC);
    state.proposed_from = {
      topic: "test", novelty_target: "field", pivot_budget_used: 0, final_verdict: "ACCEPT",
      proposal_path: path.join(dir, "proto_core.json"), novelty_justification: "fixture",
      chosen_qid: QID, chosen_specialization: SPEC, current_angle_index: 0, current_version: 1,
    };
    await saveState(repoRoot, QID, SPEC, state);
    const symbol = proto.symbols[0];
    const mandate = makeRequiredCoreEditMandate({
      core: proto,
      working: await loadWorkingState(ctx),
      edit: {
        kind: "symbol-replace", name: symbol.name,
        proposed: { ...symbol, def: `${symbol.def} under a changed semantic basis` },
        reason: "correct symbol semantics", direction: "correct",
      },
      proposalRevision: "angle:0/version:1",
    });
    await appendEscalationLog(ctx, {
      round: 2, changed: [], directive: "apply the symbol correction", require_core_changes: true,
      required_core_edit_mandates: [mandate],
    });

    await expect(run("d0_rebuild_review_packet.ts", [
      "--include-durable-proof", support.id,
    ])).rejects.toMatchObject({
      stderr: expect.stringMatching(/include-durable-proof is retired.*normal D0 solve\/merge path/i),
    });
    expect((await loadWorkingState(ctx))?.solved[support.id]?.partial).not.toBe(true);
  });

  it("durably recovers an unconsumed mandate and quarantines its same-target proof", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    const dir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
    await mkdir(dir, { recursive: true });
    const protoSrc = path.resolve(__TOOLS_ROOT, "test", "fixtures", "stat_ate_overlap_decay_proto_core.json");
    const proto = JSON.parse(await readFile(protoSrc, "utf8"));
    await writeFile(path.join(dir, "proto_core.json"), JSON.stringify(proto), "utf8");
    const target = proto.statements[0];
    const state = await loadState(repoRoot, QID, SPEC);
    state.proposed_from = {
      topic: "test", novelty_target: "field", pivot_budget_used: 0, final_verdict: "ACCEPT",
      proposal_path: path.join(dir, "proto_core.json"), novelty_justification: "fixture",
      chosen_qid: QID, chosen_specialization: SPEC, current_angle_index: 0, current_version: 1,
    };
    await saveState(repoRoot, QID, SPEC, state);
    const edit = {
      kind: "statement-delete" as const, id: target.id,
      reason: "independently adjudicated obsolete claim", direction: "delete-obsolete" as const,
    };
    const mandate = makeRequiredCoreEditMandate({
      core: proto, working: null, edit, proposalRevision: "angle:0/version:1",
    });
    await saveWorkingState(ctx, {
      round: 2, escalation_entries_consumed: 0, proposal_revision: "angle:0/version:1", solved: {},
      proposals: {
        statements: [], definitions: [], assumptions: [], coreEdits: [],
        proofs: [{ id: target.id, proof_tex: "Adversarial proof of the obsolete claim." }],
      },
    });
    await appendEscalationLog(ctx, {
      round: 2, changed: [], directive: "delete the obsolete claim", require_core_changes: true,
      required_core_edit_mandates: [mandate],
    });

    await run("d0_rebuild_review_packet.ts", []);

    const rebuilt = await loadWorkingState(ctx);
    expect(rebuilt?.required_core_edit_mandates).toEqual([expect.objectContaining({ mandate_id: mandate.mandate_id })]);
    expect(rebuilt?.proposals?.coreEdits).toEqual([expect.objectContaining({ kind: "statement-delete", id: target.id })]);
    expect(rebuilt?.proposals?.proofs).not.toContainEqual(expect.objectContaining({ id: target.id }));
  });
});
