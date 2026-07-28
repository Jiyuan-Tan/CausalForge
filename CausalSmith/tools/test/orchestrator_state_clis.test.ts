import { mkdir, mkdtemp, writeFile, readFile, access } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { beforeEach, describe, expect, it } from "vitest";
import { createInitialState, loadState, saveState } from "../src/state.js";
import {
  escalationLogPath,
  loadWorkingState,
  readEscalationLog,
  saveWorkingState,
} from "../src/discovery/stages/d0_working.js";
import type { PipelineContext } from "../src/types.js";

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
  it("appends a standalone directive to the D0 escalation log (no hand-append)", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });

    await run("d0_directive.ts", ["--directive", "use the plug-in estimator with a Nadaraya-Watson smoother"]);

    const entries = await readEscalationLog(ctx);
    expect(entries).toHaveLength(1);
    expect(entries[0].changed).toEqual([]);
    expect(entries[0].directive).toMatch(/Nadaraya-Watson/);
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
      solved: {},
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
