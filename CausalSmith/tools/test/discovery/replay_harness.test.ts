// Pins the replay-harness behaviors mandated by the Phase 0 adversarial audit
// (2026-07-30 migration plan). Each test reproduces one audit finding: reverting the
// corresponding fix in src/discovery/replay.ts makes exactly that test fail.
//
//   F1  packets replay THROUGH the apply validator (structural validity is not enough)
//   F2  new-generation receipts (transaction_id-stamped) require full field shape;
//       legacy receipt generations stay tolerated
//   F3  the temp copy carries the run-root state.json (live proposal-revision basis)
//   F4  the expected pending-change count mirrors the apply's content-dedupe
//   F5  unreadable directories gate the sweep instead of silently shrinking coverage

import { describe, it, expect } from "vitest";
import { appendFile, chmod, mkdir, mkdtemp, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { saveWorkingState, escalationLogPath } from "../../src/discovery/stages/d0_working.js";
import {
  copyRunForReplay,
  replayPacketFile,
  replayRun,
  runReplay,
} from "../../src/discovery/replay.js";
import { createDStageHarness, type DStageHarness } from "./d_stage_harness.js";

const PROTO = {
  qid: "stat_replay", specialization: "v1", cluster: "stat",
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

const validChange = { id: "thm:main", current: "LIVE CLAIM", proposed: "NEW CLAIM", reason: "r", direction: "narrow" };

function researchRootOf(h: DStageHarness): string {
  return path.join(h.repoRoot, "doc", "research");
}

function discoveryDirOf(h: DStageHarness): string {
  return path.join(h.repoRoot, "doc", "research", "active", "stat_replay", "discovery");
}

async function seedWorking(h: DStageHarness, proposals: Record<string, unknown[]>): Promise<void> {
  await saveWorkingState(h.ctx(), {
    round: 1,
    solved: {},
    resolved_oeqs: {},
    proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [], ...proposals },
  } as never);
}

describe("replay harness (Phase 0 audit findings)", () => {
  it("F4: duplicate proposal entries do not produce a count-mismatch failure", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      // Two byte-identical proposals: the apply dedupes by JSON content and validates
      // ONE change; the harness's expected count must agree, not report a mismatch.
      await seedWorking(h, { statements: [validChange, { ...validChange }] });
      const res = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(res.failures, "duplicate proposals are valid; no failure expected").toEqual([]);
      expect(res.notes.join("\n")).toContain("validated 1 pending change(s)");
    } finally { await h.dispose(); }
  }, 30000);

  it("F2: a new-generation receipt with a truncated element fails; a legacy one passes", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, {});
      const logPath = escalationLogPath(h.ctx());
      await mkdir(path.dirname(logPath), { recursive: true });
      // Legacy generation: no transaction_id, elements carry only id+kind — real
      // corpus shape (29 of 1663 elements), must stay tolerated.
      await appendFile(logPath, JSON.stringify({ round: 1, changed: [{ id: "thm:main", kind: "statement" }] }) + "\n");
      const okRes = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(okRes.failures, "legacy receipt shape is valid history").toEqual([]);

      // New generation: transaction_id present ⇒ full {id,kind,from,to,reason} required.
      await appendFile(
        logPath,
        JSON.stringify({ transaction_id: "d0apply:test", round: 2, changed: [{ id: "thm:main", kind: "statement" }] }) + "\n",
      );
      const badRes = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        badRes.failures.some((f) => f.includes("missing from/to/reason")),
        `new-generation receipt must be complete; got ${JSON.stringify(badRes.failures)}`,
      ).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("F3: the temp copy carries the run-root state.json", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      const runRoot = path.dirname(discoveryDirOf(h));
      await writeFile(path.join(runRoot, "state.json"), JSON.stringify({ stage_completed: "0" }), "utf8");
      const tmpRepo = await mkdtemp(path.join(os.tmpdir(), "replay-test-"));
      try {
        const { tmpRun } = await copyRunForReplay(discoveryDirOf(h), tmpRepo, "stat_replay");
        const { existsSync } = await import("node:fs");
        expect(
          existsSync(path.join(tmpRun, "state.json")),
          "state.json is the live proposal-revision basis for mandate resolution and must travel with the copy",
        ).toBe(true);
      } finally {
        const { rm } = await import("node:fs/promises");
        await rm(tmpRepo, { recursive: true, force: true });
      }
    } finally { await h.dispose(); }
  }, 30000);

  it("F1: an apply-contract-invalid packet is surfaced by the validator replay", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, {});
      // Structurally VALID packet whose proposal echoes a `current` that does not match
      // the proto — the round_34 incident class. Structural checks alone grade this
      // packet green; only the validator replay can refuse it.
      const core = await h.readProto();
      const packet = {
        contract: "test contract",
        full_current_paper_tex: "",
        current_typed_core: core,
        durable_working_state: { round: 1, solved: {}, resolved_oeqs: {} },
        proposed_statement_changes: [{ ...validChange, current: "STALE ECHO — NOT THE LIVE CLAIM" }],
        proposed_definition_changes: [],
        proposed_assumptions: [],
        proposed_core_edits: [],
        provisional_proofs: [],
      };
      const pktPath = path.join(discoveryDirOf(h), "proposal_review_packet.json");
      await writeFile(pktPath, JSON.stringify(packet), "utf8");
      const res = await replayPacketFile(pktPath, researchRootOf(h));
      expect(
        res.failures.some((f) => f.includes("apply check-mode")),
        `active-tier packet with a stale echo must fail the validator replay; got failures=${JSON.stringify(res.failures)} warnings=${JSON.stringify(res.warnings)}`,
      ).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("F1 control: a contract-valid packet replays green through the validator", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, { statements: [validChange] });
      const core = await h.readProto();
      const packet = {
        contract: "test contract",
        full_current_paper_tex: "",
        current_typed_core: core,
        durable_working_state: {
          round: 1, solved: {}, resolved_oeqs: {},
          proposals: { statements: [validChange], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
        },
        proposed_statement_changes: [validChange],
        proposed_definition_changes: [],
        proposed_assumptions: [],
        proposed_core_edits: [],
        provisional_proofs: [],
      };
      const pktPath = path.join(discoveryDirOf(h), "proposal_review_packet.json");
      await writeFile(pktPath, JSON.stringify(packet), "utf8");
      const res = await replayPacketFile(pktPath, researchRootOf(h));
      expect(res.failures).toEqual([]);
      expect(res.warnings).toEqual([]);
      expect(res.notes.join("\n")).toContain("validated 1 pending change(s)");
    } finally { await h.dispose(); }
  }, 30000);

  it("F5: an unreadable directory gates the sweep as a failure", async () => {
    if (process.platform === "win32") return; // POSIX permission semantics
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    const locked = path.join(researchRootOf(h), "active", "locked_dir");
    try {
      await seedWorking(h, {});
      await mkdir(locked, { recursive: true });
      await chmod(locked, 0o000);
      const summary = await runReplay({ researchRoot: researchRootOf(h) });
      expect(
        summary.failures.some((f) => f.startsWith("walk: unreadable directory")),
        `coverage gaps must gate; got ${JSON.stringify(summary.failures)}`,
      ).toBe(true);
    } finally {
      await chmod(locked, 0o755).catch(() => {});
      await h.dispose();
    }
  }, 30000);

  it("R2-F1/R3-F1: a pending transaction is graded by production's recovery validator", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, {});
      const txnPath = path.join(discoveryDirOf(h), "d0_apply_transaction.json");
      const liveProtoBytes = JSON.stringify(PROTO); // exactly what the harness seeded on disk
      const receipt = {
        transaction_id: "d0apply:y", round: 1,
        changed: [{ id: "thm:main", kind: "statement", from: "LIVE CLAIM", to: "NEW CLAIM", reason: "r" }],
      };

      // (a) Schema-invalid post-image: parseable JSON text, but not a valid core.
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: "{}",
        escalation_entry: receipt,
      }), "utf8");
      const badCore = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        badCore.failures.some((f) => f.includes("fails production recovery validation")),
        `corrupt proto_after must gate; got ${JSON.stringify(badCore.failures)}`,
      ).toBe(true);

      // (b) Receipt not stamped with the transaction id — recovery calls this corrupt.
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: liveProtoBytes,
        escalation_entry: { ...receipt, transaction_id: "d0apply:OTHER" },
      }), "utf8");
      const badId = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        badId.failures.some((f) => f.includes("fails production recovery validation")),
        `id-mismatched receipt must gate; got ${JSON.stringify(badId.failures)}`,
      ).toBe(true);

      // (c) Live proto bytes match neither image — recovery refuses to replay.
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: "{\"not\":\"the live proto\"}",
        proto_after: JSON.stringify({ ...PROTO, qid: "stat_replay" }).replace("LIVE CLAIM", "OTHER CLAIM"),
        escalation_entry: receipt,
      }), "utf8");
      const badBasis = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        badBasis.failures.some((f) => f.includes("fails production recovery validation")),
        `off-basis transaction must gate; got ${JSON.stringify(badBasis.failures)}`,
      ).toBe(true);

      // (d) An empty receipt WITHOUT a directive cannot have been produced by the
      // current writer (its own guard returns before the transaction write)...
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: liveProtoBytes,
        escalation_entry: { ...receipt, changed: [] },
      }), "utf8");
      const emptyChanged = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        emptyChanged.failures.some((f) => f.includes("changed is empty")),
        `empty receipt must gate; got ${JSON.stringify(emptyChanged.failures)}`,
      ).toBe(true);

      // (d-2) A receipt with NO changed field at all would make recovery return
      // undefined against its contract — the writer always constructs it (R5-F1).
      const { changed: _omitted, ...receiptSansChanged } = receipt;
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: liveProtoBytes,
        escalation_entry: receiptSansChanged,
      }), "utf8");
      const noChanged = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        noChanged.failures.some((f) => f.includes("changed is missing")),
        `missing changed[] must gate; got ${JSON.stringify(noChanged.failures)}`,
      ).toBe(true);

      // (d-3) directive="" is falsy to the writer's guard, so changed=[] with an
      // empty-string directive is equally unproducible (R5-F2).
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: liveProtoBytes,
        escalation_entry: { ...receipt, changed: [], directive: "" },
      }), "utf8");
      const emptyDirective = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        emptyDirective.failures.some((f) => f.includes("changed is empty")),
        `empty-string directive must not exempt an empty receipt; got ${JSON.stringify(emptyDirective.failures)}`,
      ).toBe(true);

      // (d') ...but a DIRECTIVE-ONLY apply legitimately writes changed=[] (R4-F2).
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: liveProtoBytes,
        escalation_entry: { ...receipt, changed: [], directive: "reopen thm:main with a sharper constant" },
      }), "utf8");
      const directiveOnly = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(directiveOnly.failures, "a directive-only transaction is recoverable").toEqual([]);

      // (d'') A corrupt transaction gates even when the working cursor is ABSENT —
      // recovery needs neither store, so the grading must not either (R4-F1).
      const { rm: rmFile } = await import("node:fs/promises");
      await rmFile(path.join(discoveryDirOf(h), "d0_working.json"), { force: true });
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: "{}",
        escalation_entry: receipt,
      }), "utf8");
      const noWorking = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(
        noWorking.failures.some((f) => f.includes("fails production recovery validation")),
        `corrupt transaction must gate without a working cursor; got ${JSON.stringify(noWorking.failures)}`,
      ).toBe(true);
      await seedWorking(h, {}); // restore for the remaining cases

      // (e) A transaction production recovery WOULD replay grades green.
      await writeFile(txnPath, JSON.stringify({
        version: 1, transaction_id: "d0apply:y", proto_before: liveProtoBytes, proto_after: liveProtoBytes,
        escalation_entry: receipt,
      }), "utf8");
      const ok = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(ok.failures, "a recoverable pending transaction is not a defect").toEqual([]);
      expect(ok.notes.join("\n")).toContain("check-mode skipped");
    } finally { await h.dispose(); }
  }, 30000);

  it("R2-F2: a packet with no sibling proto is a per-target problem, and runReplay survives it", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, {});
      const core = await h.readProto();
      // A dir with core.json but NO proto: identity extraction succeeds, proto copy cannot.
      const orphanDir = path.join(researchRootOf(h), "active", "orphan_run", "discovery");
      await mkdir(orphanDir, { recursive: true });
      await writeFile(path.join(orphanDir, "core.json"), JSON.stringify(core), "utf8");
      const packet = {
        contract: "test contract",
        full_current_paper_tex: "",
        current_typed_core: core,
        durable_working_state: { round: 1, solved: {}, resolved_oeqs: {} },
        proposed_statement_changes: [],
        proposed_definition_changes: [],
        proposed_assumptions: [],
        proposed_core_edits: [],
        provisional_proofs: [],
      };
      const pktPath = path.join(orphanDir, "proposal_review_packet.json");
      await writeFile(pktPath, JSON.stringify(packet), "utf8");

      const res = await replayPacketFile(pktPath, researchRootOf(h));
      expect(
        res.failures.some((f) => f.includes("no sibling proto_core.json")),
        `missing proto must be a recorded problem, not a crash; got ${JSON.stringify(res.failures)}`,
      ).toBe(true);

      // And the whole sweep completes despite the orphan target.
      const summary = await runReplay({ researchRoot: researchRootOf(h) });
      expect(summary.packetTotal).toBeGreaterThan(0);
      expect(summary.failures.some((f) => f.includes("no sibling proto_core.json"))).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("R2-F3: --only requires a non-flag value; unknown flags are usage errors", async () => {
    const { parseReplayArgs } = await import("../../src/discovery/replay.js");
    expect(parseReplayArgs([])).toEqual({ only: null, verbose: false });
    expect(parseReplayArgs(["--verbose"])).toEqual({ only: null, verbose: true });
    expect(parseReplayArgs(["--only", "stat_x", "--verbose"])).toEqual({ only: "stat_x", verbose: true });
    expect("error" in parseReplayArgs(["--only"]), "bare --only is a usage error").toBe(true);
    expect("error" in parseReplayArgs(["--only", "--verbose"]), "--only must not consume a flag").toBe(true);
    expect("error" in parseReplayArgs(["--frobnicate"]), "unknown flag is a usage error").toBe(true);
  });

  it("R2-F4: proofs-only packet/store drift is surfaced", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, {});
      const core = await h.readProto();
      const packet = {
        contract: "test contract",
        full_current_paper_tex: "",
        current_typed_core: core,
        durable_working_state: {
          round: 1, solved: {}, resolved_oeqs: {},
          proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
        },
        proposed_statement_changes: [],
        proposed_definition_changes: [],
        proposed_assumptions: [],
        proposed_core_edits: [],
        // Drift ONLY in proofs: the durable store carries none.
        provisional_proofs: [{ id: "thm:main", proof_tex: "QED." }],
      };
      const pktPath = path.join(discoveryDirOf(h), "proposal_review_packet.json");
      await writeFile(pktPath, JSON.stringify(packet), "utf8");
      const res = await replayPacketFile(pktPath, researchRootOf(h));
      expect(
        res.failures.some((f) => f.includes("proofs diverge")),
        `proofs drift must be surfaced; got failures=${JSON.stringify(res.failures)} warnings=${JSON.stringify(res.warnings)}`,
      ).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("regression: a quiet run with no proposals replays fully green", async () => {
    const h = await createDStageHarness({ qid: "stat_replay", specialization: "v1", proto: PROTO });
    try {
      await seedWorking(h, {});
      const res = await replayRun(discoveryDirOf(h), researchRootOf(h));
      expect(res.failures).toEqual([]);
      expect(res.warnings).toEqual([]);
      expect(res.qid).toBe("stat_replay");
    } finally { await h.dispose(); }
  }, 30000);
});
