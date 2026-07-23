import { describe, it, expect, beforeAll, beforeEach, afterAll, vi } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, readdir, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import {
  runStage0Solve,
  groupToProveByComponent,
  repairSolveUnitLatexSerialization,
  selectDirectiveEmissionOwnerLabel,
  selectSemanticTargetOwners,
} from "../../src/discovery/stages/d0_solve.js";
import { runStage0Typed, partitionProposedChanges, findingKeys } from "../../src/discovery/stages/d0.js";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";

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
  await mkdir(path.dirname(wp), { recursive: true });
  await writeFile(wp, JSON.stringify(working), "utf8");
}

/** The surfaced payload on the carrier (empty object when no working state). */
async function readSurfacedProposals(ctx: PipelineContext): Promise<Record<string, any[]>> {
  const wp = workingPath(ctx);
  if (!existsSync(wp)) return {};
  return (JSON.parse(await readFile(wp, "utf8")).proposals ?? {}) as Record<string, any[]>;
}
import {
  appendEscalationLog,
  escalationLogPath,
  saveWorkingState,
  workingPath,
  pruneOrphanLemmas,
} from "../../src/discovery/stages/d0_working.js";
import { canonicalLeanSubdir, promptPath, statePath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const QID = "stat_solvetest";
const SPEC = "v1";

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
      await writeFile(outPath, JSON.stringify(body), "utf8");
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
        await writeFile(outPath, JSON.stringify({
          proofs: [{ id: target, proof_tex: "QED." }],
          added_lemmas: [{
            id: "lem:shared-helper",
            kind: "lemma",
            statement: target === "thm:main" ? "First incompatible claim." : "Second incompatible claim.",
            depends_on: [],
            status: "proved",
            proof_tex: "Proof.",
          }],
        }), "utf8");
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
    expect(prompts).toHaveLength(2);
    const ownerPrompts = prompts.filter((prompt) =>
      prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads")
    );
    expect(ownerPrompts).toHaveLength(1);
    // Equal-size components prefer the headline theorem, not dispatch/Promise
    // completion order, as the deterministic integration point.
    expect(ownerPrompts[0]).toContain('"id": "thm:main"');
    const localPrompt = prompts.find((prompt) => prompt.includes("You are FORBIDDEN to"))!;
    expect(localPrompt).toContain("cite or add that exact id to `depends_on`");
    expect(localPrompt).toContain("lem:shared-comparator, sym:tau, sym:t_pi");

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
          proposed: { ...PROTO.definitions[0], construction: `${marker} envelope` },
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
      {
        name: "reverse-dependency metadata edit",
        diagnostic: "core-edit.*metadata:reverse-dependencies",
        edit: (marker: string) => ({
          kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
          reason: `${marker} reverse-edge rebuild`, direction: "correct",
        }),
      },
    ] as const).map(({ name, diagnostic, edit }) => ({
      name,
      diagnostic,
      build: (marker: string) => ({ proposed_core_edits: [edit(marker)] }),
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
      name: "cited comparator addition",
      diagnostic: "cited-added-node.*lem:singleton-comparator",
      build: (marker: string) => ({ added_lemmas: [{
        id: "lem:singleton-comparator", kind: "lemma", statement: `${marker} comparator statement`,
        depends_on: [], status: "cited",
        source: {
          cite: "Rosenbaum1983", locator: "Section 1", verbatim_statement: `${marker} source excerpt`,
        },
      }] }),
      artifact: coreJsonPath,
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
    "projects non-owner $name through the directive-wide capability owner",
    async ({ diagnostic, required, build, artifact }) => {
      const ctx = makeCtx(repoRoot);
      await appendEscalationLog(ctx, {
        round: 1,
        changed: [],
        directive: "exercise the centralized singleton write-capability matrix",
        ...(required ? { require_core_changes: true, required_core_targets: [required] } : {}),
      });
      const completionOrder: string[] = [];
      const deps: StageDeps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
          const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
          const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
          const owner = prompt.includes("You are the ONLY solve unit allowed to emit directive-wide shared payloads");
          if (owner && diagnostic.includes("metadata:reverse-dependencies")) {
            await new Promise((resolve) => setTimeout(resolve, 20));
          }
          await writeFile(outPath, JSON.stringify({
            proofs: targets.map(({ id }) => ({ id, proof_tex: `Proof of ${id}.` })),
            ...build(owner ? "OWNER" : "SIBLING"),
          }), "utf8");
          completionOrder.push(owner ? "owner" : "sibling");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      };

      const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
      try {
        await runStage0Solve({ ctx, state: makeState(), deps });
        expect(warn).toHaveBeenCalledWith(expect.stringMatching(
          new RegExp(`quarantined unauthorized ${diagnostic}.*SIBLING|quarantined unauthorized ${diagnostic}.*prop:aux`, "i"),
        ));
      } finally {
        warn.mockRestore();
      }
      if (diagnostic.includes("metadata:reverse-dependencies")) {
        expect(completionOrder).toEqual(["sibling", "owner"]);
      }
      const canonical = await readFile(artifact(ctx), "utf8");
      expect(canonical).toContain("OWNER");
      expect(canonical).not.toContain("SIBLING");
    },
  );

  it("fails closed when an exact catalog target has only a non-owner emission", async () => {
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
          proposed_core_edits: owner ? [] : [{
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

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /exact target sym:tau had unauthorized-only core-edit.*prop:aux.*capability owner thm:main emitted no authorized payload/i,
    );
    expect(existsSync(coreJsonPath(ctx))).toBe(false);
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

    // The round survives to the normal proposal checkpoint (a core edit always gates
    // for orchestrator adjudication) instead of aborting on a rationale mismatch.
    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(result.message).toMatch(/rebuild-reverse-dependencies/i);
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
    expect(() => selectSemanticTargetOwners([
      { label: "thm:first", targets: [{ id: "lem:shared" }] },
      { label: "thm:second", targets: [{ id: "lem:shared" }] },
    ])).toThrow(/ambiguous semantic ownership.*lem:shared.*thm:first,\s*thm:second/i);
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
        };
        const siblingReplacement = {
          ...proto.statements[0],
          depends_on: ["ass:overlap", "def:upper-schedule", "def:lf-admissible-schedules"],
        };
        await writeFile(outPath, JSON.stringify({
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
        }), "utf8");
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

  it("fails closed when an exact statement target has only an unauthorized sibling payload", async () => {
    const ctx = makeCtx(repoRoot);
    await appendEscalationLog(ctx, {
      round: 1,
      changed: [],
      directive: "repair prop:aux through its semantic owner",
      require_core_changes: true,
      required_core_targets: ["prop:aux"],
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

    await expect(runStage0Solve({ ctx, state: makeState(), deps })).rejects.toThrow(
      /exact target prop:aux had unauthorized-only core-edit.*thm:main.*capability owner prop:aux emitted no authorized payload/i,
    );
    expect(existsSync(coreJsonPath(ctx))).toBe(false);
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
          proposed_core_edits: [],
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

  it("recovers an exact required agent-added target omitted from working state", async () => {
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
    await writeFile(coreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [...PROTO.statements, required],
    }), "utf8");
    await saveWorkingState(ctx, {
      round: 3,
      escalation_entries_consumed: 0,
      solved: {},
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
        await writeFile(outPath, JSON.stringify({
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
        }), "utf8");
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
          proofs: targets
            .filter((target) => target.id !== rate.id)
            .map((target) => ({ id: target.id, proof_tex: `Reproved ${target.id}.` })),
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
        await writeFile(outPath, JSON.stringify(body), "utf8");
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
    expect(afterApply.solved[rate.id]).toMatchObject({ partial: true });
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
        await writeFile(outPath, JSON.stringify({
          proofs: targets.map((t) => ({ id: t.id, proof_tex: "QED." })),
          proposed_assumptions: [{
            id: "ass:overlap",
            condition: "the propensity is bounded away from 0 and 1",
            reason: "restating the standing support condition",
            standard_or_novel: "standard: Rosenbaum1983",
            not_crux: "background condition",
          }],
        }), "utf8");
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
        await writeFile(outPath, JSON.stringify({
          proofs: targets.filter((t) => t.id !== "thm:main").map((t) => ({ id: t.id, proof_tex: "QED." })),
          proposed_statement_changes: hasMain
            ? [{ id: "thm:main", current: "tau is identified", proposed: "tau is identified on the overlap region", reason: "needs overlap", direction: "narrow" }]
            : [],
          open_obligations: hasMain
            ? [{ node_id: "thm:main", what_is_open: "the full-support case", obstruction: "no bound without overlap", attempted: "direct decomposition" }]
            : [],
        }), "utf8");
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

  it("keeps a round-added lemma's catalog node when ANOTHER unit supplies its proof", async () => {
    // The parking mechanism only covers the ordering where the proving unit runs BEFORE
    // the installing unit. In the other ordering the id is already in statementIds, so
    // the proof takes the inline branch, whose `priorAgent` reads the PREVIOUS round —
    // undefined for a lemma added this round — and recordProof then replaced the
    // node-carrying record with a node-less one. Next round carryPlan drops the lemma
    // ("record carries no statement definition"): a proved lemma silently vanishes, or
    // its consumers dangle. Ownership must come from the SAME-round install.
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
                 depends_on: [], status: "to-prove" }]
            : [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0Solve({ ctx, state: makeState(), deps });
    expect(String((result as { message?: string }).message ?? "")).not.toMatch(/PLUMBING FAULT/);
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const rec = working.solved["lem:cross-helper"];
    expect(rec?.node, "the agent-added lemma must keep its catalog node definition").toBeDefined();
    expect(rec?.node?.id).toBe("lem:cross-helper");
    expect(rec?.proof_tex).toBe("Proved by the sibling unit.");
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
    let calls = 0;
    let agentReproofCalls = 0;
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        calls += 1;
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const targetBlock = prompt.split("=== TARGET STATEMENT(S) TO SOLVE")[1] ?? "";
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
    expect(pending.solved["thm:replicated-boundary"]).toMatchObject({ partial: true });

    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(agentReproofCalls).toBe(1);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:replicated-boundary")).toMatchObject({
      status: "proved",
      proof_tex: "Apply the corrected separator.",
    });
    expect(core.statements.find((s: any) => s.id === "lem:replicated-separator")).toMatchObject({
      status: "proved",
      proof_tex: "The corrected frontier admits the separator.",
    });

    const callsAfterReproof = calls;
    await runStage0Solve({ ctx, state: makeState(), deps });
    expect(calls).toBe(callsAfterReproof);
  });

  it("accepts statement-delete at the structured solver-output boundary", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.statements[1].depends_on = ["thm:main"];
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

  it("applies typed assumption, deletion, symbol, bibliography, and reverse-edge edits", async () => {
    const ctx = makeCtx(repoRoot);
    const proto = structuredClone(PROTO) as any;
    proto.symbols[0].role = "open target";
    proto.assumptions[0].used_by = ["thm:stale"];
    proto.symbols.push({ name: "unused_handle", type: "scalar", role: "obsolete notation" });
    proto.definitions.push({ id: "def:obsolete-handle", name: "old", construction: "future program", inputs: [] });
    proto.target_estimand = "H_F: equality holds " + "\f" + "orall units";
    proto.statements[0].depends_on.push("def:obsolete-handle");
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
    expect(updated.statements[0].depends_on).not.toContain("def:obsolete-handle");
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
    expect(updated.assumptions[0].used_by).toEqual(["def:class", "prop:aux"]);

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["conj:obsolete-result"]).toBeUndefined();
    expect(working.solved["prop:carried-consumer"].node.depends_on).toEqual(["thm:canonical-result"]);
    expect(working.solved["prop:carried-consumer"].snapshot.depends_on).toEqual(["conj:obsolete-result"]);

    await runStage0Solve({ ctx, state: makeState(), deps: solverDeps("prove") });
    const rebuilt = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rebuilt.statements.some((s: any) => s.id === "conj:obsolete-result")).toBe(false);
    expect(rebuilt.statements.some((s: any) => s.id === "thm:canonical-result")).toBe(true);
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
      proposed: { ...node, depends_on: ["ass:overlap", "def:env"] },
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
    await seedWorkingProposals(ctx, { coreEdits: [{
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
        const mine = !emittedResolution;
        emittedResolution = true;
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

    await runStage0Solve({ ctx, state: makeState(), deps });

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
  });

  it("discharges a recovered agent-authored cited target emitted again through added_lemmas", async () => {
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
    await runStage0Solve({ ctx, state: makeState(), deps });

    const rebuilt = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(rebuilt.statements.find((s: any) => s.id === citedNode.id)).toMatchObject({
      status: "cited",
      source: { locator: "Section 2" },
    });
    expect(calls).toBe(2);
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
    expect(prompts.find((p) => p.includes("You are the ONLY solve unit allowed"))).toContain(
      "sibling-only ids",
    );
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
    for (const artifact of [directedCore, directedProto]) {
      expect(artifact.tldr).toBe("The sharp operational threshold is now proved.");
      expect(artifact.honest_scope).toContain("threshold is settled");
      expect(artifact.sampling_model).toEqual({
        design: "The corrected scoped design description.",
        units: "Independent replicated units; this sibling must survive a design-only update.",
      });
      expect(artifact.statements.find((s: any) => s.id === "thm:a").consumer).toBe("Operational design screening.");
    }

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
    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["thm:sharp-rate-answer"].node.consumer).toBe("Use the exact rate for inference.");
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
    expect((await readSurfacedProposals(ctx)).statements.length).toBeGreaterThan(0);
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
    // a class-targeted def change is rejected; with no other proposed change and all
    // targets proved, the run discharges cleanly (no checkpoint) and SAYS it ignored it.
    expect("status" in res ? res.status : "clean").not.toBe("checkpoint");
    expect(res.message).toMatch(/discharged/i);
    expect(res.message).toMatch(/ignored .*illegal class\/unknown def/i);
    // and this run surfaced NO definition change (the illegal change was dropped).
    expect(((await readSurfacedProposals(ctx)).definitions ?? []).length).toBe(0);
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
        await writeFile(outPath, JSON.stringify(body), "utf8");
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
        await writeFile(outPath, JSON.stringify(makeBody(targets, prompt)), "utf8");
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
    const deps = depsReturning((targets) => ({
      proofs: targets.filter((t) => t.id !== "oeq:tight").map((t) => ({ id: t.id, proof_tex: "QED." })),
      added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
      open_obligations: targets.some((t) => t.id === "oeq:tight") ? [{ node_id: "oeq:tight", what_is_open: "tightness", obstruction: "open", attempted: "x" }] : [],
    }));
    const res = (await runStage0Solve({ ctx, state: makeState(), deps })) as any;
    expect("status" in res).toBe(false); // Stage0SolveResult = clean discharge (OEQ residual did NOT halt)
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: any) => s.id === "thm:main").status).toBe("proved");
    expect(core.statements.find((s: any) => s.id === "oeq:tight").status).toBe("to-prove"); // legitimately left open
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
