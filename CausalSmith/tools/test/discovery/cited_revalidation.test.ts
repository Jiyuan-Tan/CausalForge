// Citation revalidation for REOPENED cited leaves (claim changed, citation kept).
//
// The supported channel is a byte-faithful `added_lemmas` re-emission of the complete
// cited node — the explicit "source still supports the current claim" receipt. Merge
// accepts it for BOTH origins:
//   - agent-authored (absent from proto, present in working) — the 2026-07-22 incident
//     (stat_block_orbit_conformal_certificate): repair solvers treated the re-emission
//     as a no-op, emitted nothing, and the exact-target gate livelocked;
//   - FROZEN proto members — their reopen (d0_apply) leaves the same schema-valid cited
//     leaf + partial working record, but the merge discharge path used to be gated on
//     `!sourceById.has(id)` (agent-only), so the mandated receipt was withheld as a
//     collision ("different claim" — false: the claim was byte-identical) and the leaf
//     could never be revalidated.
//
// For a frozen member the receipt must ALSO match the displayed source byte-for-byte:
// merge keeps the proto copy canonical, so accepting a different source would silently
// drop the solver's correction — a frozen source fix must travel the adjudicated
// statement-replace channel instead. (Agent-authored nodes stay wholesale-replaceable
// under an exact required directive; a directed source refresh relies on that.)

import { describe, it, expect, beforeAll, beforeEach, afterAll } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, readdir, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { appendEscalationLog, workingPath } from "../../src/discovery/stages/d0_working.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const QID = "stat_cited_reval";
const SPEC = "v1";

const FROZEN_COMPARATOR = {
  id: "lem:frozen-comparator",
  kind: "lemma",
  statement: "the narrowed comparator claim",
  depends_on: [],
  status: "cited",
  source: {
    cite: "Rosenbaum1983",
    locator: "Theorem 2",
    verbatim_statement: "The comparator claim.",
  },
  justification: "comparator context",
  gap: "n/a",
  consumer: "context",
};

const PROTO = {
  qid: QID,
  specialization: SPEC,
  cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{
    id: "ass:overlap", kind: "support", condition: "the propensity is bounded away from 0 and 1",
    free_symbols: [], standard: { name: "overlap", cite: "Rosenbaum1983" },
  }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [
    {
      id: "thm:main", kind: "theorem", statement: "tau is identified",
      depends_on: ["ass:overlap", "lem:frozen-comparator"], status: "to-prove",
      justification: "core ID", gap: "vs prior", consumer: "applied",
    },
    FROZEN_COMPARATOR,
  ],
  target_estimand: "tau = E[Y(1) - Y(0)]",
  bibliography: [{ key: "Rosenbaum1983" }],
};

const AGENT_COMPARATOR = {
  id: "lem:agent-comparator",
  kind: "lemma",
  statement: "the comparator claim",
  depends_on: [],
  status: "cited",
  source: {
    cite: "Rosenbaum1983",
    locator: "Section 4",
    verbatim_statement: "The comparator claim.",
  },
};

let repoRoot: string;

function makeCtx(): PipelineContext {
  return { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}
function makeState(): StateJson {
  return {
    stage_completed: "0",
    lean_subdir: `CausalSmith/Stat/${QID}`,
    design_decisions: {},
    added_assumptions: [],
    proposed_from: { topic: "t", novelty_target: "field", cluster: "stat" },
    flags: {},
  } as unknown as StateJson;
}

/** Proves every dispatched target except the emitted lemmas' own ids, and emits the
 *  given nodes through `added_lemmas` (the re-emission channel under test). */
function solveDeps(addedLemmas: Array<{ id: string }>): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = seg.includes("[")
        ? JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>
        : [];
      const skip = new Set(addedLemmas.map((l) => l.id));
      await writeFile(outPath, JSON.stringify({
        proofs: targets.filter((t) => !skip.has(t.id))
          .map((t) => ({ id: t.id, proof_tex: `Direct argument for ${t.id}.` })),
        added_lemmas: addedLemmas,
      }), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

/** Simulates the post-apply reopened state for the FROZEN cited leaf: the proto already
 *  carries the (accepted) narrowed claim, and the working cursor holds the seeded
 *  OLD-basis partial record d0_apply writes on reopen. */
async function reopenFrozenComparator(ctx: PipelineContext): Promise<void> {
  const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
  working.solved[FROZEN_COMPARATOR.id] = {
    proof_tex: "",
    snapshot: {
      stmt: "the comparator's previous claim",
      depends_on: [],
      defs: {},
      assumptions: {},
    },
    partial: true,
  };
  await writeFile(workingPath(ctx), JSON.stringify(working), "utf8");
  await appendEscalationLog(ctx, {
    round: 2,
    changed: [],
    directive: "revalidate the reopened comparator citation against its narrowed claim",
    required_core_targets: [FROZEN_COMPARATOR.id],
  });
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "cited-reval-"));
  for (const name of ["stage0_common_discovery.txt", "stage0_setup_stat.txt", "stage0_solve.txt"]) {
    const t = promptPath(repoRoot, name);
    await mkdir(path.dirname(t), { recursive: true });
    await writeFile(t, `stub ${name}`, "utf8");
  }
  const p = protoCoreJsonPath(makeCtx());
  await mkdir(path.dirname(p), { recursive: true });
  await writeFile(p, JSON.stringify(PROTO), "utf8");
});
afterAll(async () => { await rm(repoRoot, { recursive: true, force: true }); });

beforeEach(async () => {
  const ctx = makeCtx();
  const dir = path.dirname(coreJsonPath(ctx));
  for (const f of await readdir(dir)) {
    if (f.includes("proto_core")) continue;
    await rm(path.join(dir, f), { recursive: true, force: true });
  }
  await writeFile(protoCoreJsonPath(ctx), JSON.stringify(PROTO), "utf8");
});

describe("reopened FROZEN cited leaf", () => {
  it("byte-faithful re-emission is the revalidation receipt: clears partial, keeps the proto copy canonical", async () => {
    const ctx = makeCtx();

    const r1 = await runStage0Solve({ ctx, state: makeState(), deps: solveDeps([]) });
    expect((r1 as { status?: string }).status, "round 1 must discharge cleanly").not.toBe("checkpoint");

    await reopenFrozenComparator(ctx);
    const r2 = await runStage0Solve({ ctx, state: makeState(), deps: solveDeps([FROZEN_COMPARATOR]) });

    expect((r2 as { status?: string }).status, "the receipt must not cost a checkpoint round").not.toBe("checkpoint");
    expect(String((r2 as { message?: string }).message ?? "")).not.toMatch(/WITHHELD/);

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const rec = working.solved[FROZEN_COMPARATOR.id];
    expect(rec, "the receipt must refresh the working record").toBeDefined();
    expect(rec.partial, "the reopen must be cleared").toBeUndefined();
    expect(rec.snapshot.stmt, "the snapshot must now certify the CURRENT claim")
      .toBe(FROZEN_COMPARATOR.statement);
    expect(rec.node, "a frozen member must not enter the agent-node catalog").toBeUndefined();

    // The proto copy stays canonical: authored prose fields the re-emission carried
    // (or could have omitted) must not be clobbered by the receipt.
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const leaf = core.statements.find((s: { id: string }) => s.id === FROZEN_COMPARATOR.id);
    expect(leaf).toMatchObject({
      status: "cited",
      statement: FROZEN_COMPARATOR.statement,
      source: { locator: "Theorem 2" },
      justification: "comparator context",
    });
  }, 30000);

  it("a re-emission with a DIFFERENT source is withheld, not silently swapped", async () => {
    const ctx = makeCtx();

    const r1 = await runStage0Solve({ ctx, state: makeState(), deps: solveDeps([]) });
    expect((r1 as { status?: string }).status).not.toBe("checkpoint");

    await reopenFrozenComparator(ctx);
    const swapped = {
      ...FROZEN_COMPARATOR,
      source: { ...FROZEN_COMPARATOR.source, locator: "Theorem 3" },
    };
    const r2 = await runStage0Solve({ ctx, state: makeState(), deps: solveDeps([swapped]) });

    expect((r2 as { status?: string }).status, "a swapped frozen citation must reach the orchestrator").toBe("checkpoint");
    expect(String((r2 as { message?: string }).message ?? "")).toMatch(/WITHHELD/);

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved[FROZEN_COMPARATOR.id]?.partial, "the reopen must NOT clear").toBe(true);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: { id: string }) => s.id === FROZEN_COMPARATOR.id)?.source)
      .toMatchObject({ locator: "Theorem 2" });
  }, 30000);
});

describe("reopened AGENT-AUTHORED cited leaf (2026-07-22 incident, end-to-end)", () => {
  it("byte-faithful re-emission clears partial and refreshes the snapshot", async () => {
    const ctx = makeCtx();
    // Agent-flavour proto: the comparator exists ONLY in the working catalog.
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify({
      ...PROTO,
      statements: [{
        id: "thm:main", kind: "theorem", statement: "tau is identified",
        depends_on: ["ass:overlap"], status: "to-prove",
        justification: "core ID", gap: "vs prior", consumer: "applied",
      }],
    }), "utf8");

    const r1 = await runStage0Solve({ ctx, state: makeState(), deps: solveDeps([AGENT_COMPARATOR]) });
    expect((r1 as { status?: string }).status).not.toBe("checkpoint");

    // Claim-change invalidation: node carries the (already narrowed) current claim,
    // snapshot names the old one, `partial` holds the leaf open.
    const stale = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    stale.solved[AGENT_COMPARATOR.id].partial = true;
    stale.solved[AGENT_COMPARATOR.id].snapshot.stmt = "the comparator's previous claim";
    await writeFile(workingPath(ctx), JSON.stringify(stale), "utf8");
    await appendEscalationLog(ctx, {
      round: 2,
      changed: [],
      directive: "revalidate the comparator citation against its narrowed claim",
      required_core_targets: [AGENT_COMPARATOR.id],
    });

    const r2 = await runStage0Solve({ ctx, state: makeState(), deps: solveDeps([AGENT_COMPARATOR]) });
    expect((r2 as { status?: string }).status, "the receipt must not cost a checkpoint round").not.toBe("checkpoint");
    expect(String((r2 as { message?: string }).message ?? "")).not.toMatch(/WITHHELD/);

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    const rec = working.solved[AGENT_COMPARATOR.id];
    expect(rec.partial, "the reopen must be cleared").toBeUndefined();
    expect(rec.snapshot.stmt).toBe(AGENT_COMPARATOR.statement);
    expect(rec.node).toMatchObject({ status: "cited", source: { locator: "Section 4" } });

    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(core.statements.find((s: { id: string }) => s.id === AGENT_COMPARATOR.id))
      .toMatchObject({ status: "cited", source: { locator: "Section 4" } });
  }, 30000);
});
