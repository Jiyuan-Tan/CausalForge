// A re-emitted helper whose CLAIM is byte-identical to an already-settled node must be
// a no-op discharge, not a collision. Observed cost: a valid ~4.9k-char canonical proof
// and a ~5.1k-char re-derivation shared the same id, statement, and dependency list —
// only the proof PROSE differed — and the prose difference alone forced a withheld-helper
// checkpoint plus a full recovery round. Proof prose is not part of a node's identity;
// only the claim is. The canonical proof stays active; the alternative payload stays in
// the round's solve_*.json for the archive sweep.
//
// A DIFFERENT claim under the same id must still collide (that guard is load-bearing and
// separately tested in stage0_solve.test.ts).

import { describe, it, expect, beforeAll, beforeEach, afterAll } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, readdir, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { appendEscalationLog, workingPath } from "../../src/discovery/stages/d0_working.js";
import { proofArchiveDir, readProofArchiveIndex } from "../../src/discovery/proof_archive.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const QID = "stat_reproof";
const SPEC = "v1";

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
    { id: "thm:main", kind: "theorem", statement: "tau is identified", depends_on: ["ass:overlap"], status: "to-prove", justification: "core ID", gap: "vs prior", consumer: "applied" },
  ],
  target_estimand: "tau = E[Y(1) - Y(0)]",
  bibliography: [{ key: "Rosenbaum1983" }],
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

/** Proves every target and (re-)emits `lem:shared` with a fixed claim and the given
 *  proof prose. Rounds differ ONLY in the helper's prose (and, when `deps` is
 *  passed, the ORDER of its dependency list). */
function emitHelper(proofProse: string, deps: string[] = []): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(seg.slice(seg.indexOf("["), seg.lastIndexOf("]") + 1)) as Array<{ id: string }>;
      await writeFile(outPath, JSON.stringify({
        // The helper travels ONLY through added_lemmas (the re-emission channel under
        // test); a direct `proofs` entry for it would be a legitimate directed re-proof.
        proofs: targets.filter((t) => t.id !== "lem:shared")
          .map((t) => ({ id: t.id, proof_tex: `By lem:shared, ${t.id} follows.` })),
        added_lemmas: [{
          id: "lem:shared", kind: "lemma", statement: "the shared helper claim", depends_on: deps,
          status: "proved", proof_tex: proofProse,
        }],
      }), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "dup-reproof-"));
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

describe("a stale solve artifact is archived before the pre-dispatch removal", () => {
  it("preserves an uncommitted prior round's proof bytes", async () => {
    // A round that dies before commit leaves solve_*.json as the ONLY copy of what its
    // dispatch paid for; the next dispatch of the same unit removes that file. The
    // removal must archive first (audit family: raw-file overwrite byte loss).
    const ctx = makeCtx();
    const dir = path.dirname(coreJsonPath(ctx));
    await writeFile(path.join(dir, "solve_thm_main.json"), JSON.stringify({
      proofs: [{ id: "thm:main", proof_tex: "bytes from a round that never committed" }],
    }), "utf8");

    await runStage0Solve({ ctx, state: makeState(), deps: emitHelper("fresh proof") });

    const index = await readProofArchiveIndex(dir);
    const stale = index.find((e) => e.node_id === "thm:main" && e.reason === "stale-dispatch-cleared");
    expect(stale, "the uncommitted prior bytes must reach the archive").toBeDefined();
  }, 30000);
});

describe("identical-claim re-proof of a settled node is a no-op discharge", () => {
  it("does not checkpoint, and the canonical proof stays active", async () => {
    const ctx = makeCtx();

    // Round 1: lem:shared lands with the canonical proof.
    const r1 = await runStage0Solve({ ctx, state: makeState(), deps: emitHelper("Canonical proof, round 1.") });
    expect((r1 as { status?: string }).status, "round 1 must discharge cleanly").not.toBe("checkpoint");

    // Round 2: a directed re-solve re-emits lem:shared — same id, same claim, same
    // dependencies — with different prose. This must NOT collide.
    await appendEscalationLog(ctx, { round: 2, changed: [], directive: "re-derive the targets" });
    const r2 = await runStage0Solve({ ctx, state: makeState(), deps: emitHelper("Alternative proof, round 2.") });

    expect((r2 as { status?: string }).status, "a prose-only re-proof must not cost a checkpoint round").not.toBe("checkpoint");
    expect(String((r2 as { message?: string }).message ?? "")).not.toMatch(/WITHHELD/);

    const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
    expect(working.solved["lem:shared"]?.proof_tex, "the canonical proof must stay active")
      .toBe("Canonical proof, round 1.");
    expect(working.solved["lem:shared"]?.partial, "the settled node must not reopen").toBeUndefined();

    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const lem = core.statements.find((s: { id: string }) => s.id === "lem:shared");
    expect(lem?.status).toBe("proved");
    expect(lem?.proof_tex).toBe("Canonical proof, round 1.");

    const withheldPath = path.join(path.dirname(coreJsonPath(ctx)), "withheld_content.json");
    expect(existsSync(withheldPath), "nothing may be reported withheld").toBe(false);

    // The alternative bytes must be archived AT ROUND COMMIT, not only when a later
    // apply happens to sweep solve_*.json — an ordinary next round overwrites the same
    // solve output path without any sweep (audit finding, 2026-07-21).
    const index = await readProofArchiveIndex(path.dirname(coreJsonPath(ctx)));
    const alt = index.find((e) => e.node_id === "lem:shared" && e.reason === "duplicate-reproof");
    expect(alt, "the skipped alternative proof must reach the cold archive at commit").toBeDefined();
    const body = await readFile(
      path.join(proofArchiveDir(path.dirname(coreJsonPath(ctx))), "objects", `${alt!.hash}.tex`),
      "utf8",
    );
    expect(body).toBe("Alternative proof, round 2.");
  }, 30000);

  it("treats a dependency-ORDER-only re-emission as the same claim (deps are a set)", async () => {
    // Dependencies are canonicalized as a sorted set everywhere else in proof reuse
    // (depsKey, computeValidNodes, oeqSourceFingerprint); LLM re-emission order is not
    // stable, so an order-only difference must not fall into the collision path and
    // cost a withheld-helper checkpoint plus a recovery round.
    const ctx = makeCtx();

    const r1 = await runStage0Solve({
      ctx, state: makeState(), deps: emitHelper("Canonical proof, round 1.", ["ass:overlap", "def:env"]),
    });
    expect((r1 as { status?: string }).status, "round 1 must discharge cleanly").not.toBe("checkpoint");

    await appendEscalationLog(ctx, { round: 2, changed: [], directive: "re-derive the targets" });
    const r2 = await runStage0Solve({
      ctx, state: makeState(), deps: emitHelper("Alternative proof, round 2.", ["def:env", "ass:overlap"]),
    });

    expect((r2 as { status?: string }).status, "an order-only re-proof must not cost a checkpoint round").not.toBe("checkpoint");
    expect(String((r2 as { message?: string }).message ?? "")).not.toMatch(/WITHHELD/);
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    const lem = core.statements.find((s: { id: string }) => s.id === "lem:shared");
    expect(lem?.status).toBe("proved");
    expect(lem?.proof_tex).toBe("Canonical proof, round 1.");
  }, 30000);
});
