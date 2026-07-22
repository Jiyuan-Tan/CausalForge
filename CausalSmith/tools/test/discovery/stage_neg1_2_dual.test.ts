import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it, vi } from "vitest";
import {
  runStageNeg1_2ProtoCore,
  protoCoreJsonPath,
} from "../../src/discovery/stages/neg1_2_author.js";
import { runStageNeg1_2Dual } from "../../src/discovery/stages/neg1_2.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";

let repoRoot: string;
let goldenCore: string;

async function stubPrompts(root: string): Promise<void> {
  const stub = async (name: string, body: string) => {
    const target = promptPath(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, body, "utf8");
  };
  await stub("stage_neg1_2_proto_core.txt", "stub proposal author (formal + prose contract)");
  // The author now composes a mode head + the body; stub every mode head.
  for (const m of ["cold_start", "revise", "pivot", "kernel_replace", "draft_rebuild"]) {
    await stub(`stage_neg1_2_proto_head_${m}.txt`, `stub ${m} head`);
  }
}

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}

function makeState(): StateJson {
  return {
    stage_completed: "-1.2",
    lean_subdir: `CausalSmith/Stat/${QID}`,
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { local_fix_from_4d: false, missing_architecture: false },
    proposed_from: {
      topic: "test",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "accept",
      proposal_path: "",
      novelty_justification: "",
      chosen_qid: QID,
      chosen_specialization: SPEC,
      cluster: "stat",
    },
  } as unknown as StateJson;
}

/** runCodex stub: writes `coreBody` to the core path, returns `extra` handoff keys. */
function authorDeps(coreBody: string, extra: Record<string, unknown> = {}): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
      if (!m) throw new Error("authorDeps: no core path in prompt");
      const target = m[1].trim();
      await mkdir(path.dirname(target), { recursive: true });
      await writeFile(target, coreBody, "utf8");
      return {
        stdout: JSON.stringify({ status: "completed", message: "core", artifacts: [target], ...extra }),
        stderr: "",
      };
    },
    runClaude: async () => {
      throw new Error("runClaude not expected");
    },
    lean: undefined as never,
  };
}

/** needs-pivot author: writes a diagnostic core but returns only the minimal status receipt. */
function needsPivotDeps(coreBody: string): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
      if (!m) throw new Error("needsPivotDeps: no core path in prompt");
      const target = m[1].trim();
      await mkdir(path.dirname(target), { recursive: true });
      await writeFile(target, coreBody, "utf8");
      return {
        stdout: JSON.stringify({ status: "needs-pivot", message: "initial kernel is invalid" }),
        stderr: "",
      };
    },
    runClaude: async () => {
      throw new Error("runClaude not expected");
    },
    lean: undefined as never,
  };
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "neg12single-"));
  await stubPrompts(repoRoot);
  goldenCore = await readFile(
    new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
    "utf8",
  );
});

afterAll(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage -1.2 author (single artifact: formal + prose → gate → schema-validate)", () => {
  it("makes standalone orchestrator directives outrank an ACCEPT with no reviewer flags", async () => {
    const prompt = await readFile(
      new URL("../../src/discovery/prompts/D-1/stage_neg1_2_proto_head_revise.txt", import.meta.url),
      "utf8",
    );
    expect(prompt).toContain("overrides this mode's reviewer-flags-only / kernel-preserved scope");
    expect(prompt).toContain("prior verdict is `ACCEPT` with empty S / N / C flags");
    expect(prompt).toContain("Empty reviewer flags never authorize a no-op");
  });

  it("writes the core, passes the gate, and renders NO proposal .tex", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const res = await runStageNeg1_2ProtoCore({ ctx, state, mode: "cold-start", deps: authorDeps(goldenCore) });
    expect(existsSync(res.protoCoreJsonPath)).toBe(true);
    // The proto_core JSON is the sole discovery artifact; no proposal .tex is rendered.
    expect(existsSync(artifactPaths(ctx, state).proposalTex)).toBe(false);
  });

  it("preserves the SC6 comparator promise table across schema canonicalization", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.comparator_promise_table = [{
      comparator_bibkey: "Tsybakov2009",
      comparator_claim: "A published minimax comparator claim.",
      matched_by: "Theorem 1",
      match_kind: "strict_tightening",
    }];

    const res = await runStageNeg1_2ProtoCore({
      ctx,
      state: makeState(),
      mode: "revise",
      deps: authorDeps(JSON.stringify(core)),
    });
    const persisted = JSON.parse(await readFile(res.protoCoreJsonPath, "utf8"));
    expect(persisted.comparator_promise_table).toEqual(core.comparator_promise_table);
  });

  it("warns with the key names when the persist boundary drops non-schema keys", async () => {
    const ctx = makeCtx(repoRoot);
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.__unknown_mandated_field = "the author complied but nothing persists this key";
    const warnSpy = vi.spyOn(console, "warn").mockImplementation(() => {});
    try {
      await runStageNeg1_2ProtoCore({
        ctx,
        state: makeState(),
        mode: "revise",
        deps: authorDeps(JSON.stringify(core)),
      });
      const calls = warnSpy.mock.calls.map((c) => c.join(" "));
      expect(
        calls.some((c) => c.includes("__unknown_mandated_field") && c.includes("dropped")),
        `expected a console.warn naming the dropped key; got: ${JSON.stringify(calls)}`,
      ).toBe(true);
    } finally {
      warnSpy.mockRestore();
    }
  });

  it("THROWS when the authored core fails the gate (GP2: a proven statement)", async () => {
    const ctx = makeCtx(repoRoot);
    const broken = JSON.parse(goldenCore);
    broken.statements[0].status = "proved";
    await expect(
      runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "cold-start", deps: authorDeps(JSON.stringify(broken)) }),
    ).rejects.toThrow(/proposal gate/);
  });

  it("THROWS when the authored core fails the gate (GP3: missing tldr)", async () => {
    const ctx = makeCtx(repoRoot);
    const broken = JSON.parse(goldenCore);
    delete broken.tldr;
    await expect(
      runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "cold-start", deps: authorDeps(JSON.stringify(broken)) }),
    ).rejects.toThrow(/proposal gate/);
  });

  it("THROWS when the authored core omits the mandatory comparator promise table", async () => {
    const ctx = makeCtx(repoRoot);
    const broken = JSON.parse(goldenCore);
    delete broken.comparator_promise_table;
    await expect(
      runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "revise", deps: authorDeps(JSON.stringify(broken)) }),
    ).rejects.toThrow(/proposal gate[\s\S]*comparator_promise_table/);
  });

  it("THROWS when the model reports failed", async () => {
    const ctx = makeCtx(repoRoot);
    const deps: StageDeps = {
      runCodex: async () => ({
        stdout: JSON.stringify({ status: "failed", message: "kernel not authorable" }),
        stderr: "",
      }),
      runClaude: async () => {
        throw new Error("unused");
      },
      lean: undefined as never,
    };
    await expect(runStageNeg1_2ProtoCore({ ctx, state: makeState(), mode: "cold-start", deps })).rejects.toThrow(/failed/);
  });
});

describe("runStageNeg1_2Dual (rollout step 5 — one author + render + harvest)", () => {
  it("harvests diagnostic-core seeds before returning needs-pivot", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.seeds = ["alternative lower-bound experiment", "certified-ratio coverage"];
    core.seed_details = [{ seed: "alternative lower-bound experiment", motif: "M7" }];
    core.literature_map = { anchor: "Dorn2025", gap: "finite-sample coverage" };

    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: needsPivotDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });

    expect(res.status).toBe("completed");
    expect(state.proposed_from!.last_draft_status).toBe("needs-pivot");
    expect(state.proposed_from!.seed_list).toEqual([
      "alternative lower-bound experiment",
      "certified-ratio coverage",
    ]);
    expect(state.proposed_from!.seed_details).toEqual([
      { seed: "alternative lower-bound experiment", motif: "M7" },
    ]);
    expect(state.proposed_from!.literature_map).toBe(
      JSON.stringify({ anchor: "Dorn2025", gap: "finite-sample coverage" }),
    );
  });

  it("classifies a sandbox-startup needs-pivot as env-failure, not a dead angle", async () => {
    // The monolith called handoffSignalsEnvFailure on the needs-pivot receipt; the
    // carve lost that call, so `last_draft_status` was set to "needs-pivot"
    // unconditionally and the entire D-0.5 env-failure retry branch
    // (NEG1_ENV_FAILURE_RETRY_BUDGET, flags.neg1_env_failure_retries) was dead code —
    // a codex sandbox-spawn failure burned a healthy angle as "not authorable".
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const m = prompt.match(/proposal core JSON to this path \(create it\): (.+)/);
        if (!m) throw new Error("env-failure deps: no core path in prompt");
        const target = m[1].trim();
        await mkdir(path.dirname(target), { recursive: true });
        await writeFile(target, goldenCore, "utf8");
        return {
          stdout: JSON.stringify({
            status: "needs-pivot",
            message: "could not run the derivation",
            blocking_reason: "windows sandbox: spawn setup refresh (os error 740)",
          }),
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("runClaude not expected"); },
      lean: undefined as never,
    };

    const res = await runStageNeg1_2Dual({
      ctx, state, deps, mode: "cold-start", nextVersion: 1, angleIndex: 0,
    });
    expect(res.status).toBe("completed");
    expect(state.proposed_from!.last_draft_status).toBe("env-failure");
  });

  it("authors the core (no .tex) and harvests the handoff into proposed_from", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const deps = authorDeps(goldenCore, {
      literature_checklist: [{ bibkey: "Tsybakov2009", relevant_to: "thm:lower" }],
      cluster: "stat",
      novelty_justification: "novel: matching converse under overlap decay",
      seeds: ["seedA"],
      seed_details: [{ one_liner: "overlap-decay rate" }],
      literature_map: "the lit map",
    });
    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps,
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });
    expect(res.status).toBe("completed");
    expect(existsSync(protoCoreJsonPath(ctx))).toBe(true);
    // No proposal .tex; proposal_path points at the proto_core JSON (the sole artifact).
    expect(existsSync(artifactPaths(ctx, state).proposalTex)).toBe(false);

    const pf = state.proposed_from as Record<string, unknown>;
    expect(pf.proposal_path).toBe(protoCoreJsonPath(ctx));
    expect(pf.current_version).toBe(1);
    expect(pf.last_draft_status).toBe("completed");
    expect(pf.cluster).toBe("stat");
    expect(pf.seed_list).toEqual(["seedA"]);
    expect(typeof pf.novelty_justification).toBe("string");
    expect(pf.last_draft_handoff as string).toContain("literature_checklist");
  });

  it("harvests ideation metadata from the core when the stdout receipt is minimal", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.seeds = ["core seed A", "core seed B"];
    core.seed_details = [{ seed: "core seed A", motif: "M20" }];
    core.literature_map = { anchor: "Tian and Pearl", gap: "mediator-defier frontier" };
    core.novelty_justification = "core-authored novelty case";
    core.literature_checklist = [{ bibkey: "TianPearl2000", relevant_to: "thm:pn" }];

    const res = await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core)),
      mode: "cold-start",
      nextVersion: 1,
      angleIndex: 0,
    });

    expect(res.status).toBe("completed");
    const pf = state.proposed_from as Record<string, unknown>;
    expect(pf.seed_list).toEqual(["core seed A", "core seed B"]);
    expect(pf.seed_details).toEqual([{ seed: "core seed A", motif: "M20" }]);
    expect(pf.literature_map).toBe(
      JSON.stringify({ anchor: "Tian and Pearl", gap: "mediator-defier frontier" }),
    );
    expect(pf.novelty_justification).toBe("core-authored novelty case");
    expect(pf.last_draft_handoff as string).toContain("TianPearl2000");
  });

  it("rehydrates missing seed state from a revised core after an interrupted run", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.proposed_from!.seed_list = [];
    const core = JSON.parse(goldenCore) as Record<string, unknown>;
    core.seeds = ["surviving pivot seed"];
    core.literature_map = "persisted literature map";

    await runStageNeg1_2Dual({
      ctx,
      state,
      deps: authorDeps(JSON.stringify(core)),
      mode: "revise",
      nextVersion: 6,
      angleIndex: 0,
    });

    expect(state.proposed_from!.seed_list).toEqual(["surviving pivot seed"]);
    expect(state.proposed_from!.literature_map).toBe("persisted literature map");
  });
});
