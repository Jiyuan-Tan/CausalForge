// A D-stage round, runnable offline.
//
// Rounds need a temp repo, stubbed prompts, a seeded proto, a ctx/state pair, and a
// between-tests reset that keeps the proto but clears everything a round wrote. That
// setup was already written once inside `stage0_solve.test.ts`; putting a SECOND copy in
// the soak suite would recreate exactly the two-copies-that-drift pattern behind several
// of the faults these tests exist to catch. So it lives here, once.
//
// The solver is injected, so a round costs no agent tokens and can be run as often as
// needed — which is what makes sustained soak pressure affordable in the first place.

import { mkdtemp, mkdir, writeFile, readFile, readdir, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { workingPath } from "../../src/discovery/stages/d0_working.js";
import { canonicalLeanSubdir, promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

/** Prompts a D0 solve round reads. Stubbed — these tests exercise plumbing, not wording. */
const STUB_PROMPTS = ["stage0_common_discovery.txt", "stage0_setup_stat.txt", "stage0_solve.txt"];

export interface DStageHarness {
  readonly repoRoot: string;
  ctx(): PipelineContext;
  state(): StateJson;
  readProto(): Promise<Core>;
  readCore(): Promise<Core>;
  readWorking(): Promise<WorkingState>;
  writeProto(proto: Core): Promise<void>;
  /** Clear everything a round wrote, restoring the seeded proto. */
  reset(): Promise<void>;
  dispose(): Promise<void>;
}

export async function createDStageHarness(args: {
  qid: string;
  specialization: string;
  proto: unknown;
}): Promise<DStageHarness> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), `${args.qid}-`));
  const seeded = JSON.stringify(args.proto);
  const ctx = (): PipelineContext => ({
    repoRoot,
    qid: args.qid,
    specialization: args.specialization,
    dryRun: false,
    resume: false,
  });

  for (const name of STUB_PROMPTS) {
    const target = promptPath(repoRoot, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, `stub ${name}`, "utf8");
  }
  const protoPath = protoCoreJsonPath(ctx());
  await mkdir(path.dirname(protoPath), { recursive: true });
  await writeFile(protoPath, seeded, "utf8");

  const readJson = async <T>(p: string): Promise<T> => JSON.parse(await readFile(p, "utf8")) as T;

  return {
    repoRoot,
    ctx,
    state: () =>
      ({
        stage_completed: "0",
        // Must satisfy saveState's qid/lean_subdir invariant: runStage0Typed
        // persists the round budget before dispatch, so this stub gets saved.
        lean_subdir: canonicalLeanSubdir(args.qid),
        design_decisions: {},
        added_assumptions: [],
        proposed_from: { topic: "t", novelty_target: "field", cluster: "stat" },
        flags: {},
      }) as unknown as StateJson,
    readProto: () => readJson<Core>(protoCoreJsonPath(ctx())),
    readCore: () => readJson<Core>(coreJsonPath(ctx())),
    readWorking: () => readJson<WorkingState>(workingPath(ctx())),
    writeProto: async (proto) => { await writeFile(protoCoreJsonPath(ctx()), JSON.stringify(proto), "utf8"); },
    reset: async () => {
      const dir = path.dirname(coreJsonPath(ctx()));
      for (const f of await readdir(dir)) {
        if (f.includes("proto_core")) continue;
        await rm(path.join(dir, f), { recursive: true, force: true });
      }
      await writeFile(protoCoreJsonPath(ctx()), seeded, "utf8");
    },
    dispose: async () => { await rm(repoRoot, { recursive: true, force: true }); },
  };
}

/** A solver plus a record of what it was asked to solve. */
export interface RecordingSolver {
  deps: StageDeps;
  /** Target-id sets, one entry per dispatched unit, in call order. */
  dispatches(): string[][];
  /** Every target dispatched since the last `resetLog()`. */
  dispatchedSince(): Set<string>;
  resetLog(): void;
}

/**
 * A solver that proves every dispatched target and answers any dispatched OEQ with a
 * FRESH answer id each time it is asked.
 *
 * The renaming is deliberate and load-bearing. A stub that reuses one fixed answer id
 * cannot detect the churn fault at all: when the pipeline drops a resolution it
 * re-dispatches the OEQ, and a fixed-id solver answers with the same id, so the round is
 * silently wasted and the test still passes. (I made exactly that mistake writing this
 * harness — the first version asserted id stability against a fixed-id stub and passed
 * with the fix reverted.) Real solvers rename on re-derivation, which is how the fault
 * was originally spotted, so the stub models that.
 *
 * Re-dispatch is also recorded directly, because the cost of the fault is the wasted
 * round, not the rename.
 */
export function provingSolver(opts: { answerPrefix?: string } = {}): RecordingSolver {
  const prefix = opts.answerPrefix ?? "thm:rate-is-sharp";
  let answersGiven = 0;
  let log: string[][] = [];
  const deps: StageDeps = {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(
        segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1),
      ) as Array<{ id: string }>;
      log.push(targets.map((t) => t.id));
      const isOeq = (id: string): boolean => id.startsWith("oeq:");
      const answerId = `${prefix}-${++answersGiven}`;
      const body = {
        proofs: targets.filter((t) => !isOeq(t.id)).map((t) => ({ id: t.id, proof_tex: "QED." })),
        added_lemmas: [],
        proposed_statement_changes: [],
        resolved_oeqs: targets.filter((t) => isOeq(t.id)).map((t) => ({
          source_id: t.id,
          theorem: {
            id: answerId,
            kind: "theorem",
            statement: "the rate is sharp",
            depends_on: ["ass:overlap"],
            status: "proved",
            // The answer CITES the question it settles — as real answers do. That single
            // reference is the deadlock's precondition: the D0 boundary removes the `oeq:`
            // node from the core, so a gate unaware of resolutions reads this as a
            // cite-without-emit and issues an unsatisfiable auto-heal. A stub proving
            // "QED." exercises none of that.
            proof_tex: `This settles ${t.id} in the affirmative.`,
            justification: "answers the open question",
            gap: "vs prior",
            consumer: "thm:main",
          },
        })),
      };
      await writeFile(outPath, JSON.stringify(body), "utf8");
      return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("runClaude is not used by D0 solve"); },
    lean: undefined as never,
  };
  return {
    deps,
    dispatches: () => log.map((ids) => [...ids]),
    dispatchedSince: () => new Set(log.flat()),
    resetLog: () => { log = []; },
  };
}
