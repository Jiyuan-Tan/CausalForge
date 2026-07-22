import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, cp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runPipeline } from "../../src/pipeline.js";
import { createInitialState, saveState } from "../../src/state.js";
import { claimOpenQuestionForRun } from "../../src/shared/claim_open_question.js";
import {
  closeOpenQuestion,
} from "../../src/shared/close_open_question.js";
import { parseArgs } from "../../src/cli.js";
import { pipelineLogPath, statePath } from "../../src/paths.js";
import type { PipelineContext } from "../../src/types.js";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURE_DIR = path.resolve(HERE, "..", "fixtures", "fixtures_phase3");

let repoRoot: string;

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "phase3-smoke-"));
  await writeFile(
    path.join(repoRoot, "lakefile.toml"),
    'name = "CausalSmith"\n',
  );
  // Stage the graph under doc/study/ inside the synthetic repo root.
  await mkdir(path.join(repoRoot, "doc", "study"), { recursive: true });
  await cp(FIXTURE_DIR, path.join(repoRoot, "doc", "study"), { recursive: true });
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

const OQ_ID = "oq_two-step-control-function_panel-extension";

describe("/causalsmith --from-question CLI parsing", () => {
  it("parses the flag and exposes fromQuestionOqId", () => {
    const parsed = parseArgs(["--from-question", "oq_abc", "panel_test_qid", "spec1"]);
    expect(parsed.fromQuestionOqId).toBe("oq_abc");
    expect(parsed.qid).toBe("panel_test_qid");
    expect(parsed.specialization).toBe("spec1");
  });
  it("rejects --from-question + --propose", () => {
    expect(() =>
      parseArgs(["--from-question", "oq_x", "--propose", "T", "q", "s"]),
    ).toThrow(/mutually exclusive/);
  });
});

describe("/causalsmith --from-question atomic OQ claim", () => {
  it("flips OQ status open → in_progress under graph lock", async () => {
    const oqPath = path.join(repoRoot, "doc", "study", "nodes", "open_question", `${OQ_ID}.json`);
    const before = JSON.parse(await readFile(oqPath, "utf8"));
    expect(before.status).toBe("open");

    const claim = await claimOpenQuestionForRun({ repoRoot, oq_id: OQ_ID });
    expect(claim.method_id).toBe("iv");

    const after = JSON.parse(await readFile(oqPath, "utf8"));
    expect(after.status).toBe("in_progress");
  });

  it("rejects a second claim on the same OQ", async () => {
    await claimOpenQuestionForRun({ repoRoot, oq_id: OQ_ID });
    await expect(
      claimOpenQuestionForRun({ repoRoot, oq_id: OQ_ID }),
    ).rejects.toMatchObject({ name: "OpenQuestionClaimError" });
  });
});

describe("/causalsmith --from-question --dry-run pipeline integration", () => {
  it("runs the pipeline end-to-end and logs the dry-run close-hook", async () => {
    // Claim the OQ (mirrors what runCli does).
    await claimOpenQuestionForRun({ repoRoot, oq_id: OQ_ID });

    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_iv_basic",
      specialization: "default",
      resume: false,
      dryRun: true,
      fromQuestionOqId: OQ_ID,
    };
    const state = await runPipeline(ctx);
    expect(state.stage_completed).toBe("5");
    expect(state.from_question_oq_id).toBe(OQ_ID);

    // Confirm the dry-run skip log line landed on the pipeline jsonl.
    const logPath = pipelineLogPath(repoRoot, "panel_iv_basic", "default");
    const log = await readFile(logPath, "utf8");
    expect(log).toMatch(/\[dry-run\] would close OpenQuestion/);
    expect(log).toContain(OQ_ID);
  });
});

describe("/causalsmith --from-question post-Stage-5 live close (simulated)", () => {
  it("after Stage 5 the OQ flips to closed_by:<bt_id> and BankedTheorem exists", async () => {
    // Simulate the post-Stage-5 close: the pipeline-driven path is exercised
    // by the dry-run test above; this one verifies the real (non-dry-run)
    // close logic against the same fixture so the graph mutation + index
    // rebuild are validated end-to-end.
    await claimOpenQuestionForRun({ repoRoot, oq_id: OQ_ID });

    const result = await closeOpenQuestion(
      {
        qid: "panel_iv_basic",
        spec: "default",
        oq_id: OQ_ID,
        bankMetadata: { instantiates: ["iv"], uses: ["strict-exogeneity"] },
      },
      { graphRoot: path.join(repoRoot, "doc", "study") },
    );
    expect(result.bt_id).toBe("panel_iv_basic_default");

    const oq = JSON.parse(
      await readFile(
        path.join(repoRoot, "doc", "study", "nodes", "open_question", `${OQ_ID}.json`),
        "utf8",
      ),
    );
    expect(oq.status).toEqual({ closed_by: result.bt_id });

    const idx = JSON.parse(
      await readFile(path.join(repoRoot, "doc", "study", "index.json"), "utf8"),
    ) as { forward: Record<string, Record<string, string[]>>; reverse: Record<string, Record<string, string[]>> };
    expect(idx.forward[result.bt_id]?.closes).toContain(OQ_ID);
    expect(idx.reverse[OQ_ID]?.closes).toContain(result.bt_id);
  });
});

describe("Stage -1.2 prompt splice: OPEN_QUESTION_CONTEXT block", () => {
  it("renders the bundle Markdown when state.from_question_oq_id is set", async () => {
    // Direct invocation of resolveOpenQuestion + renderOpenQuestionContext
    // (the same code path Stage -1.2 calls). The Stage -1.2 driver is gated
    // by --propose; this verifies the inline splice produces the expected
    // headers and node ids when called against our synthetic graph.
    const { resolveOpenQuestion, renderOpenQuestionContext } = await import(
      "../../src/shared/resolve_open_question.js"
    );
    const bundle = await resolveOpenQuestion(OQ_ID, {
      graphRoot: path.join(repoRoot, "doc", "study"),
    });
    const block = renderOpenQuestionContext(bundle);
    expect(block).toContain("## Target OpenQuestion");
    expect(block).toContain(OQ_ID);
    expect(block).toContain("Instrumental Variables");
    expect(block).toContain("panel_iv_v1");
  });
});

describe("--from-question initializer wires from_question_oq_id onto state", () => {
  it("createInitialState defaults are null; pipeline writes the oq_id on cold start", async () => {
    const init = createInitialState("panel_iv_basic");
    expect(init.from_question_oq_id).toBeNull();
    // Simulate cold-start save with the field set.
    init.from_question_oq_id = OQ_ID;
    await saveState(repoRoot, "panel_iv_basic", "default", init);
    const reloaded = JSON.parse(
      await readFile(statePath(repoRoot, "panel_iv_basic", "default"), "utf8"),
    );
    expect(reloaded.from_question_oq_id).toBe(OQ_ID);
  });
});
