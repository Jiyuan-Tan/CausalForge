import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { dispatchAgent, parseAgentJson, dispatchClaudeAgent } from "../../../src/framework/agent_dispatch.js";
import { pipelineLogPath } from "../../../src/paths.js";
import type { PipelineContext } from "../../../src/types.js";
import type { StageDeps } from "../../../src/pipeline_support.js";

let tmp: string;
let ctx: PipelineContext;

beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "dispatch-test-"));
  ctx = { repoRoot: tmp, qid: "stat_demo", specialization: "econometrics", dryRun: false, resume: false } as PipelineContext;
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("dispatchAgent", () => {
  it("logs resolved prompt size+sources before the call and stdout size after", async () => {
    const deps = {
      runCodex: async () => ({ stdout: '{"ok":true}', stderr: "" }),
    } as unknown as StageDeps;
    const out = await dispatchAgent({
      ctx,
      deps,
      stage: "-1.1",
      label: "lit-review",
      prompt: "PROMPT BODY",
      promptSources: ["prompts/D-1/stage_neg1_1_lit_review.txt"],
      model: "gpt-5.6-terra",
      reasoningEffort: "high",
    });
    expect(out.stdout).toBe('{"ok":true}');
    const log = await readFile(pipelineLogPath(tmp, "stat_demo", "econometrics"), "utf8");
    const lines = log
      .trim()
      .split("\n")
      .map((l) => JSON.parse(l));
    const dispatch = lines.find((l) => l.status === "dispatch");
    const complete = lines.find((l) => l.status === "dispatch-complete");
    expect(dispatch.message).toContain("lit-review");
    expect(dispatch.message).toContain(`${Buffer.byteLength("PROMPT BODY", "utf8")} bytes`);
    expect(dispatch.message).toContain("stage_neg1_1_lit_review.txt");
    expect(complete.message).toContain(`${Buffer.byteLength('{"ok":true}', "utf8")} bytes`);
  });

  it("refuses an empty prompt — the fail-open-to-empty-prompt class, made structural", async () => {
    const deps = { runCodex: async () => ({ stdout: "", stderr: "" }) } as unknown as StageDeps;
    await expect(
      dispatchAgent({
        ctx,
        deps,
        stage: "-1.1",
        label: "x",
        prompt: "  \n",
        promptSources: ["p"],
        model: "m",
        reasoningEffort: "high",
      }),
    ).rejects.toThrow(/empty prompt/i);
  });

  it("forwards multiAgent to runCodex when set, omits it when not", async () => {
    const calls: Array<Record<string, unknown>> = [];
    const deps = {
      runCodex: async (input: Record<string, unknown>) => {
        calls.push(input);
        return { stdout: "{}", stderr: "" };
      },
    };
    const base = {
      ctx, // reuse the test file's existing tmp ctx fixture
      deps: deps as never,
      stage: "2.5" as const,
      label: "t",
      prompt: "p",
      promptSources: ["s"],
      model: "m",
      reasoningEffort: "medium" as const,
    };
    await dispatchAgent({ ...base, multiAgent: false });
    expect(calls[0].multiAgent).toBe(false);
    await dispatchAgent(base);
    expect("multiAgent" in calls[1]).toBe(false);
  });
});

describe("dispatchClaudeAgent", () => {
  it("dispatchClaudeAgent refuses an empty prompt and logs a dispatch pair", async () => {
    const calls: Array<Record<string, unknown>> = [];
    const deps = {
      runClaude: (async (input: Record<string, unknown>) => {
        calls.push(input);
        return "ok";
      }) as never,
    };
    const input = { prompt: "hello", model: "opus", cwd: ctx.repoRoot } as never;
    await expect(
      dispatchClaudeAgent({ ctx, deps, stage: "1", label: "claude-dispatch-t", promptSources: ["src-claude.txt"], input: { ...(input as object), prompt: "  " } as never }),
    ).rejects.toThrow(/EMPTY prompt/);
    const out = await dispatchClaudeAgent({ ctx, deps, stage: "1", label: "claude-dispatch-t", promptSources: ["src-claude.txt"], input });
    expect(out).toBe("ok");
    expect(calls[0].prompt).toBe("hello");
    const log = await readFile(pipelineLogPath(tmp, "stat_demo", "econometrics"), "utf8");
    const lines = log
      .trim()
      .split("\n")
      .map((l) => JSON.parse(l));
    const dispatch = lines.find((l) => l.status === "dispatch");
    const complete = lines.find((l) => l.status === "dispatch-complete");
    expect(dispatch.message).toContain("claude-dispatch-t: prompt ");
    expect(dispatch.message).toContain(`${Buffer.byteLength("hello", "utf8")} bytes`);
    expect(dispatch.message).toContain("from [src-claude.txt]");
    expect(dispatch.model).toBe("opus");
    expect(complete.message).toContain(`${Buffer.byteLength("ok", "utf8")} bytes`);
    expect(complete.model).toBe("opus");
  });
});

describe("parseAgentJson", () => {
  it("returns the parsed object on success", () => {
    const r = parseAgentJson('noise\n{"a": 1}\n');
    expect(r.json).toEqual({ a: 1 });
  });
  it("returns parseError (never throws) on garbage", () => {
    const r = parseAgentJson("no json here at all");
    expect(r.json).toBeUndefined();
    expect(typeof r.parseError).toBe("string");
  });
});
