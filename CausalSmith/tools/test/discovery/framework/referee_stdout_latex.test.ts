import { readFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";
import { ClaudeRunError } from "../../../src/workers/claude.js";
import { runReferee } from "../../../src/discovery/framework/referee.js";
import { generalReviewPayloadValidationError } from "../../../src/discovery/stages/d0_5_general.js";
import { pipelineLogPath } from "../../../src/paths.js";
import type { PipelineContext } from "../../../src/types.js";
import type { StageDeps } from "../../../src/pipeline_support.js";

const ctx = {
  repoRoot: "/tmp/causalsmith-referee-test",
  qid: "stat_test",
  specialization: "v1",
  dryRun: false,
  resume: false,
} as PipelineContext;

describe("stdout referee LaTeX JSON boundary", () => {
  it("repairs the round-60 invalid-backslash shape while preserving raw stdout", async () => {
    // Production round 60 failed on the critique's single-backslash inline TeX:
    // `\(d/\epsilon\)` (the first `\(` is an invalid JSON escape).
    const raw = String.raw`{
      "tier":"subfield",
      "salvageable":true,
      "improvement_directive":"Prove the missing comparison.",
      "flagged_conjecture_labels":["clean-temperature-feature-upper"],
      "critique":"The pointwise local \(d/\epsilon\) lower bound remains narrow.",
      "flagship_potential":false,
      "flagship_directive":""
    }`;
    const deps = {
      runCodex: async () => ({ stdout: raw, stderr: "" }),
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G regression",
      prompt: "review this note",
      promptSources: ["inline test"],
      model: "test",
      reasoningEffort: "high",
      leanLsp: false,
      validate: generalReviewPayloadValidationError,
    });

    expect(result.parseError).toBeNull();
    expect(result.raw).toBe(raw);
    expect(result.json.critique).toBe(String.raw`The pointwise local \(d/\epsilon\) lower bound remains narrow.`);
  });

  it("does not accept a repaired but structurally invalid general review", async () => {
    const raw = String.raw`{"tier":"field","critique":"Uses \(d/\epsilon\)."}`;
    const deps = {
      runCodex: async () => ({ stdout: raw, stderr: "" }),
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G invalid regression",
      prompt: "review this note",
      promptSources: ["inline test"],
      model: "test",
      reasoningEffort: "high",
      validate: generalReviewPayloadValidationError,
    });

    expect(result.json.critique).toBe(String.raw`Uses \(d/\epsilon\).`);
    expect(result.parseError).toMatch(/strict schema validation/);
  });

  // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general).
  // Two properties the swap must preserve: the verdict contract is runner-independent
  // (same parse, same LaTeX repair, same validate), and the judge that actually ran is
  // the one configured — a silent fallback to codex would swap the referee back with
  // nothing in the log to show it.
  it("routes runner='claude' through runClaude and parses the same verdict contract", async () => {
    const raw = String.raw`{
      "tier":"subfield",
      "salvageable":true,
      "improvement_directive":"Compute the frontier for one nondegenerate menu.",
      "flagged_conjecture_labels":["collision-geometry-sandwich"],
      "critique":"The sandwich is loose by \(\Theta(\sqrt n)\) at the no-interference calibration.",
      "flagship_potential":false,
      "flagship_directive":""
    }`;
    let codexCalls = 0;
    const claudeCalls: Array<{ model: string; allowedTools?: string[] }> = [];
    const deps = {
      runCodex: async () => {
        codexCalls += 1;
        return { stdout: "{}", stderr: "" };
      },
      runClaude: async (input: { model: string; allowedTools?: string[] }) => {
        claudeCalls.push(input);
        return raw;
      },
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G claude runner",
      prompt: "review this note",
      promptSources: ["inline test"],
      runner: "claude",
      model: "opus",
      leanLsp: false,
      validate: generalReviewPayloadValidationError,
    });

    expect(codexCalls).toBe(0);
    expect(claudeCalls).toHaveLength(1);
    expect(claudeCalls[0].model).toBe("opus");
    // Zero tools: the note is inline, and a rubric-free referee must not be able to
    // go read the flagship rubric off disk.
    expect(claudeCalls[0].allowedTools).toEqual([]);
    expect(result.parseError).toBeNull();
    expect(result.json.tier).toBe("subfield");
    expect(result.json.critique).toBe(
      String.raw`The sandwich is loose by \(\Theta(\sqrt n)\) at the no-interference calibration.`,
    );
  });

  it("fails mechanically rather than falling back to codex when no claude runner is configured", async () => {
    const deps = { runCodex: async () => ({ stdout: "{}", stderr: "" }) } as unknown as StageDeps;
    await expect(
      runReferee({
        ctx,
        deps,
        stage: "0.5",
        label: "D0.5.G missing runner",
        prompt: "review this note",
        promptSources: ["inline test"],
        runner: "claude",
        model: "opus",
      }),
    ).rejects.toThrow(/no claude runner is configured/);
  });

  it("falls back visibly to codex when the configured Claude process is unavailable", async () => {
    const raw = JSON.stringify({
      tier: "field",
      salvageable: false,
      improvement_directive: "",
      flagged_conjecture_labels: [],
      critique: "The delivered theorem meets the field floor on its proved finite design class.",
      flagship_potential: false,
      flagship_directive: "",
    });
    let codexCalls = 0;
    const codexInputs: Array<Record<string, unknown>> = [];
    const deps = {
      runClaude: async () => {
        const outageStream = [
          JSON.stringify({ type: "system", subtype: "init", tools: [], mcp_servers: [] }),
          JSON.stringify({ type: "rate_limit_event", rate_limit_info: { status: "rejected" } }),
          JSON.stringify({
            type: "assistant", is_api_error_message: true, error: "rate_limit",
            message: { model: "<synthetic>", content: [{ type: "text", text: "You've hit your session limit" }] },
          }),
          JSON.stringify({
            type: "result", is_error: true, terminal_reason: "api_error",
            api_error_status: 429, result: "You've hit your session limit",
          }),
        ].join("\n");
        throw new ClaudeRunError("claude failed: exit 1", outageStream, "");
      },
      runCodex: async (input: Record<string, unknown>) => {
        codexCalls += 1;
        codexInputs.push(input);
        return { stdout: raw, stderr: "" };
      },
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G unavailable runner",
      prompt: "review this note",
      promptSources: ["inline test"],
      runner: "claude",
      model: "opus",
      claudeUnavailableFallback: {
        runner: "codex",
        model: "gpt-5.6-sol",
        reasoningEffort: "high",
      },
      leanLsp: false,
      validate: generalReviewPayloadValidationError,
    });

    expect(codexCalls).toBe(1);
    expect(result.parseError).toBeNull();
    expect(result.json.tier).toBe("field");
    expect(result.provenance).toMatchObject({
      requested_runner: "claude", actual_runner: "codex",
      fallback_kind: "rate-limit", quorum: 1,
    });
    expect(codexInputs).toHaveLength(1);
    expect(codexInputs[0]).toMatchObject({
      model: "gpt-5.6-sol", reasoningEffort: "high", leanLsp: false,
      multiAgent: false, webSearch: false, sandboxMode: "read-only",
      ignoreUserConfig: true,
    });
    expect(String(codexInputs[0]!.prompt)).toContain("The prompt is the world");
    const log = await readFile(pipelineLogPath(ctx.repoRoot, ctx.qid, ctx.specialization), "utf8");
    const lines = log.trim().split("\n").map((line) => JSON.parse(line));
    const fallback = lines.find((line) => line.status === "dispatch-fallback");
    expect(fallback.message).toContain("Claude unavailable");
    expect(fallback.message).toContain("gpt-5.6-sol/high");
  });

  it("does not replace a completed but malformed Claude verdict with codex", async () => {
    let codexCalls = 0;
    const deps = {
      runClaude: async () => "not valid JSON",
      runCodex: async () => {
        codexCalls += 1;
        return { stdout: "{}", stderr: "" };
      },
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G malformed runner",
      prompt: "review this note",
      promptSources: ["inline test"],
      runner: "claude",
      model: "opus",
      claudeUnavailableFallback: {
        runner: "codex",
        model: "gpt-5.6-sol",
        reasoningEffort: "high",
      },
    });

    expect(codexCalls).toBe(0);
    expect(result.parseError).toBeTruthy();
  });

  it("fails closed on a non-availability Claude error and on a partial assistant response", async () => {
    for (const error of [
      new ClaudeRunError("claude failed: invalid model", "", "invalid model name"),
      new ClaudeRunError(
        "claude failed after response: rate limit",
        JSON.stringify({ type: "assistant", message: { content: [{ type: "text", text: "reject" }] } }),
        "rate limit",
      ),
    ]) {
      let codexCalls = 0;
      const deps = {
        runClaude: async () => { throw error; },
        runCodex: async () => { codexCalls += 1; return { stdout: "{}", stderr: "" }; },
      } as unknown as StageDeps;
      await expect(runReferee({
        ctx, deps, stage: "0.5", label: "D0.5.G fail closed",
        prompt: "review", promptSources: ["inline"], runner: "claude", model: "opus",
        claudeUnavailableFallback: {
          runner: "codex", model: "gpt-5.6-sol", reasoningEffort: "high",
        },
      })).rejects.toBe(error);
      expect(codexCalls).toBe(0);
    }
  });

  it("uses one valid Codex fallback review", async () => {
    let codexCalls = 0;
    const deps = {
      runClaude: async () => {
        throw new ClaudeRunError("claude failed", "", "api_error_status:429 rate_limit_event");
      },
      runCodex: async () => {
        codexCalls += 1;
        return { stdout: JSON.stringify({
        tier: "field", salvageable: true, improvement_directive: "bounded repair",
        flagged_conjecture_labels: [], critique: "independent fallback review",
        flagship_potential: false, flagship_directive: "",
      }), stderr: "" };
      },
    } as unknown as StageDeps;
    const result = await runReferee({
      ctx, deps, stage: "0.5", label: "D0.5.G single fallback",
      prompt: "review", promptSources: ["inline"], runner: "claude", model: "opus",
      claudeUnavailableFallback: {
        runner: "codex", model: "gpt-5.6-sol", reasoningEffort: "high",
      },
      validate: generalReviewPayloadValidationError,
    });
    expect(result.json.tier).toBe("field");
    expect(codexCalls).toBe(1);
  });
});
