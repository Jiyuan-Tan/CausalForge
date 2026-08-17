// The referee web grant. A cold referee is hermetic by default, but the D0.5.G verdict
// grades a note against PUBLISHED work — a judgement that rests on what a named comparator
// actually states, which is not in the note. These tests pin that the grant is opt-in, that
// it reaches the literature WITHOUT reaching the run (filesystem stays denied), and that an
// availability fallback does not silently drop it.
import { describe, expect, it } from "vitest";
import { ClaudeRunError } from "../../../src/workers/claude.js";
import { runReferee } from "../../../src/discovery/framework/referee.js";
import { MODEL_PLAN } from "../../../src/constants.js";
import type { PipelineContext } from "../../../src/types.js";
import type { StageDeps } from "../../../src/pipeline_support.js";

const ctx = {
  repoRoot: "/tmp/causalsmith-referee-web-test",
  qid: "stat_test",
  specialization: "v1",
  dryRun: false,
  resume: false,
} as PipelineContext;

const verdict = JSON.stringify({
  tier: "field",
  salvageable: false,
  flagged_conjecture_labels: [],
  critique: "Meets the field floor on the proved class.",
  flagship_potential: false,
  flagship_directive: "",
});

/** Capture the input dispatchClaudeAgent hands the claude worker. */
function claudeDeps(inputs: Array<Record<string, unknown>>): StageDeps {
  return {
    runClaude: async (input: Record<string, unknown>) => {
      inputs.push(input);
      return verdict;
    },
  } as unknown as StageDeps;
}

describe("runReferee web grant", () => {
  it("stays hermetic by default — an existing claude referee gains nothing", async () => {
    const inputs: Array<Record<string, unknown>> = [];
    await runReferee({
      ctx, deps: claudeDeps(inputs), stage: "0.5", label: "default referee",
      prompt: "review", promptSources: ["inline"], runner: "claude", model: "opus", leanLsp: false,
    });
    expect(inputs[0]).toMatchObject({ webSearch: false, allowedTools: [], allowSubagents: false });
  });

  it("grants the web without granting the run", async () => {
    const inputs: Array<Record<string, unknown>> = [];
    await runReferee({
      ctx, deps: claudeDeps(inputs), stage: "0.5", label: "web referee",
      prompt: "review", promptSources: ["inline"], runner: "claude", model: "opus",
      webSearch: true, leanLsp: false,
    });
    // The whole point of the split: reach the SOURCE, never the run artifacts. Read/Grep/Glob
    // and Task stay denied, so prior reviews and state cannot steer a cold verdict.
    expect(inputs[0]).toMatchObject({
      webSearch: true, allowedTools: [], allowSubagents: false, leanLsp: false,
    });
  });

  it("carries the grant through an availability fallback to codex", async () => {
    // A verdict that NEEDS the literature must not silently become a hermetic one just
    // because the claude process was unavailable.
    const codexInputs: Array<Record<string, unknown>> = [];
    const deps = {
      runClaude: async () => {
        throw new ClaudeRunError(
          "claude failed: exit 1",
          JSON.stringify({ type: "result", is_error: true, api_error_status: 429, result: "limit" }),
          "",
        );
      },
      runCodex: async (input: Record<string, unknown>) => {
        codexInputs.push(input);
        return { stdout: verdict, stderr: "" };
      },
    } as unknown as StageDeps;

    await runReferee({
      ctx, deps, stage: "0.5", label: "fallback referee",
      prompt: "review", promptSources: ["inline"], runner: "claude", model: "opus",
      webSearch: true, leanLsp: false,
      claudeUnavailableFallback: { runner: "codex", model: "gpt-5.6-sol", reasoningEffort: "high" },
    });
    // Codex search is hosted/server-side, so `read-only` does not conflict with it.
    expect(codexInputs[0]).toMatchObject({ webSearch: true, sandboxMode: "read-only" });
  });
});

/** Capture what the codex runner is handed (the default runner for every referee). */
function codexDeps(inputs: Array<Record<string, unknown>>): StageDeps {
  return {
    runCodex: async (input: Record<string, unknown>) => {
      inputs.push(input);
      return { stdout: verdict, stderr: "" };
    },
  } as unknown as StageDeps;
}

describe("runReferee web grant on the codex runner", () => {
  async function run(webSearch?: boolean): Promise<Record<string, unknown>> {
    const inputs: Array<Record<string, unknown>> = [];
    await runReferee({
      ctx, deps: codexDeps(inputs), stage: "0.5", label: "codex referee",
      prompt: "review", promptSources: ["inline"], model: "gpt-5.6-sol",
      reasoningEffort: "high", leanLsp: false,
      ...(webSearch === undefined ? {} : { webSearch }),
    });
    return inputs[0]!;
  }

  it("leaves codex's default-on search alone when the caller says nothing", async () => {
    // Load-bearing: D-0.5's prompt instructs citation verification and relies on this
    // default. Mapping unset to `false` would silently take the web away from it.
    expect(await run()).not.toHaveProperty("webSearch");
  });

  it("forwards an explicit grant, pinning intent against a change of runner or default", async () => {
    expect(await run(true)).toMatchObject({ webSearch: true, reasoningEffort: "high" });
  });

  it("forwards an explicit denial, so a hermetic codex referee is still expressible", async () => {
    expect(await run(false)).toMatchObject({ webSearch: false });
  });
});

describe("D0.5.G runner configuration", () => {
  it("judges on codex at high effort", () => {
    // Reversed from opus on 2026-08-09; see the evidence recorded at the MODEL_PLAN entry.
    // A silent revert would also silently drop `effort`, which the claude path ignores.
    expect(MODEL_PLAN.stage0_5_general).toMatchObject({ runner: "codex", effort: "high" });
  });
});
