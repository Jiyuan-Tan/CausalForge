import { describe, expect, it } from "vitest";
import { runReferee } from "../../../src/discovery/framework/referee.js";
import { generalReviewPayloadValidationError } from "../../../src/discovery/stages/d0_5_general.js";
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
});
