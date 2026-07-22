import { describe, expect, it } from "vitest";

import { copyVerifiedCitedSourcesToPlan } from "../../src/formalization/stage1.js";
import type { Core } from "../../src/discovery/core/schema.js";

function coreWithSource(source: Record<string, unknown>, proof_tex?: string): Core {
  return {
    statements: [{
      id: "lem:external",
      kind: "lemma",
      statement: "external theorem",
      depends_on: [],
      status: "cited",
      source,
      ...(proof_tex ? { proof_tex } : {}),
    }],
  } as unknown as Core;
}

describe("F1 cited source-of-record carry-forward", () => {
  it("copies the D0.5-verified source instead of trusting planner prose", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{
        id: "cite:external",
        locator: "wrong locator",
        verbatim_statement: "planner reconstruction",
      }],
    };
    const count = copyVerifiedCitedSourcesToPlan(plan, coreWithSource({
      cite: "Paper2026",
      locator: "Theorem 3.1",
      verbatim_statement: "Exact theorem with hypothesis H.",
      doi: "10.1/example",
      attestation: { by: "user", note: "page supplied by user" },
    }));
    expect(count).toBe(1);
    expect(plan.citations[0]).toMatchObject({
      locator: "Theorem 3.1",
      verbatim_statement: "Exact theorem with hypothesis H.",
      doi: "10.1/example",
      attestation: { by: "user", note: "page supplied by user" },
    });
  });

  it("migrates a legacy cited transcription from proof_tex", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{ id: "cite:external" }],
    };
    copyVerifiedCitedSourcesToPlan(
      plan,
      coreWithSource({ cite: "Paper2026", locator: "Lemma 2" }, "Legacy exact transcription."),
    );
    expect(plan.citations[0]).toMatchObject({
      locator: "Lemma 2",
      verbatim_statement: "Legacy exact transcription.",
    });
  });
});
