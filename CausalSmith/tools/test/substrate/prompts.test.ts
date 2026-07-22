// CausalSmith/tools/test/substrate/prompts.test.ts
import { describe, it, expect } from "vitest";
import {
  buildCoordinatorPrompt,
  buildFillerPrompt,
  buildReviewerPrompt,
  buildScaffolderPrompt,
} from "../../src/substrate/prompts.js";

describe("substrate prompts", () => {
  it("scaffolder prompt carries role contract + requirement + caps", () => {
    const p = buildScaffolderPrompt({
      slug: "x", requirement: "REQ-BODY", leanDir: "/r/CausalSmith/Substrate/X",
      modulePrefix: "CausalSmith.Substrate.X", planMarkdown: null, lastReport: null,
      lastReview: null, buildRounds: 0, buildCap: 8,
    });
    expect(p).toContain("REQ-BODY");
    expect(p).toContain("CausalSmith.Substrate.X");
    expect(p).toMatch(/sorry/i);
    expect(p).toMatch(/decision/);
    expect(p).toMatch(/codex_prompts/);
    // Refinements: assess ground truth + structured status-ledger plan + verify-before-review.
    expect(p).toMatch(/ground truth|diagnostics/i);
    expect(p).toContain("## Remaining");
    expect(p).toMatch(/zero remaining sorries/i);
    // Integrity rules: no laundering, no vacuous statements, escalate instead.
    expect(p).toMatch(/launder/i);
    expect(p).toMatch(/vacuous/i);
    expect(p).toMatch(/escalate/i);
    expect(p).toMatch(/same temporary tree/i);
    expect(p).toMatch(/Never import a paper\/research module/i);
    // Source-grounding: fetch the primary reference when possible.
    expect(p).toMatch(/fetch/i);
  });

  it("loads scaffolder prompt from the externalized .txt template", () => {
    // The template tokens must all be substituted (no leftover {{...}}).
    const p = buildScaffolderPrompt({
      slug: "x", requirement: "REQ-BODY", leanDir: "/d", modulePrefix: "M",
      planMarkdown: null, lastReport: null, lastReview: null, buildRounds: 0, buildCap: 8,
    });
    expect(p).not.toMatch(/\{\{[A-Z_]+\}\}/);
  });
  it("scaffolder prompt injects the prior round report when present", () => {
    const p = buildScaffolderPrompt({
      slug: "x", requirement: "R", leanDir: "/d", modulePrefix: "M",
      planMarkdown: "PLAN-TEXT",
      lastReport: { round: 1, fillers: [{ id: "p1", ok: false, summary: "stuck on lemma" }],
        build: { ok: false, errors: ["error: boom"], sorryCount: 3, perFile: {} } },
      lastReview: null, buildRounds: 1, buildCap: 8,
    });
    expect(p).toContain("PLAN-TEXT");
    expect(p).toContain("stuck on lemma");
    expect(p).toContain("error: boom");
  });
  it("reviewer prompt lists all six checks", () => {
    const p = buildReviewerPrompt({ requirement: "R", leanDir: "/d", modulePrefix: "M" });
    for (const k of ["generic", "reusable", "standard", "not_vacuous", "fulfills_goal", "sorry_free", "layered"]) {
      expect(p).toContain(k);
    }
  });
  it("filler prompt names the target decls", () => {
    const p = buildFillerPrompt({ leanDir: "/d", modulePrefix: "CausalSmith.Substrate.X", prompt: { id: "p1", target_decls: ["foo_lemma"], prompt: "prove it" } });
    expect(p).toContain("foo_lemma");
    expect(p).toContain("prove it");
    expect(p).toMatch(/BUILD GREEN BEFORE YOU STOP/);
    expect(p).toContain("BUILD_EXIT=0");
    expect(p).toContain("CausalSmith.Substrate.X.*");
    expect(p).toMatch(/helpers from other runs are forbidden/i);
  });
  it("coordinator requires a headline anchor for every theorem-bearing promoted file", () => {
    const p = buildCoordinatorPrompt({
      requirement: "R", leanDir: "/d", modulePrefix: "M",
      leanFiles: ["/d/Main.lean", "/d/Support.lean"], stagingDir: "/stage",
      lastFailureLog: null,
    });
    expect(p).toMatch(/audit EVERY promoted Lean file/i);
    expect(p).toMatch(/every file containing a public `theorem` or `lemma`/i);
    expect(p).toMatch(/single required headline anchor/i);
    expect(p).toMatch(/Preserve every existing sidecar entry/i);
    expect(p).toMatch(/existing top-level subject area/i);
    expect(p).toMatch(/no `CausalSmith` import or qualified reference/i);
    expect(p).not.toMatch(/LAST RESORT/i);
  });
});
