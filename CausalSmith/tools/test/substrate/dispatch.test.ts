// CausalSmith/tools/test/substrate/dispatch.test.ts
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { runScaffolder } from "../../src/substrate/scaffolder.js";
import { runFillers } from "../../src/substrate/filler.js";
import { runReviewer } from "../../src/substrate/reviewer.js";

let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "subdisp-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("substrate dispatchers (with fakes)", () => {
  it("runScaffolder uses the kernel Codex model and parses its JSON", async () => {
    let received: { model?: string; reasoningEffort?: string } | undefined;
    const fakeCodex = async (input: { model?: string; reasoningEffort?: string }) => {
      received = input;
      return { stdout: JSON.stringify({
        decision: "build", plan_markdown: "p",
        codex_prompts: [{ id: "a", target_decls: ["x"], prompt: "prove x" }],
      }), stderr: "" };
    };
    const out = await runScaffolder(
      { repoRoot: root, runDir: root, slug: "x", requirement: "R", leanDir: "/d", modulePrefix: "M",
        planMarkdown: null, lastReport: null, lastReview: null, buildRounds: 0, buildCap: 8 },
      { runCodex: fakeCodex as any },
    );
    expect(out.decision).toBe("build");
    expect(out.codex_prompts[0].id).toBe("a");
    expect(received).toMatchObject({ model: "gpt-5.6-sol", reasoningEffort: "high" });
  });

  it("runFillers maps one report per prompt and marks failures", async () => {
    const received: Array<{ model?: string; reasoningEffort?: string }> = [];
    const fakeCodex = async ({ prompt, ...input }: { prompt: string; model?: string; reasoningEffort?: string }) => {
      received.push(input);
      return prompt.includes("BOOM")
        ? Promise.reject(new Error("codex died"))
        : { stdout: "closed x", stderr: "" };
    };
    const reports = await runFillers(
      { repoRoot: root, runDir: root, round: 1, leanDir: "/d", modulePrefix: "CausalSmith.Substrate.X", concurrency: 2,
        prompts: [{ id: "ok", target_decls: [], prompt: "fine" }, { id: "bad", target_decls: [], prompt: "BOOM" }] },
      { runCodex: fakeCodex as any },
    );
    expect(reports).toHaveLength(2);
    expect(reports.find((r) => r.id === "ok")!.ok).toBe(true);
    expect(reports.find((r) => r.id === "bad")!.ok).toBe(false);
    expect(received).toHaveLength(2);
    for (const input of received) {
      expect(input).toMatchObject({ model: "gpt-5.6-sol", reasoningEffort: "medium" });
    }
  });

  it("runReviewer parses codex verdict JSON", async () => {
    const fakeCodex = async () => ({ stdout: JSON.stringify({
      pass: true, findings: "good",
      checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true },
    }), stderr: "" });
    const v = await runReviewer(
      { repoRoot: root, runDir: root, round: 1, slug: "x", requirement: "R", leanDir: "/d", modulePrefix: "M" },
      { runCodex: fakeCodex as any },
    );
    expect(v.pass).toBe(true);
  });
});
