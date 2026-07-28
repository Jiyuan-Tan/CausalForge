import { describe, expect, it } from "vitest";
import { resolveCodexWorkingDirectory } from "../../src/pipeline_support.js";
import { dispatchAgent } from "../../src/framework/agent_dispatch.js";

describe("formalization Codex production-write routing", () => {
  it("keeps reviewers in paper tmp but roots source producers at the requested production cwd", () => {
    const common = {
      requestedCwd: "/repo",
      paperTmp: "/repo/CausalSmith/Stat/Paper/tmp",
      usePaperTmpAsCwd: true,
    };
    expect(resolveCodexWorkingDirectory(common)).toBe(common.paperTmp);
    expect(resolveCodexWorkingDirectory({ ...common, productionWrite: true })).toBe(common.requestedCwd);
  });

  it("forwards the source-producing capability through the logged dispatch boundary", async () => {
    let seen: Record<string, unknown> | undefined;
    await dispatchAgent({
      ctx: { repoRoot: "/tmp/causalsmith-production-write-test", qid: "q", specialization: "s" },
      deps: {
        runCodex: async (input) => {
          seen = input as unknown as Record<string, unknown>;
          return { stdout: "{}", stderr: "" };
        },
      },
      stage: "2",
      label: "test producer",
      prompt: "edit production source",
      promptSources: ["unit-test"],
      model: "test-model",
      reasoningEffort: "medium",
      productionWrite: true,
    });
    expect(seen?.productionWrite).toBe(true);
    expect(seen?.cwd).toBe("/tmp/causalsmith-production-write-test");
  });
});
