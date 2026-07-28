import { describe, expect, it } from "vitest";
import { resolveLiveFillerDirective } from "../../src/formalization/proof_review_loop.js";
import type { StateJson } from "../../src/types.js";

function stateWithDirective(value: string | null): StateJson {
  return {
    stage_completed: "2",
    lean_subdir: "CausalSmith/Stat/Test",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { f3_filler_directive: value },
  } as unknown as StateJson;
}

const ctx = { repoRoot: "/repo", qid: "q", specialization: "s" };

describe("resolveLiveFillerDirective", () => {
  it("observes an external clear and synchronizes the shared process state", async () => {
    const shared = stateWithDirective("stale projection hint");
    const durable = stateWithDirective(null);

    const result = await resolveLiveFillerDirective(
      ctx,
      shared,
      "stale projection hint",
      async () => durable,
    );

    expect(result).toBeNull();
    expect(shared.flags.f3_filler_directive).toBeNull();
  });

  it("observes an external update and synchronizes the shared process state", async () => {
    const shared = stateWithDirective(null);
    const durable = stateWithDirective("new reusable lemma hint");

    const result = await resolveLiveFillerDirective(ctx, shared, null, async () => durable);

    expect(result).toBe("new reusable lemma hint");
    expect(shared.flags.f3_filler_directive).toBe("new reusable lemma hint");
  });

  it("falls back to the startup value when no durable state exists", async () => {
    const result = await resolveLiveFillerDirective(
      ctx,
      undefined,
      "standalone hint",
      async () => { throw new Error("no state"); },
    );

    expect(result).toBe("standalone hint");
  });
});
