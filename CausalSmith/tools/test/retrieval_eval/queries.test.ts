import { describe, it, expect } from "vitest";
import { renderDocQueries } from "../../src/formalization/retrieval_eval/queries.js";

describe("renderDocQueries", () => {
  it("emits a doc query per pair with non-empty doc, qid = theorem#doc#0", () => {
    const pairs = [
      { theorem: "Causalean.A", cluster: "stat", gold: ["X"], doc: "Positivity holds.", statement: "" },
      { theorem: "Causalean.B", cluster: "stat", gold: ["Y"], doc: "", statement: "" },
    ] as any;
    const qs = renderDocQueries(pairs);
    expect(qs).toHaveLength(1);
    expect(qs[0]).toMatchObject({ qid: "Causalean.A#doc#0", rendering: "doc", text: "Positivity holds." });
  });
});
