// Does a dropped edit say WHY?
//
// `statement-replace` is dependency/metadata-only: `kind`, `statement`, and `status` must echo the
// node's current values byte-for-byte. Failing that skips the WHOLE edit, losing the
// dependency rewiring the round intended. Proofs do not belong to this payload because
// apply carries the authoritative proof independently.
//
// These pin the diagnosis, not just the rejection: a check that says "something was
// dropped" is a safety net; one that names the field is a fix.

import { describe, it, expect } from "vitest";
import { describeEchoMismatch } from "../../src/discovery/stages/d0_apply.js";

const node = (over: Record<string, unknown> = {}) => ({
  id: "thm:x", kind: "theorem", statement: "S", status: "proved", proof_tex: "P", ...over,
});

describe("describeEchoMismatch", () => {
  it("accepts a faithful echo", () => {
    expect(describeEchoMismatch(node(), node(), "thm:x")).toBeNull();
  });

  it("names STATUS — the exact failure that cost three rounds", () => {
    // Round 57 sent `to-prove` against a `proved` node; round 58 sent `proved` against a
    // `to-prove` one. Opposite directions, same misunderstanding: the solver bundled a
    // re-proof into a channel that cannot carry one.
    const why = describeEchoMismatch(node({ status: "to-prove" }), node({ status: "proved" }), "thm:x");
    expect(why).toMatch(/status must echo/);
    expect(why).toMatch(/'proved'/);
    expect(why).toMatch(/'to-prove'/);
    expect(why, "must point at the channel that CAN change status").toMatch(/proofs/);
  });

  it("does not compare a legacy proof_tex field that apply will discard", () => {
    expect(
      describeEchoMismatch(node({ proof_tex: "RETRANSCRIBED" }), node({ proof_tex: "CARRIED" }), "thm:x"),
    ).toBeNull();
  });

  it("names STATEMENT and redirects claim changes to their own channel", () => {
    const why = describeEchoMismatch(node({ statement: "NEW CLAIM" }), node(), "thm:x");
    expect(why).toMatch(/statement must echo/);
    expect(why).toMatch(/proposed_statement_changes/);
  });

  it("rejects a kind change in the dependency/metadata-only channel", () => {
    const why = describeEchoMismatch(node({ kind: "openendedquestion" }), node(), "thm:x");
    expect(why).toMatch(/kind must echo/);
    expect(why).toMatch(/dependency\/metadata-only/);
  });

  it("names an id mismatch", () => {
    expect(describeEchoMismatch(node({ id: "thm:other" }), node(), "thm:x")).toMatch(/does not match the edit target/);
  });

  it("keeps statement and status strict when proof text differs too", () => {
    expect(describeEchoMismatch(node({ status: "to-prove", proof_tex: "NEW" }), node({ proof_tex: "OLD" }), "thm:x"))
      .toMatch(/status must echo/);
  });

  it("reports the FIRST divergence rather than a vague summary", () => {
    // Several fields wrong at once still yields one actionable field to fix.
    const why = describeEchoMismatch(
      node({ statement: "NEW", status: "to-prove", proof_tex: "NEW" }),
      node(),
      "thm:x",
    );
    expect(why).toMatch(/statement must echo/);
  });
});

describe("the proof-free contract reaches the real apply", () => {
  it("ignores a legacy retranscribed proof and preserves the current proof", async () => {
    const { applyProposedChanges } = await import("../../src/discovery/stages/d0_apply.js");
    const { saveWorkingState } = await import("../../src/discovery/stages/d0_working.js");
    const { createDStageHarness } = await import("./d_stage_harness.js");

    const proto = {
      qid: "stat_echo", specialization: "v1", cluster: "stat",
      symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
      assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
      definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
      statements: [{
        id: "thm:main", kind: "theorem", statement: "tau is identified",
        depends_on: ["ass:overlap"], status: "proved", proof_tex: "CARRIED PROOF",
        justification: "j", gap: "g", consumer: "c",
      }],
      target_estimand: "tau", bibliography: [{ key: "R1983" }],
    };
    const h = await createDStageHarness({ qid: "stat_echo", specialization: "v1", proto });
    try {
      const edit = {
        kind: "statement-replace", id: "thm:main",
        proposed: {
          id: "thm:main", kind: "theorem", statement: "tau is identified",
          depends_on: ["ass:overlap", "def:env"],
          status: "proved", proof_tex: "RETRANSCRIBED PROOF",
          justification: "j", gap: "g", consumer: "c",
        },
        reason: "declare the envelope dependency", direction: "correct",
      };
      // The apply reads proposals from the working state, not from its arguments — so
      // seed them the way a solve round would, which exercises that read path too.
      await saveWorkingState(h.ctx(), {
        round: 1, solved: {}, resolved_oeqs: {},
        proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [edit], proofs: [] },
      } as never);
      await expect(applyProposedChanges({ ctx: h.ctx() })).resolves.toHaveLength(1);
      const applied = await h.readProto();
      expect(applied.statements[0].depends_on).toEqual(["ass:overlap", "def:env"]);
      expect(applied.statements[0].proof_tex).toBe("CARRIED PROOF");
    } finally {
      await h.dispose();
    }
  }, 30000);
});
