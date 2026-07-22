import { describe, it, expect } from "vitest";
import { buildReviewPacket, REVIEW_PACKET_CONTRACT } from "../../src/discovery/review_packet.js";
import { readFileSync } from "node:fs";
import { CoreSchema, type Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

// The same golden proposal core `render_tex.test.ts` uses — the packet embeds a real
// rendered document, so a hand-rolled stub only proves the stub renders.
const core: Core = CoreSchema.parse(
  JSON.parse(readFileSync(new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url), "utf8")),
);
const working = { round: 1, solved: {} } as WorkingState;

const base = {
  core,
  working,
  proposedStatementChanges: [],
  proposedDefinitionChanges: [],
  proposedAssumptions: [],
  proposedCoreEdits: [],
  provisionalProofs: [],
};

describe("buildReviewPacket", () => {
  it("ships the same contract on the normal and the recovery path", () => {
    // These were hand-authored separately and DRIFTED: the recovery packet carried an
    // OEQ instruction the normal packet lacked, so the path taken every round shipped
    // weaker guidance than the one taken almost never.
    const normal = buildReviewPacket(base);
    const recovered = buildReviewPacket({ ...base, recovery: { mode: "mechanical-no-solver" } });
    expect(normal.contract).toBe(recovered.contract);
    expect(normal.contract).toBe(REVIEW_PACKET_CONTRACT);
  });

  it("retains the OEQ guidance that only the recovery copy used to carry", () => {
    expect(REVIEW_PACKET_CONTRACT).toMatch(/never discharge an OEQ/);
  });

  it("keeps the durable-working-state guidance both copies agreed on", () => {
    expect(REVIEW_PACKET_CONTRACT).toMatch(/not treated as dropped/);
  });

  it("omits the recovery block entirely on the normal path", () => {
    // Its presence is how a reader tells a mechanically rebuilt packet from a solved one.
    expect("recovery" in buildReviewPacket(base)).toBe(false);
  });

  it("includes the recovery block when provided", () => {
    const p = buildReviewPacket({ ...base, recovery: { mode: "mechanical-no-solver" } });
    expect(p.recovery).toEqual({ mode: "mechanical-no-solver" });
  });

  it("carries every payload channel the adjudicator reads", () => {
    const p = buildReviewPacket({
      ...base,
      proposedStatementChanges: [{ id: "thm:a" }],
      provisionalProofs: [{ id: "lem:b", proof_tex: "P" }],
    });
    for (const key of [
      "full_current_paper_tex",
      "current_typed_core",
      "durable_working_state",
      "proposed_statement_changes",
      "proposed_definition_changes",
      "proposed_assumptions",
      "proposed_core_edits",
      "provisional_proofs",
    ]) {
      expect(p, `missing ${key}`).toHaveProperty(key);
    }
    expect(p.proposed_statement_changes).toEqual([{ id: "thm:a" }]);
    expect(p.provisional_proofs).toEqual([{ id: "lem:b", proof_tex: "P" }]);
  });
});
