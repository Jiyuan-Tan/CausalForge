import { describe, expect, it } from "vitest";
import { checkpointGuidance } from "../../src/checkpoint_playbook.js";
import { D0_5_TRIAGE_MARKER } from "../../src/constants.js";
import { decideTriageKill, formatTriageTier } from "../../src/discovery/stages/d0_5_general.js";
import type { GeneralReviewResult } from "../../src/discovery/stages/d0_5_general.js";

// D0.5.G now runs CONCURRENTLY with the core panel on the first round, so its verdict
// exists while D0.R still has repairs outstanding. `decideTriageKill` is the whole of the
// authority that early read carries: it may end the run only when the referee says the
// note is below the floor AND has no bounded fix — a claim about the kernel, which an
// in-place math repair cannot change. Everything softer stays advisory, because the
// referee is reading a draft whose flagged proofs are still broken and this referee class
// already over-rejects complete work.

const gen = (over: Partial<GeneralReviewResult>): GeneralReviewResult => ({
  tier: "subfield",
  salvageable: false,
  flagged_conjecture_labels: [],
  critique: "kernel is a relabelling of a known result",
  raw: "{}",
  ...over,
});

describe("decideTriageKill", () => {
  it("kills a below-floor note with no bounded fix", () => {
    expect(decideTriageKill(gen({ tier: "subfield", salvageable: false }), "field")).toBe(true);
    expect(decideTriageKill(gen({ tier: "incremental", salvageable: false }), "subfield")).toBe(true);
  });

  it("spares a below-floor note the referee calls salvageable", () => {
    // The loop may yet deliver the named upgrade, and a mid-repair draft reads low.
    expect(decideTriageKill(gen({ tier: "subfield", salvageable: true }), "field")).toBe(false);
  });

  it("never kills a note that meets its floor", () => {
    expect(decideTriageKill(gen({ tier: "field", salvageable: false }), "field")).toBe(false);
    expect(decideTriageKill(gen({ tier: "flagship", salvageable: false }), "field")).toBe(false);
  });

  it("imposes no kill at the bottom floor, where nothing is below it", () => {
    expect(decideTriageKill(gen({ tier: "incremental", salvageable: false }), "incremental")).toBe(false);
  });
});

describe("formatTriageTier", () => {
  // The classifier cut is `message.split(MARKER)[0]`, so ANY text this emits before the
  // marker is handed straight back to the keyword match. That makes "opens with the marker"
  // the single invariant the whole design rests on.
  it("OPENS with the marker, so the playbook's cut hides all of it", () => {
    for (const t of ["subfield", "field", "flagship", "incremental"] as const) {
      const note = formatTriageTier(gen({ tier: t }), "field");
      expect(note.startsWith(D0_5_TRIAGE_MARKER)).toBe(true);
      expect(note.split(D0_5_TRIAGE_MARKER)[0]).toBe("");
    }
  });

  // Both the machine classifier and the agent orchestrator read halt messages. The note
  // must not be mistakable for the halt's own verdict, so it must not speak their tokens:
  // `tier=X ≥ floor=Y` is verbatim the documented PASS signal, and "BELOW NOVELTY FLOOR" is
  // how the skills route a sound-but-under-novel paper to `bank downgraded`.
  it("never emits the verdict tokens the orchestrator routes on", () => {
    for (const t of ["subfield", "field", "flagship", "incremental"] as const) {
      for (const salvageable of [true, false]) {
        const note = formatTriageTier(gen({ tier: t, salvageable }), "field");
        expect(note).not.toMatch(/≥\s*floor/);
        expect(note).not.toMatch(/<\s*floor/);
        expect(note).not.toMatch(/below novelty floor/i);
        expect(note).not.toMatch(/\bpass\b/i);
      }
    }
  });

  it("labels the read as advisory and first-round, so it is not misread as the floor call", () => {
    const note = formatTriageTier(gen({ tier: "subfield", salvageable: true }), "field");
    expect(note).toContain("TRIAGE");
    expect(note).toContain("NOT the verdict");
    expect(note).toContain("under the bar");
  });

  it("stays quiet about re-solving when the note already meets the floor", () => {
    const note = formatTriageTier(gen({ tier: "field" }), "field");
    expect(note).toContain("meets the bar");
    expect(note).not.toContain("stop here again");
  });
});

// The note is appended to halt messages that checkpoint_playbook classifies by KEYWORD.
// It carries `floor=` plus the referee's free-text critique, so leaving it visible to that
// match decides the branch: a cap-exhausted halt (no pass, no floor language of its own)
// matched the PASS branch on the word `floor` alone, and a math `fail` with a below-floor
// triage matched BELOW NOVELTY FLOOR — reporting a novelty problem for a math defect. The
// playbook therefore cuts the message at D0_5_TRIAGE_MARKER before matching.
describe("D0.5 halt classification is not perturbed by the appended triage note", () => {
  const guide = (verdict: string, tier: GeneralTierCase) =>
    checkpointGuidance("0.5", "checkpoint", {}, false, verdict + formatTriageTier(gen(tier), "field"))!;
  type GeneralTierCase = Partial<GeneralReviewResult>;

  const CAP_EXHAUSTED =
    "Stage 0.5 (typed) revise cap exhausted (3 rounds, CARRIED across resumes) without PASS — " +
    "likely a genuine open gap. Provide guidance via the D0 directive and re-run, or rewind D0/D-1.2.";
  const FAIL =
    "Stage 0.5 (typed) FAIL on round 0 — the math note has a defect the directed revise cannot fix " +
    "in place. Findings: bad step.";
  const NON_CONVERGING =
    "Stage 0.5 (typed) non-converging — finding(s) survived a D0.R edit and are still flagged on round 1.";

  it("does not read a cap-exhausted halt as a PASS when the triage met the floor", () => {
    expect(guide(CAP_EXHAUSTED, { tier: "field" })).not.toContain("D0.5 PASS");
  });

  it("does not read a math FAIL as a novelty-floor problem when the triage was below floor", () => {
    const g = guide(FAIL, { tier: "subfield" });
    expect(g).not.toContain("BELOW NOVELTY FLOOR");
    expect(g).not.toContain("D0.5 PASS");
  });

  it("is not fooled by referee prose containing 'cleared'", () => {
    const critique = "the kernel has not cleared the bar";
    expect(guide(CAP_EXHAUSTED, { tier: "field", critique })).not.toContain("D0.5 PASS");
  });

  it("still classifies the verdicts the message itself states", () => {
    expect(guide(NON_CONVERGING, { tier: "field" })).toContain("NON-CONVERGING");
    // The triage KILL states its own below-floor verdict, so it must still route there.
    const kill = "Stage 0.5 (typed) BELOW NOVELTY FLOOR (triage, round 0) — D0.5.G tier=subfield < floor=field";
    expect(checkpointGuidance("0.5", "checkpoint", {}, false, kill)).toContain("BELOW NOVELTY FLOOR");
  });
});
