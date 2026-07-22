import { describe, it, expect } from "vitest";
import { checkProseConsistency } from "../src/discovery/core/prose_consistency.js";
import type { Core } from "../src/discovery/core/schema.js";

type Stmt = Core["statements"][number];

function stmt(id: string, kind: Stmt["kind"], statement: string, status: Stmt["status"] = "to-prove"): Stmt {
  return { id, kind, statement, status, depends_on: [] } as Stmt;
}

function core(overrides: Partial<Core>): Core {
  return {
    qid: "q",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [],
    target_estimand: "τ",
    bibliography: [],
    ...overrides,
  } as unknown as Core;
}

describe("checkProseConsistency", () => {
  it("flags a dangling statement-label reference in prose (renamed by a reframe)", () => {
    const c = core({
      statements: [stmt("thm:barrier", "theorem", "no two-point route reaches the branch")],
      tldr: "We establish thm:barrier and settle oeq:old-frontier.",
    });
    const w = checkProseConsistency(c);
    const dangling = w.filter((x) => x.code === "PROSE-DANGLING-REF");
    expect(dangling.map((x) => x.message).join(" ")).toContain("oeq:old-frontier");
    // thm:barrier resolves, so it must NOT be flagged.
    expect(dangling.map((x) => x.message).join(" ")).not.toContain("thm:barrier");
  });

  it("flags prose that claims to establish an OPEN-only target term", () => {
    const c = core({
      statements: [
        stmt("thm:barrier", "theorem", "a proof-method obstruction on the two-point route"),
        stmt("oeq:frontier", "openendedquestion", "the sharp minimax frontier for the class"),
      ],
      tldr: "We determine the sharp frontier for the class.",
    });
    const w = checkProseConsistency(c);
    const over = w.filter((x) => x.code === "PROSE-OPEN-OVERCLAIM");
    expect(over.length).toBeGreaterThan(0);
    expect(over[0].message).toContain("oeq:frontier");
  });

  it("does NOT flag an establishment claim whose term lives in a NON-open statement", () => {
    const c = core({
      statements: [
        stmt("lem:bracket", "lemma", "a certified two-sided bracket on the risk"),
        stmt("oeq:frontier", "openendedquestion", "the sharp minimax frontier"),
      ],
      // "bracket" is a proved(-to-prove, non-open) term, so establishing it is honest.
      tldr: "We establish a certified bracket on the risk.",
    });
    const over = checkProseConsistency(c).filter((x) => x.code === "PROSE-OPEN-OVERCLAIM");
    expect(over).toEqual([]);
  });

  it("does NOT flag when the open target is acknowledged as open (negation guard)", () => {
    const c = core({
      statements: [stmt("oeq:frontier", "openendedquestion", "the sharp minimax frontier")],
      project_justification: {
        gap: "the frontier is unknown",
        niche: "we open it up",
        fill: "The sharp frontier is left as an open question; we do not determine it here.",
      },
    });
    const over = checkProseConsistency(c).filter((x) => x.code === "PROSE-OPEN-OVERCLAIM");
    expect(over).toEqual([]);
  });

  it("returns no warnings for a clean, consistent core", () => {
    const c = core({
      statements: [stmt("thm:barrier", "theorem", "a proof-method obstruction")],
      tldr: "We prove a proof-method obstruction for the two-point route.",
    });
    expect(checkProseConsistency(c)).toEqual([]);
  });

  // A well-scoped open node narrows itself by reciting what is already settled before
  // posing its question. Both signals below fired on stat_cot_observational_efficiency
  // against prose that was TRUE — the cited criterion really is proved — and would
  // recur for any correctly-narrowed open node.
  it("does not flag a sentence whose only establishment verb IS the flagged term", () => {
    const c = core({
      statements: [
        stmt("lem:criterion", "lemma", "square summability governs the series", "proved"),
        stmt(
          "oeq:adaptive",
          "openendedquestion",
          "The spectral subproblem is settled. Does there exist an adaptive procedure?",
        ),
      ],
      tldr: "The spectral existence criterion is settled;",
    });
    // "settled" is both an ESTABLISH verb and a word unique to the open statement, so it
    // used to match itself. Removing it leaves no establishment claim ⇒ vacuous.
    expect(checkProseConsistency(c).filter((x) => x.code === "PROSE-OPEN-OVERCLAIM")).toEqual([]);
  });

  it("does not flag when the establishment verb survives narrowing inside the question", () => {
    const c = core({
      statements: [
        stmt("oeq:charac", "openendedquestion", "Does there exist a characterization of the class?"),
      ],
      related_work: "The characterization is standard in this literature.",
    });
    // Here narrowing keeps "characterization" (it is in the QUESTION), so the recital
    // rule cannot help — only the circular-match test can. Prose merely NAMES the object
    // without claiming to have established it; the sole ESTABLISH hit is the term itself.
    expect(checkProseConsistency(c).filter((x) => x.code === "PROSE-OPEN-OVERCLAIM")).toEqual([]);
  });

  it("does not treat the open node's settled recital as naming the open target", () => {
    const c = core({
      statements: [
        stmt(
          "oeq:adaptive",
          "openendedquestion",
          "The spectral subproblem is settled: square summability is necessary and " +
            "sufficient for existence of the series. Does there exist an adaptive " +
            "calibration procedure?",
        ),
      ],
      related_work: "the Gaussian-series existence criteria themselves are established.",
    });
    // "existence" lives only in the recital, which describes PROVED material. NOTE the
    // recital is recognised by its establishment verb ("is settled"), matching the shape
    // actually observed. A recital phrased as a bare assertion ("X is necessary and
    // sufficient for Y", no verb) is NOT recognised and still leaks its terms; narrowing
    // to interrogative sentences alone would cover that but would also drop a target
    // legitimately introduced in a declarative ("Let T be the threshold. Does …?"),
    // trading these false positives for false negatives on the signal that matters.
    expect(checkProseConsistency(c).filter((x) => x.code === "PROSE-OPEN-OVERCLAIM")).toEqual([]);
  });

  it("still flags a genuine over-claim on a node that carries a settled recital", () => {
    const c = core({
      statements: [
        stmt(
          "oeq:adaptive",
          "openendedquestion",
          "Square summability is necessary and sufficient for existence of the series. " +
            "Does there exist an adaptive recalibration procedure?",
        ),
      ],
      tldr: "We establish the adaptive recalibration procedure for the full parent.",
    });
    // The narrowing must not silence the signal: "recalibration" comes from the QUESTION,
    // and "establish" survives its removal, so this is a real over-claim.
    const over = checkProseConsistency(c).filter((x) => x.code === "PROSE-OPEN-OVERCLAIM");
    expect(over.length).toBeGreaterThan(0);
    expect(over[0].message).toContain("oeq:adaptive");
  });
});
