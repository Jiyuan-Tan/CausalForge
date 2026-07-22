import { describe, it, expect } from "vitest";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  sectionRevisionBrief,
  frontMatterRevisionBrief,
  proofRevisionBrief,
  outlineRevisionBrief,
  loadPriorReview,
  type PriorReview,
  type FindingKind,
} from "../src/presentation/revision_brief.js";

const REVIEW: PriorReview = {
  recommendation: "major_revision",
  findings: [
    { severity: "major", section: "global", issue: "overstates rate characterization", fix: "retitle as lower bound" },
    { severity: "major", section: "Minimax Lower Bound", issue: "essential clause unsupported", fix: "remove sentence" },
    { severity: "minor", section: "abstract", issue: "missing qualifier", fix: "add calibration caveat" },
    { severity: "major", section: "intro", issue: "causal language", fix: "say observed-law" },
    { severity: "minor", section: "Appendix B", issue: "lemmas look derived", fix: "label as reductions" },
    { severity: "minor", section: "Proofs of the main results", issue: "Lean comments distracting", fix: "move to appendix" },
    { severity: "nit", section: "Clarity & Presentation", issue: "labels unusual", fix: "use thm:" },
  ],
};

describe("revision brief routing", () => {
  it("routes a section-matched finding plus cross-cutting ones to a body section", () => {
    const b = sectionRevisionBrief(REVIEW, "Minimax Lower Bound");
    expect(b).toContain("essential clause unsupported"); // section-matched
    expect(b).toContain("overstates rate characterization"); // global cross-cutting
    expect(b).toContain("labels unusual"); // clarity & presentation cross-cutting
    expect(b).not.toContain("causal language"); // intro-only, not this section
    expect(b).not.toContain("missing qualifier"); // abstract-only
  });

  it("fuzzy-matches a referee label that is a prefix of the outline section name", () => {
    const b = sectionRevisionBrief(REVIEW, "Appendix B. Empirical-Process and Cross-Fitting Details");
    expect(b).toContain("lemmas look derived"); // "Appendix B" ⊂ full name
  });

  it("routes verification-note feedback to the authored appendix section", () => {
    const review: PriorReview = {
      recommendation: "major_revision",
      findings: [{
        severity: "major",
        section: "abstract; Verification note and maintained inputs; Proof of Theorem",
        issue: "trust boundary is stale",
        fix: "state the current unconditional theorem",
        kind: "prose",
      }],
    };
    expect(sectionRevisionBrief(review, "Appendix with proofs and auxiliary lemmas"))
      .toContain("trust boundary is stale");
  });

  it("orders findings major-first in the rendered brief", () => {
    const b = sectionRevisionBrief(REVIEW, "Minimax Lower Bound");
    expect(b.indexOf("[major]")).toBeLessThan(b.indexOf("[nit]"));
  });

  it("front matter gets abstract + intro + global, not body-section findings", () => {
    const b = frontMatterRevisionBrief(REVIEW);
    expect(b).toContain("missing qualifier"); // abstract
    expect(b).toContain("causal language"); // intro
    expect(b).toContain("overstates rate characterization"); // global
    expect(b).not.toContain("essential clause unsupported"); // body section
  });

  it("proof brief picks only proof-section findings", () => {
    const b = proofRevisionBrief(REVIEW);
    expect(b).toContain("Lean comments distracting");
    expect(b).not.toContain("overstates rate characterization");
    expect(b).not.toContain("lemmas look derived"); // appendix-B section, not a proof
  });

  it("scopes object-named proof findings to that proof", () => {
    const review: PriorReview = {
      recommendation: "minor_revision",
      findings: [{
        severity: "minor",
        section: "Proof of thm:main",
        issue: "thm:main skips an explanation",
        fix: "explain the reduction",
        kind: "prose",
      }],
    };
    expect(proofRevisionBrief(review, "thm:main")).toContain("skips an explanation");
    expect(proofRevisionBrief(review, "thm:other")).not.toContain("skips an explanation");
  });

  it("returns an inert sentinel when there is no prior review (first draft)", () => {
    expect(sectionRevisionBrief(null, "Minimax Lower Bound")).toMatch(/first draft/i);
    expect(frontMatterRevisionBrief(null)).toMatch(/first draft/i);
    expect(proofRevisionBrief(null)).toMatch(/first draft/i);
  });

  it("a section with no matching or global findings still yields a usable sentinel string", () => {
    const onlyLocal: PriorReview = {
      recommendation: "minor_revision",
      findings: [{ severity: "minor", section: "Setup and Assumptions", issue: "x", fix: "y" }],
    };
    const b = sectionRevisionBrief(onlyLocal, "Related Literature");
    expect(b).toMatch(/no prior referee findings/i);
  });
});

describe("FindingKind", () => {
  it("admits the five generic kinds", () => {
    const ks: FindingKind[] = ["prose", "structure", "statement", "citation", "other"];
    expect(ks).toHaveLength(5);
  });
});

describe("loadPriorReview carries kind", () => {
  it("preserves a tagged kind and tolerates an absent one", async () => {
    const dir = mkdtempSync(join(tmpdir(), "psrev-"));
    writeFileSync(
      join(dir, "p5_review.json"),
      JSON.stringify({
        recommendation: "major_revision",
        findings: [
          { severity: "major", section: "global", issue: "x", fix: "y", kind: "structure" },
          { severity: "minor", section: "intro", issue: "z", fix: "w" },
        ],
      }),
    );
    const r = await loadPriorReview(dir);
    expect(r!.findings[0].kind).toBe("structure");
    expect(r!.findings[1].kind).toBeUndefined();
  });
});

describe("outlineRevisionBrief (P1 structure findings)", () => {
  const review: PriorReview = {
    recommendation: "major_revision",
    findings: [
      { severity: "major", section: "main results", issue: "Def 4 is not a definition", fix: "make it a corollary", kind: "structure" },
      { severity: "major", section: "abstract", issue: "wording", fix: "reword", kind: "prose" },
      { severity: "major", section: "global", issue: "title overclaims", fix: "drop Sharp", kind: "structure" },
    ],
  };
  it("selects only structure-kind findings", () => {
    const b = outlineRevisionBrief(review);
    expect(b).toContain("Def 4 is not a definition");
    expect(b).toContain("title overclaims");
    expect(b).not.toContain("wording");
  });
  it("is a friendly no-op string when there is no review", () => {
    expect(outlineRevisionBrief(null)).toMatch(/no prior referee review/i);
  });
});
