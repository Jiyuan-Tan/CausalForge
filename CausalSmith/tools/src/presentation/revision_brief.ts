import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { repairLatexStringsDeep } from "../discovery/core/latex_serialization.js";

/**
 * P5 review data. Automated post-P5 revision is owned by one holistic manuscript
 * reviser; P1/P2 first-draft prompts carry the inert FIRST_DRAFT_BRIEF constant
 * (it participates in content cache keys, so its bytes must never change).
 */
/** Generic, stage-independent problem kind a P5 referee tags a finding with. The orchestrator
 *  (not the referee) maps this to a pipeline action — see revision_routing.ts. */
export type FindingKind = "prose" | "structure" | "statement" | "citation" | "other";
export type FindingRemedy =
  | "rewrite"
  | "citation_research"
  | "new_theorem"
  | "simulation"
  | "implementation"
  | "source_change"
  | "adjudication";

export interface ReviewFinding {
  severity: "major" | "minor" | "nit";
  section: string;
  issue: string;
  fix: string;
  /** Advisory generic classification; absent ⇒ treat as "other". */
  kind?: FindingKind;
  /** Stable issue-family id supplied by P5; used to detect non-converging rewrites. */
  finding_id?: string;
  /** What resolving the finding actually requires. Only `rewrite` is unattended. */
  remedy?: FindingRemedy;
}
export interface PriorReview {
  recommendation: string;
  score?: number;
  summary?: string;
  findings: ReviewFinding[];
}

/** Load the prior P5 referee review from the run dir, or null if none exists yet. */
export async function loadPriorReview(outDir: string): Promise<PriorReview | null> {
  const raw = await readFile(join(outDir, "p5_review.json"), "utf8").catch(() => null);
  if (raw === null) return null;
  try {
    const r = JSON.parse(raw) as Partial<PriorReview>;
    repairLatexStringsDeep(r);
    if (!Array.isArray(r.findings)) return null;
    return {
      recommendation: r.recommendation ?? "?",
      score: typeof r.score === "number" ? r.score : undefined,
      summary: r.summary,
      findings: r.findings,
    };
  } catch {
    return null;
  }
}

/** The revision-brief slot value for a first draft. P5 feedback is never fanned back out to the
 * P1/P2 drafters (the holistic reviser owns post-review edits), so every drafting prompt receives
 * exactly this string. It is baked into section/proof/front-matter/outline cache keys — keep it
 * byte-identical or every cached artifact re-renders. */
export const FIRST_DRAFT_BRIEF = "(no prior referee review — this is a first draft)";
