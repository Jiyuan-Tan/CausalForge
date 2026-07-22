import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { repairLatexStringsDeep } from "../discovery/core/latex_serialization.js";

/**
 * P5 review data and legacy per-section brief formatters. Automated post-P5
 * revision is now owned by one holistic manuscript reviser; P1/P2 no longer
 * consume these briefs. The formatters remain for review inspection and old
 * artifact compatibility.
 *
 * Routing is by the finding's `section` field, matched fuzzily to the outline
 * section name (referees label findings with the section heading). Cross-cutting
 * findings (`global`, `clarity & presentation`) reach every section; the drafter
 * is told to act only on what applies locally and never to alter a frozen env.
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

const SEV_ORDER = { major: 0, minor: 1, nit: 2 } as const;

/** lowercase, collapse every non-alphanumeric run to a single space, trim. */
function norm(s: string): string {
  return s.toLowerCase().replace(/[^a-z0-9]+/g, " ").trim();
}

/** Cross-cutting categories a referee uses for paper-wide findings — routed to every section. */
const GLOBAL_SECTIONS = new Set(["global", "clarity presentation", "clarity", "presentation"]);

function isGlobal(f: ReviewFinding): boolean {
  return GLOBAL_SECTIONS.has(norm(f.section));
}

/** A finding belongs to `sectionName` if its section label matches fuzzily (equal, or either
 *  contains the other — "Appendix B" ⊂ "Appendix B. Empirical-Process …"). */
function matchesSection(f: ReviewFinding, sectionName: string): boolean {
  const a = norm(f.section);
  const b = norm(sectionName);
  if (!a || !b) return false;
  if (a === b || a.includes(b) || b.includes(a)) return true;
  // Referees commonly call an end-of-paper paragraph "Verification note" or
  // "Proof of Theorem", while the outline owns it under an Appendix heading.
  // Route that feedback to the authored appendix section, not only to generated
  // proof blocks, so stale trust-boundary prose is actually rewritten.
  return b.includes("appendix") && (a.includes("verification note") || a.includes("proof of theorem"));
}

/** Format a set of findings as an actionable bullet list (major first). */
function formatFindings(findings: ReviewFinding[]): string {
  if (findings.length === 0) return "(no prior referee findings for this section — first draft)";
  return findings
    .slice()
    .sort((x, y) => (SEV_ORDER[x.severity] ?? 9) - (SEV_ORDER[y.severity] ?? 9))
    .map((f) => `- [${f.severity}] (${f.section}) ${f.issue}\n  Suggested fix: ${f.fix}`)
    .join("\n");
}

/** Referee findings bearing on a given BODY section: those matched to it, plus cross-cutting ones. */
export function sectionRevisionBrief(review: PriorReview | null, sectionName: string): string {
  if (!review) return "(no prior referee review — this is a first draft)";
  const relevant = review.findings.filter((f) => matchesSection(f, sectionName) || isGlobal(f));
  return formatFindings(relevant);
}

/** Referee findings for the abstract/introduction (front matter), plus cross-cutting ones. */
export function frontMatterRevisionBrief(review: PriorReview | null): string {
  if (!review) return "(no prior referee review — this is a first draft)";
  const relevant = review.findings.filter(
    (f) => {
      const section = norm(f.section);
      return section.includes("abstract") || section.includes("intro") || section.includes("front matter") || isGlobal(f);
    }, // why: reviewers use combined labels such as "Abstract and Introduction".
  );
  return formatFindings(relevant);
}

/** Referee findings about the rendered proofs (section label contains "proof"). */
export function proofRevisionBrief(review: PriorReview | null, objId?: string): string {
  if (!review) return "(no prior referee review — this is a first draft)";
  const target = objId ? norm(objId) : "";
  const relevant = review.findings.filter((f) => {
    const section = norm(f.section);
    if (!section.includes("proof")) return false;
    if (!target) return true;
    const text = norm(`${f.section} ${f.issue} ${f.fix}`);
    // A proof-wide/global proof finding applies to all proofs; otherwise only
    // invalidate the named object. This keeps unrelated proof renders reusable.
    return isGlobal(f) || section === "proofs" || section.includes("proofs of the main results") || text.includes(target);
  });
  return formatFindings(relevant);
}

/** Referee findings the P1 outline owns: `structure`-kind ones (wrong env kind, overclaiming
 *  title, contribution scope, placement). Drives an `--from P1` rewind's outline regeneration. */
export function outlineRevisionBrief(review: PriorReview | null): string {
  if (!review) return "(no prior referee review — this is a first draft)";
  const relevant = review.findings.filter((f) => f.kind === "structure");
  if (relevant.length === 0) return "(no structural referee findings — keep the existing structure)";
  return formatFindings(relevant);
}
