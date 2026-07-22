// Orchestrator-owned routing from a P5 finding to either the holistic manuscript
// reviser or an explicit halt. The P5 referee remains pipeline-stage-independent.
import type { FindingKind, ReviewFinding, PriorReview } from "./revision_brief.js";

export const MAX_P5_REVISION_PASSES = 2;

export type RevisionAction =
  | { type: "revise" }
  | { type: "escalate" } // the math/statement itself — out of causalsmith scope
  | { type: "decide" }; // orchestrator judgement (other, or a kind with no single stage)

/** kind → orchestrator action. Reframing and local rewrites go to one reviser. */
export const KIND_ACTION: Record<FindingKind, RevisionAction> = {
  prose: { type: "revise" },
  structure: { type: "revise" },
  statement: { type: "escalate" },
  citation: { type: "decide" },
  other: { type: "decide" },
};

const norm = (s: string) => s.toLowerCase().replace(/[^a-z0-9]+/g, " ").trim();

/** A referee can identify a valid problem whose remedy is outside presentation
 * rewriting. Never ask the holistic reviser to synthesize research. */
export function requiresNewResearch(f: ReviewFinding): boolean {
  if (f.remedy && f.remedy !== "rewrite") return true;
  const text = norm(`${f.issue} ${f.fix}`);
  return /\b(?:prove|new theorem|new lemma|derive a result|additional result|simulation|empirical exercise|experiment|implement|new data|collect data|literature search|find a citation|source formalization|change the lean|change the theorem)\b/.test(text);
}

export function actionForFinding(f: ReviewFinding): RevisionAction {
  if (requiresNewResearch(f)) return { type: "escalate" };
  return KIND_ACTION[f.kind ?? "other"];
}

/** Stable enough to compare the same issue family across successive P5 wordings.
 * P5 supplies `finding_id` when possible; the normalized fallback keeps old runs usable. */
export function findingFingerprint(f: ReviewFinding): string {
  if (f.finding_id?.trim()) return norm(f.finding_id);
  const issue = norm(f.issue)
    .replace(/\b\d+(?:\.\d+)?\b/g, "#")
    .split(" ")
    .slice(0, 18)
    .join(" ");
  return `${f.kind ?? "other"}|${norm(f.section)}|${issue}`;
}

/** Only prose/structure rewrite findings are safe for unattended holistic revision. Everything else is
 * persisted for adjudication instead of being silently weakened or citation-laundered. */
export function partitionFindings(findings: ReviewFinding[]): {
  repairable: ReviewFinding[];
  blocked: ReviewFinding[];
} {
  const repairable: ReviewFinding[] = [];
  const blocked: ReviewFinding[] = [];
  for (const finding of findings) {
    const action = actionForFinding(finding);
    (action.type === "revise" ? repairable : blocked).push(finding);
  }
  return { repairable, blocked };
}

/** Whether the reviser may use paper-wide reframing rather than only local edits. */
export function revisionMode(findings: ReviewFinding[]): "local" | "reframe" {
  const text = norm(findings.map((f) => `${f.section} ${f.issue} ${f.fix}`).join(" "));
  return findings.some((f) =>
    f.kind === "structure" &&
    f.severity === "major" &&
    ["global", "title", "outline", "contribution", "paper structure"].includes(norm(f.section))
  ) || /\b(?:contribution|significance|audience|positioning|econometric|reframe|retitle|paper organization|representation|law level)\b/.test(text)
    ? "reframe"
    : "local";
}

/** A human-readable routing plan grouped by holistic revision vs explicit halt. */
export function renderRoutingPlan(review: PriorReview): string {
  const byBucket = new Map<string, string[]>();
  const push = (k: string, s: string) => byBucket.set(k, [...(byBucket.get(k) ?? []), s]);
  const repairable = partitionFindings(review.findings).repairable;
  const mode = revisionMode(repairable);
  for (const f of review.findings) {
    const a = actionForFinding(f);
    const remedy = f.remedy ? `·${f.remedy}` : "";
    const line = `[${f.severity}·${f.kind ?? "other"}${remedy}] (${f.section}) ${f.issue}`;
    if (a.type === "revise") push(`holistic revision (${mode})`, line);
    else if (a.type === "escalate") push("escalate — out of causalsmith scope (bank/causalsmith)", line);
    else push("your call — orchestrator decides", line);
  }
  const out: string[] = [`# Revision routing plan (${review.recommendation})`, ""];
  for (const [bucket, lines] of byBucket) {
    out.push(`## ${bucket}`, ...lines.map((l) => `- ${l}`), "");
  }
  out.push(repairable.length > 0
    ? `→ one holistic ${mode} pass; formal statements remain frozen`
    : "→ no unattended revision (escalate/decide only)");
  return out.join("\n") + "\n";
}
