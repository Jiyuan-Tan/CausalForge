#!/usr/bin/env node
/**
 * Auto-bank a CausalSmith run.
 *
 * Routing (by formalizationKind(qid)):
 *   - research-mode qids (eid_*, pid_*, panel_*, q\d+_*, q_*) →
 *     `_bank/{accepted,downgraded,failed,legacy}/<qid>_<spec>/` (tiered).
 *     `--reason` is optional and free-form for the success tiers; it is also
 *     optional for `--tier failed` (no validation against a taxonomy — the
 *     proposer-output reviewer chain already captures the reason).
 *   - study-mode qids (insight-style, no recognized prefix):
 *       - success tiers (`accepted` / `downgraded` / `legacy`) →
 *         `_literature_bank/<qid>_<spec>/` (flat — no tier subdir; the
 *         proposer novelty rubric does not apply to paper reformalizations,
 *         so the `--tier` value is recorded in state.json but does not
 *         partition the on-disk layout).
 *       - `--tier failed` → `_literature_bank/_failed/<reason>/<qid>_<spec>/`
 *         with a `BANK_REASON.md` stamp. Requires `--reason <r>` where `r`
 *         is one of `LITERATURE_FAILURE_REASONS` (see `src/bank.ts`); routing
 *         is parallel to the success side so study-pipeline S5 can find a
 *         canonical record for the failed Lean formalization attempt.
 *
 * Performs the four mechanical steps that previously had to be done by hand:
 *   1. Read state.json from the canonical (or archived) location.
 *   2. Patch banked* fields (banked, banked_tier, banked_on, banked_reason,
 *      and optional seeds_burned) into the state.json in place.
 *   3. Move the entire <qid>/ directory to the bank destination (tiered for
 *      research, flat for study).
 *   4. Generate a README.md scaffold (frontmatter + body) from the state.json
 *      and reviews.jsonl content. Pre-fills tier_at_proposal /
 *      tier_at_derivation by parsing iterations + the reviews log.
 *
 * Usage:
 *   npx tsx tools/bin/bank_entry.ts \
 *     --qid <qid> --spec <spec> \
 *     --tier accepted|downgraded|failed|legacy \
 *     [--reason "<one-sentence verbatim verdict>"] \
 *     [--achieved-tier <incremental|subfield|field|flagship>] \
 *     [--seeds-burned "0,3"] \
 *     [--seed-burn-reason "<why these seeds are burned>"] \
 *     [--dry-run]
 *
 * The tool is conservative: it refuses to bank an already-banked entry, it
 * refuses to overwrite an existing _bank/<tier>/<qid>_<spec>/ destination,
 * and it leaves the original directory untouched in --dry-run mode.
 */
import { existsSync, readFileSync } from "node:fs";
import { mkdir, readFile, readdir, rename, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { STAGE_ORDER } from "../src/constants.js";
import {
  LITERATURE_FAILURE_REASONS,
  type LiteratureFailureReason,
} from "../src/discovery/bank.js";
import { routeToBank } from "../src/shared/bank_router.js";
import { auditSubstrateGates, citedBlockers } from "../src/formalization/gate_ops.js";
import { CoreSchema } from "../src/discovery/core/schema.js";
import { PlanSchema } from "../src/formalization/plan/schema.js";
import { GraphSchema } from "../src/graph/types.js";
import { parseLeanDecls } from "../src/formalization/crosswalk.js";
import { bankSoundnessIssues } from "../src/formalization/bank_soundness.js";
import { auditCitedReview, auditDelivery } from "../src/formalization/delivery_audit.js";
import type { CitedReviewReceipt, DeliveryReviewReceipt } from "../src/types.js";
import { normalizeNoveltyTarget, type NoveltyTarget } from "../src/novelty.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

const STAGE_0_5_IDX = STAGE_ORDER.indexOf("0.5");

type Tier = "accepted" | "downgraded" | "failed" | "legacy";
const TIERS: Tier[] = ["accepted", "downgraded", "failed", "legacy"];

// Reusability tag for downgraded/failed entries: separates "good proposal,
// solver shortfall — retry on a stronger solver or with human help" from
// "proposal itself was overrated, no derivation will rescue it" and "no
// signal available". Auto-derived from the final Stage 0.5 review's
// `proposal_promise_gap` when the operator does not pass `--reusable`.
type Reusable = "solver_blocked" | "not_reusable" | "unknown";
const REUSABLE_VALUES: Reusable[] = ["solver_blocked", "not_reusable", "unknown"];

// How a future topic selector should treat a collision with this banked entry
// (read by the causalsmith-topics saturation check). This is NOT reliably derivable
// from `proposal_promise_gap` — the same gap (`tier_genuinely_below`) covers both
// a re-raisable sound-but-overclaimed result and a dead already-known kernel — so
// the orchestrator passes `--reraise-status` from its hopeless-vs-fixable call at
// bank time (hopeless-TOPIC → true-negative; sound-but-novelty-overclaimed →
// re-raise; sound-but-a-construction-fell-short → retry). Defaults to `unknown`,
// which the topics skill resolves by skimming the reviews.
type ReraiseStatus = "re-raise" | "retry" | "true-negative" | "unknown";
const RERAISE_STATUS_VALUES: ReraiseStatus[] = ["re-raise", "retry", "true-negative", "unknown"];

interface Args {
  qid: string;
  spec: string;
  tier: Tier;
  reason?: string;
  reusable?: Reusable;
  /**
   * Re-raise verdict for the topics-skill saturation check. Set from the
   * orchestrator's hopeless-vs-fixable judgment at bank time; defaults to
   * `unknown` (topics skill skims the reviews when absent/unknown).
   */
  reraiseStatus?: ReraiseStatus;
  /**
   * Override for the README's `proposal_promise_gap` field. By default the
   * value is parsed from the latest Stage 0.5 review in reviews.jsonl; pass
   * this when the reviewer's label is stale (e.g. a banked run where the
   * solver upgrade reclassified the failure from solver-side to proposal-side).
   */
  proposalPromiseGap?: string;
  /** Achieved novelty tier for a below-floor bank; drives future --upgrade validation. */
  achievedTier?: NoveltyTarget;
  seedsBurned: number[];
  seedBurnReason?: string;
  dryRun: boolean;
  noMintOqs: boolean;
  /** Gate node ids discharged before this (re-)bank; recorded when re-banking a reopened entry. */
  dischargedGates?: string[];
}

function parseArgs(argv: string[]): Args {
  const a: Partial<Args> & { seedsBurned: number[]; dryRun: boolean; noMintOqs: boolean } = {
    seedsBurned: [],
    dryRun: false,
    noMintOqs: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const k = argv[i];
    const v = argv[i + 1];
    switch (k) {
      case "--qid":              a.qid = v; i++; break;
      case "--spec":             a.spec = v; i++; break;
      case "--tier":             a.tier = v as Tier; i++; break;
      case "--reason":           a.reason = v; i++; break;
      case "--reusable":         a.reusable = v as Reusable; i++; break;
      case "--reraise-status":   a.reraiseStatus = v as ReraiseStatus; i++; break;
      case "--proposal-promise-gap": a.proposalPromiseGap = v; i++; break;
      case "--achieved-tier": {
        const tier = normalizeNoveltyTarget(v);
        if (!tier) throw new Error("Usage: --achieved-tier <incremental|subfield|field|flagship>");
        a.achievedTier = tier;
        i++;
        break;
      }
      case "--seeds-burned":     a.seedsBurned = v.split(",").map((s) => parseInt(s.trim(), 10)).filter(Number.isFinite); i++; break;
      case "--seed-burn-reason": a.seedBurnReason = v; i++; break;
      case "--dry-run":          a.dryRun = true; break;
      case "--no-mint-oqs":      a.noMintOqs = true; break;
      default:
        if (k?.startsWith("--")) throw new Error(`Unknown flag: ${k}`);
    }
  }
  if (!a.qid || !a.spec || !a.tier) {
    throw new Error("Required: --qid <qid> --spec <spec> --tier accepted|downgraded|failed|legacy");
  }
  if (!TIERS.includes(a.tier)) {
    throw new Error(`Invalid --tier: ${a.tier}. Must be one of ${TIERS.join("|")}`);
  }
  if (a.reusable !== undefined && !REUSABLE_VALUES.includes(a.reusable)) {
    throw new Error(`Invalid --reusable: ${a.reusable}. Must be one of ${REUSABLE_VALUES.join("|")}`);
  }
  if (a.reraiseStatus !== undefined && !RERAISE_STATUS_VALUES.includes(a.reraiseStatus)) {
    throw new Error(`Invalid --reraise-status: ${a.reraiseStatus}. Must be one of ${RERAISE_STATUS_VALUES.join("|")}`);
  }
  return a as Args;
}

/**
 * Walk reviews.jsonl tail for the most recent Stage 0.5 review entry, return
 * its `proposal_promise_gap` field if present. Used to auto-classify the
 * banked entry's `reusable` status when the operator doesn't pass `--reusable`.
 */
/** Resolve a run/banked dir's reviews.jsonl: canonical reviews/ subfolder first,
 *  then the pre-move legacy locations at the dir root. Returns null if none exist. */
function resolveReviewsLog(srcDir: string, qid: string, spec: string): string | null {
  const candidates = [
    path.join(srcDir, "reviews", "reviews.jsonl"),
    path.join(srcDir, `${qid}_${spec}_reviews`, "reviews.jsonl"),
    path.join(srcDir, "reviews.jsonl"),
    path.join(srcDir, `${qid}_${spec}_reviews.jsonl`),
  ];
  return candidates.find((c) => existsSync(c)) ?? null;
}

async function proposalPromiseGapFromReviews(
  srcDir: string,
  qid: string,
  spec: string,
): Promise<string | null> {
  const reviewsLog = resolveReviewsLog(srcDir, qid, spec);
  if (!reviewsLog) return null;
  const lines = (await readFile(reviewsLog, "utf8")).trim().split("\n").filter(Boolean);
  for (let i = lines.length - 1; i >= 0; i--) {
    try {
      const r = JSON.parse(lines[i]);
      if (r.kind !== "review") continue;
      const stage = String(r.stage ?? "");
      if (!(stage.startsWith("stage_0.5") || stage === "0.5")) continue;
      const gap = r?.review?.proposal_promise_gap;
      if (typeof gap === "string" && gap.length > 0) return gap;
    } catch { /* skip malformed lines */ }
  }
  return null;
}

/**
 * Mapping from Stage 0.5 reviewer's `proposal_promise_gap` to bank-level
 * `reusable` tag. Solver-shortfall gaps (kernel substituted, assumption
 * omitted, direction-only, missing constructive object) all flag the
 * proposal as worth retrying with a stronger solver. `tier_genuinely_below`
 * flags the proposal as not worth retrying.
 */
function reusableFromGap(gap: string | null): Reusable {
  switch (gap) {
    case "kernel_substituted":
    case "assumption_omitted":
    case "direction_only":
    case "constructive_object_missing":
      return "solver_blocked";
    case "tier_genuinely_below":
    case "proposal_drift":
      return "not_reusable";
    default:
      return "unknown";
  }
}


/** Locate the entry's state.json — prefer canonical, fall back to archived. */
/** Shape `auditSubstrateGates` needs from either store. */
type AuditNode = { id: string; kind?: string; lean_name?: string; gate?: boolean; gate_class?: string };

/**
 * Normalize a run's `plan.json` / `graph.json` `nodes` into an array.
 *
 * The two stores disagree on shape and always have: `graph.json` holds an ARRAY of nodes (each with
 * its own `id`), while `plan.json` holds an OBJECT keyed by node id (which is why `bin/gate.ts`
 * writes `plan.nodes[nodeId]` but iterates `graph.nodes`). Reading only the array form silently
 * yields `[]` for every real plan, which disables the plan half of the audit — and, worse, makes
 * `bankEntry` disagree with the `gate.ts --audit` pre-flight, which reads the map correctly.
 *
 * Both files live either at the run-dir root or under `formalization/`, depending on the stage that
 * wrote them, and either may be absent on an early-tier bank — a missing or unparseable file yields
 * `[]`, so the audit degrades to "no nodes found" (reported as prose-only debt) rather than crashing.
 */
export function normalizeNodes(nodes: unknown): AuditNode[] {
  if (Array.isArray(nodes)) {
    return nodes.filter((n): n is AuditNode => !!n && typeof (n as AuditNode).id === "string");
  }
  if (nodes && typeof nodes === "object") {
    return Object.entries(nodes as Record<string, unknown>)
      .filter(([, v]) => !!v && typeof v === "object")
      .map(([id, v]) => ({ ...(v as Omit<AuditNode, "id">), id }));
  }
  return [];
}

async function readNodesFor(srcDir: string, file: "plan.json" | "graph.json"): Promise<AuditNode[]> {
  for (const p of [path.join(srcDir, file), path.join(srcDir, "formalization", file)]) {
    if (!existsSync(p)) continue;
    try {
      const parsed = JSON.parse(await readFile(p, "utf8"));
      const nodes = normalizeNodes(parsed?.nodes);
      if (nodes.length > 0) return nodes;
    } catch {
      /* unparseable → treat as absent; the audit reports prose-only debt instead of crashing */
    }
  }
  return [];
}

async function locateStateJson(srcDir: string, qid: string, spec: string): Promise<string> {
  const bare = path.join(srcDir, "state.json");
  const bareArchived = path.join(srcDir, "state.archived.json");
  const canonical = path.join(srcDir, `${qid}_${spec}_state.json`);
  const archived = path.join(srcDir, `${qid}_${spec}_state.archived.json`);
  if (existsSync(bare)) return bare;
  if (existsSync(canonical)) return canonical;
  if (existsSync(bareArchived)) return bareArchived;
  if (existsSync(archived)) return archived;
  const all = await readdir(srcDir).catch(() => []);
  const candidates = all.filter(
    (f) => f === "state.json" || (f.includes(`${qid}_${spec}`) && f.endsWith("state.json")),
  );
  if (candidates.length === 1) return path.join(srcDir, candidates[0]);
  throw new Error(`No state.json for ${qid}/${spec} in ${srcDir} (looked for canonical, archived, and unique fallback)`);
}

/** Parse final Stage -0.5 verdict from state.iterations. */
function tierAtProposal(state: any): string {
  const its = state?.proposed_from?.iterations as Array<{ verdict: string }> | undefined;
  if (!its || its.length === 0) return "NA";
  const final = state?.proposed_from?.final_verdict;
  if (final && typeof final === "string" && final !== "pending") return final;
  // Walk back to last non-"revise-cap-exhausted" verdict.
  for (let i = its.length - 1; i >= 0; i--) {
    const v = its[i].verdict?.toUpperCase();
    if (v && v !== "REVISE-CAP-EXHAUSTED") return v;
  }
  return "NA";
}

/**
 * Parse final Stage 0.5 verdict from reviews.jsonl tail. Filters to
 * `kind === "review"` entries — pipeline-notes (manual-rollback,
 * manual-resolution, ...) and intervention entries reuse the same `stage`
 * field but carry sentinel `status` strings like "manual-rollback" that
 * are not real verdicts.
 */
async function tierAtDerivation(srcDir: string, qid: string, spec: string): Promise<string> {
  const reviewsLog = resolveReviewsLog(srcDir, qid, spec);
  if (!reviewsLog) return "NA";
  const lines = (await readFile(reviewsLog, "utf8")).trim().split("\n").filter(Boolean);
  for (let i = lines.length - 1; i >= 0; i--) {
    try {
      const r = JSON.parse(lines[i]);
      if (r.kind !== "review") continue;
      const stage = String(r.stage ?? "");
      if (stage.startsWith("stage_0.5") || stage === "0.5") {
        return String(r.status ?? "NA").toUpperCase();
      }
    } catch { /* skip malformed lines */ }
  }
  return "NA";
}

/** Recover the achieved novelty tier recorded by the terminal/validity gate. */
async function achievedTierFromDecisionLog(srcDir: string): Promise<NoveltyTarget | undefined> {
  const candidates = [
    path.join(srcDir, "orchestrator", "decision_log.jsonl"),
    path.join(srcDir, "decision_log.jsonl"),
  ];
  for (const candidate of candidates) {
    if (!existsSync(candidate)) continue;
    try {
      const lines = (await readFile(candidate, "utf8")).trim().split("\n").filter(Boolean);
      for (let i = lines.length - 1; i >= 0; i--) {
        const row = JSON.parse(lines[i]) as Record<string, unknown>;
        const direct = normalizeNoveltyTarget(
          typeof row.achieved_tier === "string" ? row.achieved_tier : undefined,
        );
        if (direct) return direct;
        const codex = typeof row.codex === "string" ? row.codex : "";
        const match = codex.match(/ACHIEVED_TIER:\s*(incremental|subfield|field|flagship)/i);
        const receipt = normalizeNoveltyTarget(match?.[1]?.toLowerCase());
        if (receipt) return receipt;
      }
    } catch {
      // Try the next supported location.
    }
  }
  return undefined;
}

/** Render a YAML-safe single-line string (quote + escape). */
function yamlStr(s: string): string {
  return JSON.stringify(s);
}

/** Render a multi-line YAML block scalar. */
function yamlBlock(s: string, indent = "  "): string {
  const lines = s.split("\n");
  return `|\n${lines.map((l) => indent + l).join("\n")}`;
}

function renderReadme(args: {
  state: any;
  tier: Tier;
  qid: string;
  spec: string;
  bankedOn: string;
  bankedReason: string;
  tierProp: string;
  tierDeriv: string;
  reusable: Reusable;
  reraiseStatus: ReraiseStatus;
  proposalPromiseGap: string | null;
  bankedNoveltyTier?: NoveltyTarget;
  seedsBurnedEntries: Array<{ index: number; one_liner: string; reason: string }>;
}): string {
  const { state, tier, qid, spec, bankedOn, bankedReason, tierProp, tierDeriv, reusable, reraiseStatus, proposalPromiseGap, bankedNoveltyTier, seedsBurnedEntries } = args;
  const topic = state?.proposed_from?.topic ?? "(unknown)";
  const noveltyTarget = state?.proposed_from?.novelty_target ?? "(unknown)";

  const seedsYaml =
    seedsBurnedEntries.length === 0
      ? "seeds_burned: []"
      : `seeds_burned:\n${seedsBurnedEntries
          .map(
            (s) =>
              `  - index: ${s.index}\n` +
              `    one_liner: ${yamlStr(s.one_liner)}\n` +
              `    reason: ${yamlStr(s.reason)}`,
          )
          .join("\n")}`;

  const failedTheoremRows = (state.theorems ?? [])
    .filter((t: any) => t?.status === "failed")
    .map((t: any) => {
      if (typeof t.minted_oq_id === "string" && t.minted_oq_id.length > 0) {
        return { theorem_local_id: t.theorem_local_id, kind: "minted" as const, oq_id: t.minted_oq_id };
      }
      const stageStr: string | null = t.stage_completed ?? null;
      const stageIdx = stageStr === null ? -1 : STAGE_ORDER.indexOf(stageStr as (typeof STAGE_ORDER)[number]);
      const pastReview = stageIdx > STAGE_0_5_IDX;
      return {
        theorem_local_id: t.theorem_local_id,
        kind: "skipped" as const,
        reason: pastReview ? "minting_disabled" : "stage_below_0_5",
        stage_at_failure: stageStr ?? "(none)",
      };
    });

  const failedTheoremsYaml =
    failedTheoremRows.length === 0
      ? ""
      : `failed_theorems:\n${failedTheoremRows
          .map((row: any) => {
            if (row.kind === "minted") {
              return `  - theorem_local_id: ${yamlStr(row.theorem_local_id)}\n` +
                     `    minted_oq_id: ${yamlStr(row.oq_id)}`;
            } else {
              return `  - theorem_local_id: ${yamlStr(row.theorem_local_id)}\n` +
                     `    minted_oq_id: null\n` +
                     `    skipped_reason: ${yamlStr(row.reason)}\n` +
                     `    stage_at_failure: ${yamlStr(String(row.stage_at_failure))}`;
            }
          })
          .join("\n")}\n`;

  const upgradeFrom = state?.proposed_from?.upgrade_from as
    | { parent_qid: string; parent_spec: string; parent_tier: string; upgrade_axis: string }
    | undefined;
  const supersedesYaml = upgradeFrom
    ? `supersedes:\n` +
      `  parent_qid: ${yamlStr(upgradeFrom.parent_qid)}\n` +
      `  parent_spec: ${yamlStr(upgradeFrom.parent_spec)}\n` +
      `  parent_tier: ${yamlStr(upgradeFrom.parent_tier)}\n` +
      `  upgrade_axis: ${yamlStr(upgradeFrom.upgrade_axis)}\n`
    : "";

  const supersedesBlurb = upgradeFrom
    ? `**Supersedes.** ${upgradeFrom.parent_qid}_${upgradeFrom.parent_spec} ` +
      `(tier=${upgradeFrom.parent_tier}, upgrade_axis=${upgradeFrom.upgrade_axis}). ` +
      `The parent remains in _bank/${upgradeFrom.parent_tier}/ as an independent reference; ` +
      `this entry is the strictly-higher-tier upgrade.\n\n`
    : "";

  const frontmatter =
    `---\n` +
    `qid: ${qid}\n` +
    `spec: ${spec}\n` +
    `topic: ${yamlStr(topic)}\n` +
    `novelty_target: ${noveltyTarget}\n` +
    `banked_novelty_tier: ${bankedNoveltyTier ?? "unknown"}\n` +
    supersedesYaml +
    `tier_at_proposal: ${tierProp}\n` +
    `tier_at_derivation: ${tierDeriv}\n` +
    `proposal_promise_gap: ${proposalPromiseGap ? yamlStr(proposalPromiseGap) : "null"}\n` +
    `reusable: ${reusable}\n` +
    `reraise_status: ${reraiseStatus}\n` +
    `gap_reasons:\n` +
    `  # TODO: paste verbatim reviewer phrases identifying which Conjecture\n` +
    `  # collapsed and why. Source: ${qid}_${spec}_reviews.jsonl and any\n` +
    `  # *_oneshot_stage0_5_*.txt files in this directory.\n` +
    `reusable_artifacts:\n` +
    `  # TODO: list LP setup / operator / witness / literature_map /\n` +
    `  # counterexample paths inside this directory that future runs should\n` +
    `  # lift rather than re-derive.\n` +
    `${seedsYaml}\n` +
    (failedTheoremsYaml ? `${failedTheoremsYaml}` : "") +
    `proof_attempt_summary: ${yamlBlock(`TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.`)}\n` +
    `banked_on: ${yamlStr(bankedOn)}\n` +
    `---\n\n`;

  const tierBlurb = "";

  const body =
    `# ${qid} / ${spec} — ${tier.charAt(0).toUpperCase() + tier.slice(1)}\n\n` +
    `**Topic.** ${topic}\n\n` +
    `**Novelty target.** ${noveltyTarget}\n\n` +
    `**Stage -0.5 verdict.** ${tierProp}\n\n` +
    `**Stage 0.5 verdict.** ${tierDeriv}\n\n` +
    `**Banking reason.** ${bankedReason || "(see banked_reason in state.json)"}\n\n` +
    supersedesBlurb +
    tierBlurb +
    `## Key files\n\n` +
    `- \`state.json\` — pipeline state at banking (\`banked: true\`).\n` +
    `- \`discovery/proposal.tex\` — final proposal version.\n` +
    `- \`discovery/writeup.tex\` — derivation note (if Stage 0 ran).\n` +
    `- \`reviews/reviews.jsonl\` — per-round reviewer log (Stage -0.5 and Stage 0.5).\n` +
    `- \`reviews/\` — per-version reviewer JSON files (if present).\n\n` +
    `## Notes\n\n` +
    `<!-- Free-form context: what makes this entry interesting, what should be\n` +
    `re-derived vs. re-used, links to follow-on runs. Fill in by hand after the\n` +
    `scaffold is generated. -->\n` +
    (failedTheoremRows.length > 0
      ? `\n## Failed theorems\n\n` +
        `Each \`minted\` entry points to a canonical OQ under \`doc/study/nodes/open_question/\`. ` +
        "`skipped` entries failed at or before Stage 0.5 (math review); the per-run failure " +
        "record still lives in this bank entry's state.json, but no OQ was minted because " +
        "the math claim itself did not clear review.\n\n" +
        failedTheoremRows
          .map((row: any) =>
            row.kind === "minted"
              ? `- \`${row.theorem_local_id}\` -> minted \`${row.oq_id}\``
              : `- \`${row.theorem_local_id}\` -> skipped at stage ${row.stage_at_failure} (${row.reason})`,
          )
          .join("\n") +
        "\n"
      : "");

  return frontmatter + body;
}

/**
 * Programmatic entry point shared by the CLI (`main` below) and in-process
 * callers (e.g. study-pipeline S5 auto-routing). Behaviour is identical to the
 * CLI's main: read state.json, validate preconditions, mint failed-theorem
 * OQs (when applicable), move the source dir to the bank destination, and
 * write a README scaffold + optional BANK_REASON.md.
 *
 * `repoRoot` may be passed explicitly (used by S5 so it doesn't have to
 * re-do the `findCausalSmithRoot` walk from `process.cwd`); when omitted it walks
 * up from `process.cwd` to the CausalSmith package root, matching CLI semantics.
 */
export interface BankEntryArgs {
  qid: string;
  spec: string;
  tier: Tier;
  reason?: string;
  /**
   * Reusability tag for downgraded/failed entries. When omitted, auto-derived
   * from the final Stage 0.5 review's `proposal_promise_gap` (solver-shortfall
   * gaps → `solver_blocked`, `tier_genuinely_below` → `not_reusable`, no
   * signal → `unknown`). Operator override always wins.
   */
  reusable?: Reusable;
  /**
   * Re-raise verdict for the topics-skill saturation check. Set from the
   * orchestrator's hopeless-vs-fixable judgment at bank time; defaults to
   * `unknown` (topics skill skims the reviews when absent/unknown).
   */
  reraiseStatus?: ReraiseStatus;
  /**
   * Override for the README's `proposal_promise_gap` field. By default the
   * value is parsed from the latest Stage 0.5 review in reviews.jsonl; pass
   * this when the reviewer's label is stale (e.g. a banked run where the
   * solver upgrade reclassified the failure from solver-side to proposal-side).
   */
  proposalPromiseGap?: string;
  /** Achieved novelty tier; required metadata for future strictly-higher upgrades. */
  achievedTier?: NoveltyTarget;
  seedsBurned?: number[];
  seedBurnReason?: string;
  dryRun?: boolean;
  noMintOqs?: boolean;
  repoRoot?: string;
  /**
   * Gate node ids discharged since the entry was reopened. Recorded (with a
   * bumped `revision`) into the re-banked state.json when `state.reopened_from`
   * is present; ignored on a normal first bank. Set by `--discharge-gate`.
   */
  dischargedGates?: string[];
}

export interface BankEntryResult {
  destDir: string;
  bankedOn: string;
  tierProp: string;
  tierDeriv: string;
  reusable: Reusable;
  proposalPromiseGap: string | null;
  bankedNoveltyTier?: NoveltyTarget;
  seedsBurnedIndices: number[];
}

export async function bankEntry(input: BankEntryArgs): Promise<BankEntryResult> {
  const args: Args = {
    qid: input.qid,
    spec: input.spec,
    tier: input.tier,
    reason: input.reason,
    reusable: input.reusable,
    reraiseStatus: input.reraiseStatus,
    proposalPromiseGap: input.proposalPromiseGap,
    achievedTier: input.achievedTier,
    seedsBurned: input.seedsBurned ?? [],
    seedBurnReason: input.seedBurnReason,
    dryRun: input.dryRun ?? false,
    noMintOqs: input.noMintOqs ?? false,
    dischargedGates: input.dischargedGates ?? [],
  };
  if (!TIERS.includes(args.tier)) {
    throw new Error(`Invalid --tier: ${args.tier}. Must be one of ${TIERS.join("|")}`);
  }
  if (args.reusable !== undefined && !REUSABLE_VALUES.includes(args.reusable)) {
    throw new Error(`Invalid --reusable: ${args.reusable}. Must be one of ${REUSABLE_VALUES.join("|")}`);
  }
  if (args.reraiseStatus !== undefined && !RERAISE_STATUS_VALUES.includes(args.reraiseStatus)) {
    throw new Error(`Invalid --reraise-status: ${args.reraiseStatus}. Must be one of ${RERAISE_STATUS_VALUES.join("|")}`);
  }
  const repoRoot = input.repoRoot ?? findCausalSmithRoot(process.cwd());
  const { formalizationDir, formalizationKind, researchBankRoot, literatureBankRoot } =
    await import("../src/paths.js");
  const srcDir = formalizationDir(repoRoot, args.qid);
  const kind = formalizationKind(args.qid);

  if (!existsSync(srcDir)) {
    throw new Error(`Source directory not found: ${srcDir}`);
  }

  const statePath = await locateStateJson(srcDir, args.qid, args.spec);
  const stateRaw = await readFile(statePath, "utf8");
  const state = JSON.parse(stateRaw);

  if (state.banked === true) {
    throw new Error(`State.json already marked banked: ${statePath}. Refusing to re-bank.`);
  }

  // Every disclosed `substrate-gate` must be a REGISTERED gate node. A prose-only disclosure has
  // no machine-readable owner: "build before banking" goes unenforced, and the hand-written Lean
  // hypothesis is dropped by the next F2 re-scaffold. Only `accepted` is gated on this — the other
  // tiers exist precisely to park work that still carries debt.
  if (args.tier === "accepted") {
    const findings = auditSubstrateGates({
      addedAssumptions: Array.isArray(state.added_assumptions) ? state.added_assumptions : [],
      planNodes: await readNodesFor(srcDir, "plan.json"),
      graphNodes: await readNodesFor(srcDir, "graph.json"),
    });
    if (findings.length > 0) {
      // Errors carry their own fix: the label's suffix after the last `:` is the gate's identity
      // (node id or Lean name), which is what gate.ts takes as <node_id>.
      const lines = findings.map((f) => {
        const ident = f.label.split(":").pop() || f.label;
        return (
          `  - ${f.label}: ${f.reason}\n` +
          `      npx tsx tools/bin/gate.ts ${args.qid} ${args.spec} ${ident} --consumers <id1,id2> --class gated`
        );
      });
      throw new Error(
        `Refusing to bank ${args.qid}/${args.spec} as 'accepted': ${findings.length} disclosed ` +
          `substrate-gate(s) are not registered gate nodes.\n${lines.join("\n")}\n\n` +
          `Register each (command above), then DISCHARGE it once proven — or bank at a lower tier.\n` +
          `Pre-flight any time with: npx tsx tools/bin/gate.ts ${args.qid} ${args.spec} --audit`,
      );
    }

    // CITED source-match gate. The review loop escalates on a mismatch, but that check is
    // in-process only: `bank_entry.ts --tier accepted` and any resume re-entering at F5 would
    // otherwise bank a cited def that does not faithfully encode its source. `cited_checks` is the
    // durable record the F4 reviewer writes.
    const citedBad = citedBlockers(Array.isArray(state.cited_checks) ? state.cited_checks : []);
    if (citedBad.length > 0) {
      const rows = citedBad.map((c) => `  - ${c.name}: ${c.check_status}`).join("\n");
      throw new Error(
        `Refusing to bank ${args.qid}/${args.spec} as 'accepted': ${citedBad.length} cited def(s) ` +
          `failed the source-match gate.\n${rows}\n` +
          `Fix the Lean def or the citation and re-run F4 — never auto-rewrite a banked def.`,
      );
    }

    if (kind === "research") {
      const readStrict = async (label: string, candidates: string[]): Promise<unknown> => {
        const file = candidates.find((candidate) => existsSync(candidate));
        if (!file) throw new Error(`Refusing accepted banking: missing ${label} (${candidates.join(" or ")})`);
        try {
          return JSON.parse(await readFile(file, "utf8"));
        } catch (err) {
          throw new Error(`Refusing accepted banking: malformed ${label} at ${file}: ${err instanceof Error ? err.message : String(err)}`);
        }
      };
      const core = CoreSchema.parse(await readStrict("core.json", [path.join(srcDir, "discovery", "core.json")]));
      const plan = PlanSchema.parse(await readStrict("plan.json", [path.join(srcDir, "formalization", "plan.json"), path.join(srcDir, "plan.json")]));
      const graph = GraphSchema.parse(await readStrict("graph.json", [path.join(srcDir, "graph.json"), path.join(srcDir, "formalization", "graph.json")]));
      const leanDir = path.join(repoRoot, String(state.lean_subdir ?? ""));
      if (!existsSync(leanDir)) throw new Error(`Refusing accepted banking: Lean directory not found: ${leanDir}`);
      // Re-scan at BANK time, not just at F5. Banking is a deliberate step that can happen long
      // after F5 signed off, and the tree is editable in between (a repair, a rebase, a
      // concurrent run, a hand-edit). F5's scan is not bound to a source digest, so without this
      // an artifact that acquired a `sorry` or a cheat token after F5 is archived as `accepted`.
      const soundnessIssues = await bankSoundnessIssues(leanDir, repoRoot);
      if (soundnessIssues.length > 0) {
        throw new Error(
          `Refusing accepted banking: ${soundnessIssues.length} soundness issue(s) in the artifact ` +
            `(or its reachable CausalSmith.Mathlib closure) — the proof is not sorry-free/cheat-free ` +
            `NOW, whatever F5 saw earlier:\n  ${soundnessIssues.join("\n  ")}`,
        );
      }
      const declNames = (await parseLeanDecls(leanDir, { includeLemmas: true })).map((decl) => decl.name);
      const deliveryFindings = auditDelivery({
        core,
        plan,
        graph,
        leanDeclNames: declNames,
        stageCompleted: String(state.stage_completed ?? ""),
        requireFinalStage: true,
        receipts: Array.isArray(state.delivery_review_receipts)
          ? state.delivery_review_receipts as DeliveryReviewReceipt[]
          : [],
        requireReceipts: true,
      });
      deliveryFindings.push(...auditCitedReview({
        plan,
        graph,
        receipts: Array.isArray(state.cited_review_receipts)
          ? state.cited_review_receipts as CitedReviewReceipt[]
          : [],
      }));
      if (deliveryFindings.length > 0) {
        throw new Error(
          `Refusing to bank ${args.qid}/${args.spec} as 'accepted': undelivered delivery audit failed:\n` +
            deliveryFindings.map((finding) => `  - ${finding.code}${finding.node_id ? ` @ ${finding.node_id}` : ""}: ${finding.message}`).join("\n"),
        );
      }
    }
  }

  // Route by kind:
  //   research → `_bank/<tier>/<entry>` (tiered).
  //   study + tier=accepted → `_literature_bank/accepted/<entry>/`
  //     (symmetric with `_bank/accepted/`; routed by study-pipeline S5 on whole-
  //     paper success).
  //   study + tier=failed → `_literature_bank/_failed/<reason>/<entry>/`
  //     (parallel to study_bank.ts's run-level quarantine, but at theorem
  //     granularity). Requires `--reason` against LITERATURE_FAILURE_REASONS.
  //   study + any other tier → flat `_literature_bank/<entry>` (--tier is
  //     recorded in state.json/README frontmatter; novelty-tiering remains
  //     research-only).
  const studyFailed = kind === "study" && args.tier === "failed";
  const studyAccepted = kind === "study" && args.tier === "accepted";
  let literatureFailureReason: LiteratureFailureReason | undefined;
  if (studyFailed) {
    if (!args.reason || !(LITERATURE_FAILURE_REASONS as readonly string[]).includes(args.reason)) {
      throw new Error(
        `--tier failed for a study-mode qid requires --reason <r> where r is one of: ` +
          `${LITERATURE_FAILURE_REASONS.join(", ")}. Got: ${JSON.stringify(args.reason)}`,
      );
    }
    literatureFailureReason = args.reason as LiteratureFailureReason;
  }
  const destBase =
    kind === "research"
      ? path.join(researchBankRoot(repoRoot), args.tier)
      : studyFailed
        ? path.join(literatureBankRoot(repoRoot), "_failed", literatureFailureReason!)
        : studyAccepted
          ? path.join(literatureBankRoot(repoRoot), "accepted")
          : literatureBankRoot(repoRoot);
  const destDir = path.join(destBase, `${args.qid}_${args.spec}`);
  if (existsSync(destDir)) {
    throw new Error(`Destination already exists: ${destDir}. Refusing to overwrite.`);
  }

  const bankedOn = new Date().toISOString().slice(0, 10);
  const tierProp = tierAtProposal(state);
  const tierDeriv = await tierAtDerivation(srcDir, args.qid, args.spec);
  const reviewerGap = await proposalPromiseGapFromReviews(srcDir, args.qid, args.spec);
  const proposalPromiseGap = args.proposalPromiseGap ?? reviewerGap;
  const reusable: Reusable = args.reusable ?? reusableFromGap(proposalPromiseGap);
  const reraiseStatus: ReraiseStatus = args.reraiseStatus ?? "unknown";
  const requestedNoveltyTier = normalizeNoveltyTarget(state?.proposed_from?.novelty_target);
  const bankedNoveltyTier =
    args.achievedTier ??
    (await achievedTierFromDecisionLog(srcDir)) ??
    (args.tier === "accepted" ? requestedNoveltyTier : undefined);
  const bankedReason =
    args.reason ??
    `Auto-banked ${bankedOn}; tier_at_proposal=${tierProp}, tier_at_derivation=${tierDeriv}, novelty_target=${state?.proposed_from?.novelty_target ?? "unknown"}.`;

  // Build patched state.json (in-memory).
  const patched = {
    ...state,
    banked: true,
    banked_tier: args.tier,
    banked_on: bankedOn,
    banked_reason: bankedReason,
    banked_reusable: reusable,
    banked_proposal_promise_gap: proposalPromiseGap ?? null,
    ...(bankedNoveltyTier ? { banked_novelty_tier: bankedNoveltyTier } : {}),
  };

  // Re-bank of a reopened entry: bump the revision counter, accumulate the
  // discharged-gate history, and consume the `reopened_from` marker (the entry
  // is banked again, no longer mid-discharge).
  const discharge = dischargeMetadata(state, args.dischargedGates ?? []);
  if (discharge) {
    patched.revision = discharge.revision;
    patched.discharged_gates = discharge.discharged_gates;
    delete patched.reopened_from;
  }

  // Seeds-burned wiring: flag seed_details[i] and emit top-level seeds_burned.
  const seedsBurnedEntries: Array<{ index: number; one_liner: string; reason: string }> = [];
  if (args.seedsBurned.length > 0) {
    const details = patched.proposed_from?.seed_details as Array<any> | undefined;
    if (!details) {
      console.warn(`warning: --seeds-burned given but state.proposed_from.seed_details is missing; emitting top-level seeds_burned only.`);
    }
    for (const idx of args.seedsBurned) {
      const seedDetail = details?.[idx];
      const oneLiner =
        seedDetail?.one_line ??
        patched.proposed_from?.seed_list?.[idx] ??
        `(seed index ${idx} — one-liner not found in state.json)`;
      const reason = args.seedBurnReason ?? bankedReason;
      if (seedDetail) {
        seedDetail.burned = true;
        seedDetail.burned_reason = reason;
        seedDetail.burned_on = bankedOn;
      }
      seedsBurnedEntries.push({ index: idx, one_liner: oneLiner, reason });
    }
    patched.seeds_burned = seedsBurnedEntries.map((s) => ({ ...s, burned_on: bankedOn }));
  }

  // Mint OpenQuestion nodes for any failed theorem entries.
  // Runs in --dry-run mode too — minting is content-additive and never
  // touches the source dir; but the patched state.json is only persisted
  // outside dry-run, so dry-run reports without writing.
  //
  // Stage 0.5 gate: theorems whose stage_completed is <= "0.5" are SKIPPED;
  // they remain recorded in the per-run fail bank but do not produce an OQ.
  // See src/shared/mint_failed_theorem_oq.ts for the rationale.
  type TheoremDispatch =
    | { theorem_local_id: string; outcome: "minted"; oq_id: string; existed: boolean }
    | { theorem_local_id: string; outcome: "skipped"; reason: string }
    | { theorem_local_id: string; outcome: "dry-run"; oq_id_would_be: string };

  if (!args.noMintOqs && Array.isArray(patched.theorems)) {
    const graphRoot = path.join(repoRoot, "doc", "study");
    const dispatches: TheoremDispatch[] = [];
    const stuckTheorems: string[] = [];
    const { mintFailedTheoremOpenQuestion } = await import(
      "../src/shared/mint_failed_theorem_oq.js"
    );
    for (let i = 0; i < patched.theorems.length; i++) {
      const t = patched.theorems[i] as any;
      // Defensive log for in-flight non-terminal entries — banking a run with
      // stuck theorems usually means something was abandoned mid-pipeline.
      // We don't mint OQs for them (stuck != "valid claim, unproved"; the work
      // may still resume), but the operator should see them at bank time.
      if (t?.status === "stuck" || t?.status === "in_progress" || t?.status === "pending") {
        stuckTheorems.push(`${t.theorem_local_id} (status=${t.status})`);
        continue;
      }
      if (t?.status !== "failed") continue;
      if (typeof t.minted_oq_id === "string" && t.minted_oq_id.length > 0) continue;
      if (args.dryRun) {
        dispatches.push({
          theorem_local_id: t.theorem_local_id,
          outcome: "dry-run",
          oq_id_would_be: `oq_failed_${args.qid}_${args.spec}_${t.theorem_local_id}`,
        });
        continue;
      }
      const res = await mintFailedTheoremOpenQuestion({
        qid: args.qid,
        spec: args.spec,
        theorem: t,
        graphRoot,
      });
      if (res.kind === "skipped") {
        dispatches.push({
          theorem_local_id: t.theorem_local_id,
          outcome: "skipped",
          reason: res.reason,
        });
        continue;
      }
      t.minted_oq_id = res.oq_id;
      dispatches.push({
        theorem_local_id: t.theorem_local_id,
        outcome: "minted",
        oq_id: res.oq_id,
        existed: res.kind === "existed",
      });
    }
    if (dispatches.length > 0) {
      console.error(`failed-theorem dispatch (${dispatches.length} entries):`);
      for (const d of dispatches) {
        if (d.outcome === "minted") {
          console.error(`  - ${d.theorem_local_id} -> ${d.oq_id}${d.existed ? " (existed)" : ""}`);
        } else if (d.outcome === "skipped") {
          console.error(`  - ${d.theorem_local_id} -> skipped (${d.reason})`);
        } else {
          console.error(`  - ${d.theorem_local_id} -> would mint ${d.oq_id_would_be} (dry-run)`);
        }
      }
    }
    if (stuckTheorems.length > 0) {
      console.error(
        `warning: ${stuckTheorems.length} non-terminal theorem(s) at bank time ` +
          `(not minted as OQs; consider resuming or marking failed before re-banking):\n` +
          stuckTheorems.map((s) => `  - ${s}`).join("\n"),
      );
    }
    // (No globalThis stash needed: renderReadme below re-derives the dispatch
    // status from patched.theorems directly, which has been mutated in-place
    // with minted_oq_id by this loop.)
  }

  const readme = renderReadme({
    state: patched,
    tier: args.tier,
    qid: args.qid,
    spec: args.spec,
    bankedOn,
    bankedReason,
    tierProp,
    tierDeriv,
    reusable,
    reraiseStatus,
    proposalPromiseGap,
    bankedNoveltyTier,
    seedsBurnedEntries,
  });

  if (args.dryRun) {
    return {
      destDir,
      bankedOn,
      tierProp,
      tierDeriv,
      reusable,
      proposalPromiseGap,
      bankedNoveltyTier,
      seedsBurnedIndices: args.seedsBurned,
      __dryRun: true,
      __statePath: statePath,
      __srcDir: srcDir,
    } as BankEntryResult & { __dryRun: true; __statePath: string; __srcDir: string };
  }

  // 1. Write patched state.json back in place (still under srcDir for now).
  await writeFile(statePath, JSON.stringify(patched, null, 2) + "\n", "utf8");

  // 2. Move the source directory to the bank destination. For the study-mode
  // failed branch, route through `routeToBank` so a BANK_REASON.md is dropped
  // alongside the README (parallel to study_bank.ts's run-level quarantine).
  // For every other tier/kind, the README itself is the canonical record.
  if (studyFailed) {
    await routeToBank({
      srcDir,
      destDir,
      reason: literatureFailureReason!,
      note: bankedReason,
      identifier: `${args.qid}_${args.spec}`,
    });
  } else {
    await mkdir(destBase, { recursive: true });
    await rename(srcDir, destDir);
  }

  // 3. Write README scaffold at the new location.
  await writeFile(path.join(destDir, "README.md"), readme, "utf8");

  return {
    destDir,
    bankedOn,
    tierProp,
    tierDeriv,
    reusable,
    proposalPromiseGap,
    bankedNoveltyTier,
    seedsBurnedIndices: args.seedsBurned,
  };
}

/**
 * Re-bank bookkeeping for an entry that was reopened (via `reopenEntry`) and is
 * now being banked again. Returns the `revision` counter (bumped once per
 * reopen→re-bank cycle) and the accumulated `discharged_gates` history, or
 * `null` when the entry was never reopened (a normal first bank). The caller
 * merges the result into the patched state and drops the consumed
 * `reopened_from` marker.
 */
export function dischargeMetadata(
  priorState: { reopened_from?: unknown; revision?: number; discharged_gates?: unknown },
  dischargedGates: string[],
): { revision: number; discharged_gates: string[] } | null {
  if (!priorState.reopened_from) return null;
  const prior = Array.isArray(priorState.discharged_gates)
    ? (priorState.discharged_gates as string[])
    : [];
  return {
    revision: (priorState.revision ?? 0) + 1,
    discharged_gates: [...prior, ...dischargedGates],
  };
}

export interface ReopenEntryArgs {
  qid: string;
  spec: string;
  /** Bank tier the entry lives under. Defaults to `accepted` (the discharge use case). */
  tier?: Tier;
  repoRoot?: string;
  /** Report what would move without touching the filesystem. */
  dryRun?: boolean;
}

export interface ReopenEntryResult {
  workingDir: string;
  bankDir: string;
  priorTier: Tier;
}

/**
 * Inverse of `bankEntry`'s move: pull a banked entry back to its working
 * `formalizationDir(qid)` location and clear `banked` so the normal toolchain
 * (`gate.ts --ungate`, `--resume --from-stage F4`) can operate on it again.
 *
 * Conservative like `bankEntry`: refuses if the working dir already exists
 * (never clobber an in-flight run — also the double-reopen guard), refuses if
 * no banked entry is found, and refuses a dir not marked `banked:true`.
 *
 * The `reopened_from` record it stamps into state.json is the crash-safety
 * marker: an entry moved out of the bank but not yet re-banked is always
 * identifiable as a reopened accepted entry mid-discharge.
 */
export async function reopenEntry(input: ReopenEntryArgs): Promise<ReopenEntryResult> {
  const tier: Tier = input.tier ?? "accepted";
  const repoRoot = input.repoRoot ?? findCausalSmithRoot(process.cwd());
  const { formalizationDir, formalizationKind, researchBankRoot, literatureBankRoot } =
    await import("../src/paths.js");

  // Mirror bankEntry's destBase routing for the success tiers (research →
  // tiered `_bank/<tier>/`; study-accepted → `_literature_bank/accepted/`;
  // other study tiers → flat `_literature_bank/`).
  const kind = formalizationKind(input.qid);
  const destBase =
    kind === "research"
      ? path.join(researchBankRoot(repoRoot), tier)
      : tier === "accepted"
        ? path.join(literatureBankRoot(repoRoot), "accepted")
        : literatureBankRoot(repoRoot);
  const bankDir = path.join(destBase, `${input.qid}_${input.spec}`);
  if (!existsSync(bankDir)) {
    throw new Error(`No banked entry to reopen: ${bankDir}`);
  }

  const workingDir = formalizationDir(repoRoot, input.qid);
  if (existsSync(workingDir)) {
    throw new Error(
      `Working dir already exists: ${workingDir}. Refusing to reopen over an in-flight run ` +
        `(resolve or archive it first).`,
    );
  }

  const statePath = await locateStateJson(bankDir, input.qid, input.spec);
  const state = JSON.parse(await readFile(statePath, "utf8"));
  if (state.banked !== true) {
    throw new Error(
      `Refusing to reopen: ${statePath} is not marked banked (banked=${JSON.stringify(state.banked)}).`,
    );
  }

  const priorTier: Tier = (state.banked_tier as Tier) ?? tier;
  const patched = {
    ...state,
    banked: false,
    reopened_from: {
      tier: priorTier,
      banked_on: state.banked_on ?? null,
      reopened_on: new Date().toISOString(),
    },
  };

  if (input.dryRun) {
    return { workingDir, bankDir, priorTier };
  }

  await mkdir(path.dirname(workingDir), { recursive: true });
  // state.json travels with the dir; capture its in-dir relative path first.
  const stateRel = path.relative(bankDir, statePath);
  await rename(bankDir, workingDir);
  await writeFile(
    path.join(workingDir, stateRel),
    JSON.stringify(patched, null, 2) + "\n",
    "utf8",
  );

  return { workingDir, bankDir, priorTier };
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const repoRoot = findCausalSmithRoot(process.cwd());
  const { formalizationDir } = await import("../src/paths.js");
  const srcDir = formalizationDir(repoRoot, args.qid);
  const statePath = await locateStateJson(srcDir, args.qid, args.spec);
  const result = (await bankEntry({
    qid: args.qid,
    spec: args.spec,
    tier: args.tier,
    reason: args.reason,
    reusable: args.reusable,
    reraiseStatus: args.reraiseStatus,
    proposalPromiseGap: args.proposalPromiseGap,
    achievedTier: args.achievedTier,
    seedsBurned: args.seedsBurned,
    seedBurnReason: args.seedBurnReason,
    dryRun: args.dryRun,
    noMintOqs: args.noMintOqs,
    repoRoot,
  })) as BankEntryResult & { __dryRun?: boolean };

  if (result.__dryRun) {
    console.log(`[dry-run] would patch state.json: ${statePath}`);
    console.log(`[dry-run] would move directory: ${srcDir} -> ${result.destDir}`);
    console.log(`[dry-run] would write README:   ${path.join(result.destDir, "README.md")}`);
    console.log(`[dry-run] tier_at_proposal=${result.tierProp}, tier_at_derivation=${result.tierDeriv}`);
    console.log(`[dry-run] proposal_promise_gap=${result.proposalPromiseGap ?? "(none)"}, reusable=${result.reusable}`);
    console.log(`[dry-run] banked_novelty_tier=${result.bankedNoveltyTier ?? "unknown"}`);
    console.log(`[dry-run] seeds_burned indices: ${args.seedsBurned.join(",") || "(none)"}`);
    return;
  }
  console.log(`banked: ${args.qid}/${args.spec} -> ${path.relative(repoRoot, result.destDir)}`);
  console.log(`  tier_at_proposal=${result.tierProp}, tier_at_derivation=${result.tierDeriv}`);
  console.log(`  proposal_promise_gap=${result.proposalPromiseGap ?? "(none)"}, reusable=${result.reusable}`);
  console.log(`  banked_novelty_tier=${result.bankedNoveltyTier ?? "unknown"}`);
  if (result.seedsBurnedIndices.length > 0) {
    console.log(`  seeds_burned: ${result.seedsBurnedIndices.join(",")}`);
  }
  console.log(`  README scaffold: ${path.relative(repoRoot, path.join(result.destDir, "README.md"))} (gap_reasons + reusable_artifacts left as TODO)`);
}

// Run as CLI when invoked directly (vitest imports this module to test bankEntry).
const invokedDirectly =
  import.meta.url === `file://${process.argv[1]}` ||
  process.argv[1]?.endsWith("bank_entry.ts") ||
  process.argv[1]?.endsWith("bank_entry.js");
if (invokedDirectly) {
  main().catch((err) => {
    console.error(err instanceof Error ? err.message : err);
    process.exit(1);
  });
}
