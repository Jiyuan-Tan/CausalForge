import { readdir, readFile, stat } from "node:fs/promises";
import path from "node:path";
import { isStateFileName, researchBankRoot } from "./paths.js";
import { UPGRADE_PARENT_TIERS } from "./types.js";
import type { UpgradeAxis, UpgradeFrom } from "./types.js";
import {
  normalizeNoveltyTarget,
  REVIEWER_TIER_RANK,
  type NoveltyTarget,
} from "./novelty.js";

export type ParentTier = (typeof UPGRADE_PARENT_TIERS)[number];

export interface ParentEntry {
  parent_qid: string;
  parent_spec: string;
  tier: ParentTier;
  /** Achieved novelty tier frozen at bank time; upgrade targets must be strictly higher. */
  banked_novelty_tier: NoveltyTarget;
  topic: string;
  cluster: "panel" | "exactid" | "partialid" | "stat" | "experimentation" | "scm" | null;
  /** Verbatim §1–§13 of the parent's `*_proposal.tex` (truncated to MAX_TEX_BYTES). */
  proposal_tex: string;
  /** Verbatim Stage 0 derivation `*.tex` if it exists (truncated). */
  derivation_tex: string;
  /** Banked README.md, verbatim (small file). */
  readme_md: string;
  /** Parent's Step 0a literature map, if recorded in state.json. */
  literature_map: string;
}

const MAX_TEX_BYTES = 80 * 1024;

const UPGRADE_TIERS: ReadonlyArray<ParentTier> = UPGRADE_PARENT_TIERS;
// `downgraded` parents are now allowed — that is the re-test escape hatch
// for runs whose D0 derivation drifted (kernel_substituted, tier_genuinely_below).
// `failed`/`legacy` remain blocked: failed parents never passed D-0.5, and
// legacy entries predate the reviewer system.
const REJECTED_TIERS: ReadonlyArray<string> = ["failed", "legacy"];

export async function loadParentEntry(
  repoRoot: string,
  args: { parent_qid: string; parent_spec: string },
): Promise<ParentEntry> {
  const entryName = `${args.parent_qid}_${args.parent_spec}`;
  // --upgrade is research-mode only: the literature bank has no novelty
  // tiers and the upgrade flow is built around the bank tier split.
  const bankRoot = researchBankRoot(repoRoot);

  for (const rejected of REJECTED_TIERS) {
    const candidate = path.join(bankRoot, rejected, entryName);
    if (await dirExists(candidate)) {
      throw new Error(
        `Parent ${entryName} is in _bank/${rejected}/, but --upgrade requires an accepted or downgraded tier parent. Pick a different parent.`,
      );
    }
  }

  for (const tier of UPGRADE_TIERS) {
    const dir = path.join(bankRoot, tier, entryName);
    if (!(await dirExists(dir))) continue;
    return readParent(dir, tier, args);
  }

  throw new Error(
    `Parent ${entryName} not found in _bank/accepted/ or _bank/downgraded/. Check spelling or run \`ls CausalSmith/doc/research/_bank/{accepted,downgraded}/\`.`,
  );
}

async function readParent(
  dir: string,
  tier: ParentTier,
  args: { parent_qid: string; parent_spec: string },
): Promise<ParentEntry> {
  const entryName = `${args.parent_qid}_${args.parent_spec}`;
  const readmePath = path.join(dir, "README.md");
  const readme = await readFile(readmePath, "utf8").catch(() => "");
  const topic = matchFrontmatter(readme, "topic") ?? "(unknown)";

  let cluster: ParentEntry["cluster"] = null;
  let literature_map = "";
  let state: Record<string, any> | null = null;
  const files = await readdir(dir).catch(() => []);
  const stateFile = files.find(isStateFileName);
  if (stateFile) {
    try {
      const stateRaw = await readFile(path.join(dir, stateFile), "utf8");
      const parsed = JSON.parse(stateRaw) as Record<string, any>;
      state = parsed;
      const c = parsed?.proposed_from?.cluster;
      if (c === "panel" || c === "exactid" || c === "partialid" || c === "stat" || c === "experimentation" || c === "scm") cluster = c;
      const lm = parsed?.proposed_from?.literature_map;
      if (typeof lm === "string") literature_map = lm;
    } catch {
      /* tolerate malformed parent state.json */
    }
  }
  if (cluster === null) {
    const qid = args.parent_qid.toLowerCase();
    if (qid.startsWith("eid_")) cluster = "exactid";
    else if (qid.startsWith("pid_")) cluster = "partialid";
    else if (qid.startsWith("stat_")) cluster = "stat";
    else if (qid.startsWith("exp_")) cluster = "experimentation";
    else if (qid.startsWith("scm_")) cluster = "scm";
    else if (qid.startsWith("panel_")) cluster = "panel";
  }

  // Current bank entries preserve the live run directory verbatim. Keep the
  // pre-2026 flattened names as fallbacks so upgrades work across both layouts.
  const proposal_tex = await readFirstTrimmed([
    path.join(dir, "discovery", "proposal.tex"),
    path.join(dir, "proposal.tex"),
    path.join(dir, `${entryName}_proposal.tex`),
  ]);
  const derivation_tex = await readFirstTrimmed([
    path.join(dir, "discovery", "writeup.tex"),
    path.join(dir, "writeup.tex"),
    path.join(dir, `${entryName}.tex`),
  ]);
  const banked_novelty_tier = await resolveBankedNoveltyTier({
    dir,
    tier,
    readme,
    state,
  });

  return {
    parent_qid: args.parent_qid,
    parent_spec: args.parent_spec,
    tier,
    banked_novelty_tier,
    topic,
    cluster,
    proposal_tex,
    derivation_tex,
    readme_md: readme,
    literature_map,
  };
}

async function resolveBankedNoveltyTier(args: {
  dir: string;
  tier: ParentTier;
  readme: string;
  state: Record<string, any> | null;
}): Promise<NoveltyTarget> {
  const explicit =
    normalizeNoveltyTarget(matchFrontmatter(args.readme, "banked_novelty_tier")) ??
    normalizeNoveltyTarget(matchFrontmatter(args.readme, "achieved_tier")) ??
    normalizeNoveltyTarget(args.state?.banked_novelty_tier);
  if (explicit) return explicit;

  // Downgraded runs record the achieved tier in the terminal/validity receipt.
  // Read newest-first; direct JSON metadata wins, with the canonical Codex
  // receipt line as a backward-compatible fallback.
  const decisionLogs = [
    path.join(args.dir, "orchestrator", "decision_log.jsonl"),
    path.join(args.dir, "decision_log.jsonl"),
  ];
  for (const log of decisionLogs) {
    try {
      const lines = (await readFile(log, "utf8")).trim().split("\n").filter(Boolean);
      for (let i = lines.length - 1; i >= 0; i--) {
        const row = JSON.parse(lines[i]) as Record<string, unknown>;
        const direct = normalizeNoveltyTarget(
          typeof row.achieved_tier === "string" ? row.achieved_tier : undefined,
        );
        if (direct) return direct;
        const codex = typeof row.codex === "string" ? row.codex : "";
        const match = codex.match(/ACHIEVED_TIER:\s*(incremental|subfield|field|flagship)/i);
        const fromReceipt = normalizeNoveltyTarget(match?.[1]?.toLowerCase());
        if (fromReceipt) return fromReceipt;
      }
    } catch {
      // Try the next supported log location.
    }
  }

  // Accepted entries reached F5 at their requested floor, so that floor is a
  // conservative banked tier even when the referee assessed them still higher.
  if (args.tier === "accepted") {
    const floor =
      normalizeNoveltyTarget(matchFrontmatter(args.readme, "novelty_target")) ??
      normalizeNoveltyTarget(args.state?.proposed_from?.novelty_target);
    if (floor) return floor;
  }

  throw new Error(
    `Parent bank entry ${args.dir} has no recoverable achieved novelty tier. ` +
      `Add \`banked_novelty_tier: incremental|subfield|field|flagship\` to README.md ` +
      `before using --upgrade.`,
  );
}

/** Require an upgrade target to be strictly above the parent's achieved banked tier. */
export function assertUpgradeNoveltyTarget(
  target: NoveltyTarget | string | undefined,
  parent: ParentEntry,
): NoveltyTarget {
  const normalized = normalizeNoveltyTarget(target);
  if (!normalized) {
    throw new Error(
      `--upgrade requires --novelty <incremental|subfield|field|flagship>; ` +
        `parent ${parent.parent_qid}_${parent.parent_spec} is ${parent.banked_novelty_tier}.`,
    );
  }
  if (REVIEWER_TIER_RANK[normalized] <= REVIEWER_TIER_RANK[parent.banked_novelty_tier]) {
    throw new Error(
      `--upgrade target '${normalized}' must be strictly above parent ` +
        `${parent.parent_qid}_${parent.parent_spec}'s banked novelty tier ` +
        `'${parent.banked_novelty_tier}'.`,
    );
  }
  return normalized;
}

async function dirExists(p: string): Promise<boolean> {
  try {
    const s = await stat(p);
    return s.isDirectory();
  } catch {
    return false;
  }
}

async function readTrimmed(p: string): Promise<string> {
  try {
    const raw = await readFile(p, "utf8");
    return raw.length <= MAX_TEX_BYTES
      ? raw
      : raw.slice(0, MAX_TEX_BYTES) + "\n\n% [truncated by upgrade.loadParentEntry]\n";
  } catch {
    return "";
  }
}

async function readFirstTrimmed(candidates: string[]): Promise<string> {
  for (const candidate of candidates) {
    const value = await readTrimmed(candidate);
    if (value.length > 0) return value;
  }
  return "";
}

function matchFrontmatter(md: string, key: string): string | null {
  if (!md.startsWith("---\n")) return null;
  const end = md.indexOf("\n---", 4);
  if (end < 0) return null;
  const body = md.slice(4, end);
  const escapedKey = key.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`^${escapedKey}:\\s*(.*)$`, "m");
  const m = body.match(re);
  if (!m) return null;
  const raw = m[1].trim();
  if (raw.startsWith('"') || raw.startsWith("'")) {
    try {
      return JSON.parse(raw.replace(/^'(.*)'$/, '"$1"'));
    } catch {
      return raw.replace(/^["']|["']$/g, "");
    }
  }
  return raw;
}

// ────────────────────────────────────────────────────────────────────────
// Per-axis delta rubric (used by both prompts and any in-code validation).
// ────────────────────────────────────────────────────────────────────────

export const UPGRADE_AXIS_RUBRIC: Record<UpgradeAxis, string> = {
  computation:
    "Adds a quantitative bound, closed-form expression, sharp rate, or explicit boundary case that the parent stated only qualitatively or left implicit. Pure restatements or re-derivations of parent's bound fail.",
  estimation:
    "Adds a named estimator with an asymptotic property (consistency, asymptotic-normality, convergence rate, double-robustness) tied to a sharp population target from the parent. A bare 'one could estimate this' fails.",
  generalization:
    "Strictly widens the parent's assumption class OR weakens one named premise, and proves the parent kernel reduces to a corner case. A relabelling, a CATE/ATT restatement of an ATE result, or a T=2→general-T extension fails unless paired with a phenomenon (sign-flip, regime change) that does not appear in parent.",
  mechanism:
    "Decomposes or isolates an effect that the parent bundled — e.g. separates a direct from an indirect channel, factors a bound into a structural and a sampling component. A label change with no new identifying restriction fails.",
};

export function renderUpgradeContextBlock(args: {
  upgradeFrom: UpgradeFrom;
  parent: ParentEntry;
  directiveText: string;
  targetTier?: NoveltyTarget;
}): string {
  const { upgradeFrom, parent, directiveText, targetTier } = args;
  const lines: string[] = [];
  if (directiveText.trim().length > 0) {
    lines.push(directiveText.trim(), "");
  }
  lines.push(
    "=== UPGRADE CONTEXT (load-bearing — this run targets a strictly higher novelty tier than its banked parent) ===",
    `parent_qid: ${upgradeFrom.parent_qid}`,
    `parent_spec: ${upgradeFrom.parent_spec}`,
    `parent_tier: ${parent.tier}`,
    `parent_banked_novelty_tier: ${parent.banked_novelty_tier}`,
    `upgrade_target_tier: ${targetTier ?? "(validated by orchestrator)"}`,
    `parent_topic: ${parent.topic}`,
    `parent_cluster: ${parent.cluster ?? "(unknown — recover from §2)"}`,
    `upgrade_axis: ${upgradeFrom.upgrade_axis}`,
    `axis_rubric: ${UPGRADE_AXIS_RUBRIC[upgradeFrom.upgrade_axis]}`,
    "",
    "Your kernel must deliver on the declared upgrade_axis vs the parent. The reviewer",
    "(Stage -0.5) will NOT flag similarity to the parent — but it will run the axis_rubric",
    "above and REJECT a draft whose declared axis is not delivered. Similarity to any",
    "non-parent catalogue entry still triggers normal N-repo / N-pub rejection.",
    ...(parent.tier === "downgraded"
      ? [
          "",
          "Parent tier is `downgraded`: parent passed D-0.5 novelty review but its D0",
          "derivation drifted (typically `proposal_promise_gap: kernel_substituted` or",
          "`tier_genuinely_below`). The parent's *proposed* kernel is the substrate; do",
          "NOT treat the parent's *derived* result as a load-bearing premise. Read the",
          "parent README's `gap_reasons[]` and `proof_attempt_summary` and ensure the",
          "upgrade either (a) attacks the same proposed kernel with sharper machinery,",
          "or (b) pivots to a kernel the parent's derivation never reached. Repeating",
          "the parent's substituted kernel will be flagged by D-0.5 as not novel.",
        ]
      : []),
    "",
    "You SHOULD reuse the parent's literature_map (already loaded below) as Step 0a",
    "substrate; add at least one new published anchor that pins the upgrade axis to the",
    "frontier (an open problem in the literature that the upgrade resolves, a tension the",
    "parent did not address, or a recent paper whose claim the upgrade refines).",
    "",
    "You MUST anchor in the SAME cluster as the parent (cluster=" +
      (parent.cluster ?? "infer") +
      "); a cross-cluster pivot is a different question, not an upgrade.",
    "",
    "=== PARENT README (frontmatter + body) ===",
    parent.readme_md.slice(0, 4096),
    "=== END PARENT README ===",
    "",
    "=== PARENT PROPOSAL .tex (verbatim, possibly truncated) ===",
    parent.proposal_tex,
    "=== END PARENT PROPOSAL .tex ===",
  );
  if (parent.derivation_tex) {
    lines.push(
      "",
      "=== PARENT DERIVATION .tex (Stage 0 output, verbatim, possibly truncated) ===",
      parent.derivation_tex,
      "=== END PARENT DERIVATION .tex ===",
    );
  }
  if (parent.literature_map) {
    lines.push(
      "",
      "=== PARENT LITERATURE MAP (Step 0a substrate; verify bibkeys, add ≥1 new anchor) ===",
      parent.literature_map,
      "=== END PARENT LITERATURE MAP ===",
    );
  }
  lines.push("=== END UPGRADE CONTEXT ===");
  return lines.join("\n");
}
