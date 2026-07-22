/**
 * Bank query helpers.
 *
 * The result bank under `doc/research/_bank/{accepted,downgraded,failed,
 * legacy}/<qid>_<spec>/` is read by the pipeline at three points:
 *
 *   - **Cold-start proposal stage (`stage_neg1_2`)**: after Codex returns
 *     a fresh seed_list / seed_details, we filter out any seed whose
 *     anchor_paper.bibkey OR one_line was previously burned (logged in a
 *     banked entry under `seeds_burned[]`). This prevents the proposer from
 *     re-proposing an angle that a prior run already refuted at the kernel
 *     level.
 *
 *   - **Pivot proposal stage**: same filter is applied to the
 *     `seedList` carried into the pivot prompt.
 *
 *   - **Cold-start literature-review step (Step 0a)**: `loadReusableArtifacts`
 *     surfaces hand-curated artifacts from prior banked runs whose anchor
 *     topic / qid-cluster relates to the current run. `literature_map`
 *     content is loaded verbatim (from `proposed_from.literature_map` in the
 *     banked state.json), saving the proposer a full Step 0a; non-literature
 *     artifacts (lp_setup, witness, counterexample) are surfaced as pointers
 *     only, so the proposer can cite them but cannot lift them as the kernel.
 *
 * The bank is read on-demand (no separate registry file). Banked state.json
 * files carry a `seeds_burned: [{index, one_liner, anchor_bibkey?, reason,
 * burned_on}]` top-level array, written by `bin/bank_entry.ts --seeds-burned`.
 * Banked README.md files carry YAML frontmatter with `reusable_artifacts:`
 * filled in by hand at banking time.
 *
 * Matching is intentionally conservative: an exact anchor_bibkey match OR an
 * exact one_line string match (for seeds), and exact-topic / shared-cluster
 * match (for artifacts). We do NOT do fuzzy topic matching — false positives
 * there would silently shrink the seed frontier or muddy the prompt across
 * unrelated runs. False negatives (a paraphrased seed that should have been
 * filtered) are caught by Stage -0.5 reviewer feedback, which still has the
 * burned seeds in its context block.
 */
import { readdir, readFile, stat } from "node:fs/promises";
import path from "node:path";
import { isStateFileName, researchBankRoot } from "../paths.js";

export interface BurnedSeed {
  /** Seed index in the originating run's seed_list. */
  index: number;
  /** Verbatim one-liner from seed_list[index]. */
  one_liner: string;
  /** Anchor paper bibkey if available (preferred matching key). */
  anchor_bibkey?: string;
  /** Reason recorded at banking time. */
  reason: string;
  /** ISO date (YYYY-MM-DD) when this seed was burned. */
  burned_on: string;
  /** qid_spec of the originating run, for traceability in logs. */
  source: string;
}

/** Aggregate every burned seed across the bank. Returns [] if no bank yet.
 *  Walks only refuted-tier directories — see {@link BURNED_SEED_TIER_DIRS}.
 *  Research-bank only: burned seeds are a proposer-output concept and the
 *  literature bank has no tier structure. */
export async function loadBurnedSeeds(repoRoot: string): Promise<BurnedSeed[]> {
  const bankRoot = researchBankRoot(repoRoot);
  const out: BurnedSeed[] = [];
  let tiers: string[];
  try {
    tiers = await readdir(bankRoot);
  } catch {
    return out;
  }
  for (const tier of tiers) {
    if (!(BURNED_SEED_TIER_DIRS as readonly string[]).includes(tier)) continue;
    const tierDir = path.join(bankRoot, tier);
    let s;
    try { s = await stat(tierDir); } catch { continue; }
    if (!s.isDirectory()) continue;
    let entries: string[];
    try { entries = await readdir(tierDir); } catch { continue; }
    for (const entry of entries) {
      const entryDir = path.join(tierDir, entry);
      let st;
      try { st = await stat(entryDir); } catch { continue; }
      if (!st.isDirectory()) continue;
      let files: string[];
      try { files = await readdir(entryDir); } catch { continue; }
      const stateFile = files.find(isStateFileName);
      if (!stateFile) continue;
      let parsed: any;
      try {
        parsed = JSON.parse(await readFile(path.join(entryDir, stateFile), "utf8"));
      } catch { continue; }
      const burned = parsed?.seeds_burned;
      if (!Array.isArray(burned)) continue;
      const details = parsed?.proposed_from?.seed_details as Array<any> | undefined;
      for (const b of burned) {
        if (typeof b !== "object" || b === null) continue;
        const idx = typeof b.index === "number" ? b.index : -1;
        const detail = details?.[idx];
        out.push({
          index: idx,
          one_liner: String(b.one_liner ?? detail?.one_line ?? ""),
          anchor_bibkey: String(b.anchor_bibkey ?? detail?.anchor_paper?.bibkey ?? "") || undefined,
          reason: String(b.reason ?? ""),
          burned_on: String(b.burned_on ?? parsed?.banked_on ?? ""),
          source: entry,
        });
      }
    }
  }
  return out;
}

/**
 * Filter a fresh seed_list / seed_details against the burned-seed registry.
 *
 * Matching rules (any one triggers a drop):
 *   - `seed_details[i].anchor_paper.bibkey` exactly equals a burned
 *     `anchor_bibkey` (the strong signal — same anchor paper, same kernel).
 *   - `seed_list[i]` (the one_liner string) exactly equals a burned `one_liner`.
 *
 * Returns the kept lists in original order plus a `dropped` array suitable
 * for logging to `pipeline.jsonl`. `seedDetails` may be undefined (revise/
 * pivot prompts may not carry per-seed metadata); matching falls back to
 * one_liner only.
 */
export function filterBurnedSeeds(args: {
  seedList: string[];
  seedDetails?: Array<Record<string, unknown>>;
  burned: BurnedSeed[];
}): {
  seedList: string[];
  seedDetails?: Array<Record<string, unknown>>;
  dropped: Array<{ index: number; one_liner: string; matched_burned: BurnedSeed }>;
} {
  const dropped: Array<{ index: number; one_liner: string; matched_burned: BurnedSeed }> = [];
  const keepIdx: boolean[] = args.seedList.map((oneLiner, i) => {
    const detail = args.seedDetails?.[i];
    const bibkey = (detail?.anchor_paper as any)?.bibkey;
    for (const b of args.burned) {
      const bibkeyMatch = bibkey && b.anchor_bibkey && bibkey === b.anchor_bibkey;
      const oneLinerMatch = b.one_liner && oneLiner === b.one_liner;
      if (bibkeyMatch || oneLinerMatch) {
        dropped.push({ index: i, one_liner: oneLiner, matched_burned: b });
        return false;
      }
    }
    return true;
  });
  const kept: string[] = [];
  const keptDetails: Array<Record<string, unknown>> = [];
  for (let i = 0; i < args.seedList.length; i++) {
    if (keepIdx[i]) {
      kept.push(args.seedList[i]);
      if (args.seedDetails?.[i]) keptDetails.push(args.seedDetails[i]);
    }
  }
  return {
    seedList: kept,
    seedDetails: args.seedDetails ? keptDetails : undefined,
    dropped,
  };
}

// ─────────────────────────────────────────────────────────────────────────────
// Reusable artifacts from related banked runs.
// ─────────────────────────────────────────────────────────────────────────────

export type ArtifactKind = "literature_map" | "lp_setup" | "witness" | "counterexample" | "other";
export type BankTier = "accepted" | "downgraded" | "failed" | "legacy";
export type ArtifactMatch = "strict" | "related";

/**
 * Study-mode failure reason taxonomy for `--tier failed` entries in the
 * literature bank (`_literature_bank/_failed/<reason>/<bt_id>/`). Validated by
 * `bin/bank_entry.ts` when a study-mode qid is banked at the failed tier.
 *
 * Distinct from `bin/study_bank.ts`'s `REASONS` (study-pipeline *run*-level
 * quarantine, granularity = `run_id`); this taxonomy is theorem-level
 * (granularity = `bt_id = <qid>_<spec>`) and tracks where in the causalsmith
 * pipeline the formalization gave up.
 */
export const LITERATURE_FAILURE_REASONS = [
  // Stage 1.5 reviewer rejected the NL formalization plan beyond retry budget.
  "nl_review_rejected",
  // Stage 2 / 2.5 could not produce a sorry-only Lean scaffold (drift loops, missing imports).
  "scaffold_failed",
  // Stage 3 exhausted retries; sorries remain.
  "proof_fill_failed",
  // Stage 4 (equivalence review) judged the Lean theorem inequivalent to the NL claim.
  "equivalence_failed",
  // Stage 3.5 prune broke the build and snapshot restore also failed (rare).
  "unrecoverable_build",
  // `state.flags.missing_architecture` set; run cannot proceed without substrate work.
  "architecture_missing",
  // Orchestrator-driven catch-all when none of the above fits.
  "manual",
] as const;
export type LiteratureFailureReason = (typeof LITERATURE_FAILURE_REASONS)[number];

/** Bank tier directories that loadReusableArtifacts walks. */
const ARTIFACT_TIER_DIRS: readonly BankTier[] = [
  "accepted",
  "downgraded",
  "failed",
  "legacy",
];

/** Bank tier directories that loadBurnedSeeds walks — every tier. */
const BURNED_SEED_TIER_DIRS: readonly BankTier[] = [
  "accepted",
  "downgraded",
  "failed",
  "legacy",
];

/** Trust label for the proposer prompt, keyed by source tier. */
function trustLabel(tier: BankTier): string {
  switch (tier) {
    case "accepted":
      return "trusted-peer (Stage 5 complete; literature_map and prior-art objects fully trusted)";
    case "downgraded":
      return "math-sound, novelty-biased (Stage 0.5 ACCEPT on math, REVISE on novelty; literature_map trusted, novelty framing was found insufficient)";
    case "failed":
      return "kernel-suspect (Stage -0.5 REJECT or Stage 0.5 REJECT on correctness; literature_map citeable but verify specific claims independently)";
    case "legacy":
      return "manually-curated (pre-pipeline content; treat as curated reference)";
  }
}

export interface ReusableArtifact {
  /** Bank entry id (directory name), e.g. "flagship_explore_f1". */
  source: string;
  /** qid recorded in the banked README's frontmatter. */
  source_qid: string;
  /** spec recorded in the banked README's frontmatter. */
  source_spec: string;
  /** Topic string recorded in the banked README's frontmatter. */
  source_topic: string;
  /** Which `_bank/<tier>/` the source lives in. */
  source_tier: BankTier;
  /** Artifact kind as declared in the README. */
  kind: ArtifactKind;
  /** Hand-curated one-line description from the README. */
  one_line: string;
  /** Relative path inside the source dir, as recorded in the README. */
  path: string;
  /** Absolute path on disk to the referenced artifact (may not exist). */
  abs_path: string;
  /** Match tier with the current run's topic / qid-cluster. */
  match: ArtifactMatch;
  /** P5 self-reported overall score (0–10) of the source paper, if banked. */
  source_score?: number;
  /** Loaded content (only populated for `literature_map`). Up to 32 KB. */
  content?: string;
}

/** Query parameters describing the current run, used for matching. */
export interface ReusableArtifactsQuery {
  topic: string;
  qid: string;
}

/**
 * Extract the reusable-artifact cluster from a qid (its leading prefix token).
 */
function clusterOf(qid: string): string {
  const m = qid.match(/^([a-z0-9]+)/i);
  return (m?.[1] ?? qid).toLowerCase();
}

/** Normalize a topic string for exact comparison. */
function normTopic(s: string): string {
  return s.replace(/\s+/g, " ").trim().toLowerCase();
}

/** Classify match tier between (queryQid, queryTopic) and a banked entry. */
function classifyMatch(
  query: ReusableArtifactsQuery,
  source: { qid: string; topic: string },
): ArtifactMatch | null {
  if (normTopic(query.topic) === normTopic(source.topic)) return "strict";
  const qCluster = clusterOf(query.qid);
  const sCluster = clusterOf(source.qid);
  // "flagship" / "flagship_explore" are meta-buckets; they cross-match any cluster
  // because flagship-tier exploratory runs are not topically pinned to one bucket.
  const isFlagship = (c: string) => c === "flagship";
  if (qCluster === sCluster || isFlagship(qCluster) || isFlagship(sCluster)) {
    return "related";
  }
  return null;
}

/**
 * Minimal YAML frontmatter parser, scoped to the fields written by
 * `bin/bank_entry.ts` plus the hand-filled `reusable_artifacts:` list.
 * Handles JSON-encoded string scalars (the convention used by `yamlStr` in
 * bank_entry.ts), bare scalars, and one-level list-of-dict for
 * `reusable_artifacts`. Anything more exotic (block scalars, anchors, flow
 * maps) is silently ignored — this is a read path, not a general parser.
 */
function parseFrontmatter(md: string): Record<string, unknown> | null {
  if (!md.startsWith("---\n")) return null;
  const end = md.indexOf("\n---", 4);
  if (end < 0) return null;
  const body = md.slice(4, end);
  const lines = body.split("\n");
  const out: Record<string, unknown> = {};
  let i = 0;
  const parseScalar = (raw: string): string => {
    const t = raw.trim();
    if (t.startsWith("\"") || t.startsWith("'")) {
      try { return JSON.parse(t.replace(/^'(.*)'$/, "\"$1\"")); } catch { return t.replace(/^["']|["']$/g, ""); }
    }
    return t;
  };
  while (i < lines.length) {
    const line = lines[i];
    if (line.trim() === "" || line.trim().startsWith("#")) { i++; continue; }
    const m = line.match(/^([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$/);
    if (!m) { i++; continue; }
    const key = m[1];
    const rest = m[2];
    if (rest === "" || rest === "[]") {
      // block list or empty list
      if (rest === "[]") { out[key] = []; i++; continue; }
      const items: Array<Record<string, string>> = [];
      i++;
      while (i < lines.length) {
        const l = lines[i];
        if (l.trim() === "" || l.trim().startsWith("#")) { i++; continue; }
        const itemHead = l.match(/^\s{2}-\s+([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$/);
        if (!itemHead) break;
        const item: Record<string, string> = {};
        item[itemHead[1]] = parseScalar(itemHead[2]);
        i++;
        while (i < lines.length) {
          const sub = lines[i].match(/^\s{4}([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$/);
          if (!sub) break;
          item[sub[1]] = parseScalar(sub[2]);
          i++;
        }
        items.push(item);
      }
      out[key] = items;
    } else {
      out[key] = parseScalar(rest);
      i++;
    }
  }
  return out;
}

const MAX_CONTENT_BYTES = 32 * 1024;

/**
 * Walk the bank and harvest reusable artifacts whose source matches the
 * current run's (topic, qid-cluster). For `literature_map` kind, load content
 * from the banked state.json's `proposed_from.literature_map` (preferred —
 * shorter and structured) or from the referenced file as fallback.
 *
 * Non-`literature_map` artifacts are returned as pointers (no `content`), so
 * the proposer can cite them but is not tempted to lift them verbatim.
 */
export async function loadReusableArtifacts(
  repoRoot: string,
  query: ReusableArtifactsQuery,
): Promise<ReusableArtifact[]> {
  // Research-bank only: reusable artifacts (literature_map / lp_setup / etc.)
  // are tied to proposer-output frontmatter, which the literature bank does
  // not carry.
  const bankRoot = researchBankRoot(repoRoot);
  const out: ReusableArtifact[] = [];
  let tiers: string[];
  try { tiers = await readdir(bankRoot); } catch { return out; }
  for (const tier of tiers) {
    if (!(ARTIFACT_TIER_DIRS as readonly string[]).includes(tier)) continue;
    const tierDir = path.join(bankRoot, tier);
    let entries: string[];
    try { entries = await readdir(tierDir); } catch { continue; }
    for (const entry of entries) {
      const entryDir = path.join(tierDir, entry);
      let st;
      try { st = await stat(entryDir); } catch { continue; }
      if (!st.isDirectory()) continue;
      const readmePath = path.join(entryDir, "README.md");
      let md: string;
      try { md = await readFile(readmePath, "utf8"); } catch { continue; }
      const fm = parseFrontmatter(md);
      if (!fm) continue;
      const srcQid = typeof fm.qid === "string" ? fm.qid : "";
      const srcSpec = typeof fm.spec === "string" ? fm.spec : "";
      const srcTopic = typeof fm.topic === "string" ? fm.topic : "";
      if (!srcQid || !srcTopic) continue;
      // paper_score is written back into the accepted entry by causalsmith P5;
      // parseFrontmatter yields it as a scalar string, so coerce to a number.
      const scoreNum = fm.paper_score != null ? Number(fm.paper_score) : NaN;
      const srcScore = Number.isFinite(scoreNum) ? scoreNum : undefined;
      const match = classifyMatch(query, { qid: srcQid, topic: srcTopic });
      if (!match) continue;
      const artifacts = Array.isArray(fm.reusable_artifacts) ? fm.reusable_artifacts : [];
      // Lazy state.json load (only when a literature_map artifact wants content).
      let stateJson: any = null;
      const loadState = async (): Promise<any> => {
        if (stateJson !== null) return stateJson;
        let files: string[];
        try { files = await readdir(entryDir); } catch { return (stateJson = {}); }
        const sf = files.find(isStateFileName);
        if (!sf) return (stateJson = {});
        try { stateJson = JSON.parse(await readFile(path.join(entryDir, sf), "utf8")); }
        catch { stateJson = {}; }
        return stateJson;
      };
      for (const aRaw of artifacts as Array<Record<string, unknown>>) {
        if (!aRaw || typeof aRaw !== "object") continue;
        const p = typeof aRaw.path === "string" ? aRaw.path : "";
        const kindRaw = typeof aRaw.kind === "string" ? aRaw.kind.toLowerCase() : "other";
        const kind: ArtifactKind =
          kindRaw === "literature_map" || kindRaw === "lp_setup" ||
          kindRaw === "witness" || kindRaw === "counterexample"
            ? (kindRaw as ArtifactKind)
            : "other";
        const oneLine = typeof aRaw.one_line === "string" ? aRaw.one_line : "";
        if (!p && kind !== "literature_map") continue;
        const absPath = p ? path.join(entryDir, p) : "";
        const artifact: ReusableArtifact = {
          source: entry,
          source_qid: srcQid,
          source_spec: srcSpec,
          source_topic: srcTopic,
          source_tier: tier as BankTier,
          kind,
          one_line: oneLine,
          path: p,
          abs_path: absPath,
          match,
          source_score: srcScore,
        };
        if (kind === "literature_map") {
          const s = await loadState();
          const lmFromState = s?.proposed_from?.literature_map;
          if (typeof lmFromState === "string" && lmFromState.trim().length > 0) {
            artifact.content = lmFromState.slice(0, MAX_CONTENT_BYTES);
          } else if (absPath) {
            try {
              const raw = await readFile(absPath, "utf8");
              artifact.content = raw.slice(0, MAX_CONTENT_BYTES);
            } catch { /* leave content undefined */ }
          }
        }
        out.push(artifact);
      }
    }
  }
  return out;
}

/**
 * Render a compact prompt-ready block describing reusable prior-art
 * artifacts found in the bank. Returns empty string if there are none.
 *
 * Block contract (read by the Codex proposer):
 *   - `literature_map (full)` entries embed verbatim content; the proposer
 *     may use them to seed Step 0a, but must verify bibkeys.
 *   - `lp_setup` / `witness` / `counterexample` entries are pointers: the
 *     proposer may cite them as prior art but lifting them verbatim will
 *     be flagged at Stage -0.5 / Stage 0.5 as not contribution-bearing.
 */
export function renderReusableArtifactsBlock(artifacts: ReusableArtifact[]): string {
  if (artifacts.length === 0) return "";
  const lines: string[] = [
    "=== REUSABLE PRIOR-ART ARTIFACTS (from related banked runs; prior art, NOT a starting kernel) ===",
    "These artifacts come from prior banked runs whose anchor topic or qid-cluster",
    "relates to the current run. Use them as Step 0a / §5 prior-art substrate.",
    "literature_map content is verbatim — you may rely on it after verifying bibkeys.",
    "lp_setup / witness / counterexample entries are POINTERS — you may cite them,",
    "but you MUST contribute net-new content; lifting them as the kernel will be",
    "flagged at Stage -0.5 / Stage 0.5 as not novel.",
    "",
    "Trust hierarchy (the `trust:` header on each source):",
    "  - trusted-peer (accepted): Stage 5 complete. Use literature_map and prior-art objects as if they were yours, after citing.",
    "  - math-sound, novelty-biased (downgraded): math is sound. literature_map is trusted; the novelty framing was found insufficient — do not inherit it without questioning.",
    "  - kernel-suspect (failed): the prior run did not pass correctness/proposal review. literature_map is citeable but verify specific paper claims independently.",
    "  - manually-curated (legacy): pre-pipeline material. Treat as a curated reference.",
  ];
  // Group by source for readability.
  const bySource = new Map<string, ReusableArtifact[]>();
  for (const a of artifacts) {
    const arr = bySource.get(a.source) ?? [];
    arr.push(a);
    bySource.set(a.source, arr);
  }
  for (const [source, arr] of bySource) {
    const first = arr[0];
    const scoreTag = typeof first.source_score === "number" ? `, self-score=${first.source_score}/10` : "";
    lines.push(
      "",
      `--- from ${source} [tier=${first.source_tier}, match=${first.match}${scoreTag}] ---`,
      `  trust: ${trustLabel(first.source_tier)}`,
      `  source_topic: ${first.source_topic}`,
    );
    // literature_map first (verbatim content), then pointers.
    const lmList = arr.filter((a) => a.kind === "literature_map");
    const ptrList = arr.filter((a) => a.kind !== "literature_map");
    for (const a of lmList) {
      lines.push("", `  [literature_map] ${a.one_line || "(no one-line summary)"}`);
      if (a.content) {
        lines.push("  --- begin literature_map content ---");
        for (const cl of a.content.split("\n")) lines.push(`  ${cl}`);
        lines.push("  --- end literature_map content ---");
      } else {
        lines.push(`  (content not loadable; see ${a.path})`);
      }
    }
    for (const a of ptrList) {
      lines.push(`  [${a.kind} pointer] ${a.one_line || "(no one-line summary)"} (see ${a.path})`);
    }
  }
  lines.push("", "=== END REUSABLE PRIOR-ART ARTIFACTS ===");
  return lines.join("\n");
}

/**
 * Render a compact, prompt-ready block listing burned seeds. The proposer
 * Codex worker reads this as defense-in-depth so it does not re-propose
 * the same angles (the post-hoc filter is the load-bearing enforcement).
 */
export function renderBurnedSeedsBlock(burned: BurnedSeed[]): string {
  if (burned.length === 0) return "";
  const lines: string[] = [
    "=== BURNED SEEDS (do NOT re-propose; these were refuted by prior banked runs) ===",
  ];
  for (const b of burned) {
    const bib = b.anchor_bibkey ? `[anchor: ${b.anchor_bibkey}] ` : "";
    lines.push(`- ${bib}${b.one_liner}`);
    if (b.reason) lines.push(`  reason: ${b.reason}`);
    lines.push(`  source: ${b.source} (burned ${b.burned_on})`);
  }
  lines.push("=== END BURNED SEEDS ===");
  return lines.join("\n");
}
