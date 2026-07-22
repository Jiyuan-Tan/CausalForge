#!/usr/bin/env node
/**
 * Compute the proposal→derivation tier-drift metric across the bank.
 *
 * For every banked entry in `_bank/{accepted,downgraded}/` (failed is
 * excluded because it never had a derivation; legacy is excluded because
 * it predates the reviewer system and has no calibrated verdicts), read:
 *
 *   - state.json `proposed_from.novelty_target` (the target band)
 *   - state.json final iteration verdict (Stage -0.5)
 *   - reviews.jsonl last `stage_0.5*` line (Stage 0.5)
 *
 * Compute:
 *
 *   drift_rate(novelty_target) =
 *     |{downgraded entries with novelty_target = T}| /
 *     |{accepted ∪ downgraded entries proposed at T}|
 *
 * A rising drift rate at field/flagship means Stage -0.5 is over-promising
 * relative to Stage 0.5; falling = calibration.
 *
 * Usage:
 *   npx tsx tools/bin/bank_drift.ts             # human-readable table
 *   npx tsx tools/bin/bank_drift.ts --json      # machine-readable JSON
 *
 * Exit code is always 0 unless the bank directory itself is unreadable;
 * an empty bank prints an empty table and exits 0 (drift is undefined,
 * not an error).
 */
import { existsSync, readFileSync } from "node:fs";
import { readdir, readFile, stat } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { isStateFileName } from "../src/paths.js";
import { normalizeNoveltyTarget } from "../src/novelty.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

type Tier = "accepted" | "downgraded";
type NoveltyTarget = "incremental" | "subfield" | "field" | "flagship";

interface EntrySummary {
  tier: Tier;
  qid: string;
  spec: string;
  novelty_target: NoveltyTarget | "unknown";
  tier_at_proposal: string;
  tier_at_derivation: string;
}


function tierAtProposal(state: any): string {
  const its = state?.proposed_from?.iterations as Array<{ verdict: string }> | undefined;
  if (!its || its.length === 0) return "NA";
  const final = state?.proposed_from?.final_verdict;
  if (final && typeof final === "string" && final !== "pending") return final;
  for (let i = its.length - 1; i >= 0; i--) {
    const v = its[i].verdict?.toUpperCase();
    if (v && v !== "REVISE-CAP-EXHAUSTED") return v;
  }
  return "NA";
}

async function tierAtDerivation(entryDir: string, qid: string, spec: string): Promise<string> {
  // canonical reviews/ subfolder first, then pre-move legacy root locations.
  const reviewsLog = [
    path.join(entryDir, "reviews", "reviews.jsonl"),
    path.join(entryDir, `${qid}_${spec}_reviews`, "reviews.jsonl"),
    path.join(entryDir, "reviews.jsonl"),
    path.join(entryDir, `${qid}_${spec}_reviews.jsonl`),
  ].find((c) => existsSync(c));
  if (!reviewsLog) return "NA";
  const lines = (await readFile(reviewsLog, "utf8")).trim().split("\n").filter(Boolean);
  // Only `kind === "review"` lines carry real verdicts; pipeline-notes
  // (manual-rollback, manual-resolution) reuse the stage field with
  // sentinel status strings.
  for (let i = lines.length - 1; i >= 0; i--) {
    try {
      const r = JSON.parse(lines[i]);
      if (r.kind !== "review") continue;
      const stage = String(r.stage ?? "");
      if (stage.startsWith("stage_0.5") || stage === "0.5") {
        return String(r.status ?? "NA").toUpperCase();
      }
    } catch { /* skip */ }
  }
  return "NA";
}

async function readEntry(tier: Tier, entryDir: string, dirName: string): Promise<EntrySummary | null> {
  const files = await readdir(entryDir).catch(() => [] as string[]);
  const stateFile = files.find(isStateFileName);
  if (!stateFile) return null;
  let state: any;
  try { state = JSON.parse(await readFile(path.join(entryDir, stateFile), "utf8")); } catch { return null; }
  const qid = state?.proposed_from?.chosen_qid as string | undefined;
  const spec = state?.proposed_from?.chosen_specialization as string | undefined;
  if (!qid || !spec) {
    const m = dirName.match(/^(.+?)_([^_]+(?:_[^_]+)*)$/);
    if (!m) return null;
  }
  const resolvedQid = qid ?? dirName.split("_")[0];
  const resolvedSpec = spec ?? dirName.slice(resolvedQid.length + 1);
  return {
    tier,
    qid: resolvedQid,
    spec: resolvedSpec,
    novelty_target: (normalizeNoveltyTarget(state?.proposed_from?.novelty_target) ?? "unknown") as
      | NoveltyTarget
      | "unknown",
    tier_at_proposal: tierAtProposal(state),
    tier_at_derivation: await tierAtDerivation(entryDir, resolvedQid, resolvedSpec),
  };
}

async function collect(repoRoot: string): Promise<EntrySummary[]> {
  // Research-bank only: tier-drift is a calibration metric for the proposer
  // reviewer chain (Stage -0.5 vs Stage 0.5). The literature bank has no
  // novelty target / tier verdict pair to drift against.
  const bankRoot = path.join(repoRoot, "doc", "research", "_bank");
  const out: EntrySummary[] = [];
  for (const tier of ["accepted", "downgraded"] as Tier[]) {
    const tierDir = path.join(bankRoot, tier);
    let entries: string[];
    try { entries = await readdir(tierDir); } catch { continue; }
    for (const entry of entries) {
      const entryDir = path.join(tierDir, entry);
      let s; try { s = await stat(entryDir); } catch { continue; }
      if (!s.isDirectory()) continue;
      const summary = await readEntry(tier, entryDir, entry);
      if (summary) out.push(summary);
    }
  }
  return out;
}

function computeDrift(entries: EntrySummary[]): Array<{
  novelty_target: string;
  proposed: number;
  downgraded: number;
  accepted: number;
  drift_rate: number | null;
}> {
  const buckets = new Map<string, { accepted: number; downgraded: number }>();
  for (const e of entries) {
    const key = e.novelty_target;
    const b = buckets.get(key) ?? { accepted: 0, downgraded: 0 };
    if (e.tier === "accepted") b.accepted++;
    else if (e.tier === "downgraded") b.downgraded++;
    buckets.set(key, b);
  }
  const rows: Array<{
    novelty_target: string;
    proposed: number;
    downgraded: number;
    accepted: number;
    drift_rate: number | null;
  }> = [];
  for (const [k, v] of buckets) {
    const proposed = v.accepted + v.downgraded;
    rows.push({
      novelty_target: k,
      proposed,
      downgraded: v.downgraded,
      accepted: v.accepted,
      drift_rate: proposed === 0 ? null : v.downgraded / proposed,
    });
  }
  // Stable order: incremental, subfield, field, flagship, unknown
  const order = ["incremental", "subfield", "field", "flagship"];
  rows.sort((a, b) => {
    const ai = order.indexOf(a.novelty_target);
    const bi = order.indexOf(b.novelty_target);
    return (ai < 0 ? 99 : ai) - (bi < 0 ? 99 : bi);
  });
  return rows;
}

function renderTable(rows: ReturnType<typeof computeDrift>, entries: EntrySummary[]): string {
  if (rows.length === 0) return "(bank empty — no accepted or downgraded entries yet)";
  const lines: string[] = [];
  lines.push("Bank tier-drift summary");
  lines.push("=======================");
  lines.push("");
  const header = ["novelty_target", "proposed", "accepted", "downgraded", "drift_rate"];
  const widths = header.map((h) => h.length);
  const data = rows.map((r) => [
    r.novelty_target,
    String(r.proposed),
    String(r.accepted),
    String(r.downgraded),
    r.drift_rate === null ? "—" : r.drift_rate.toFixed(3),
  ]);
  for (const row of data) row.forEach((c, i) => { widths[i] = Math.max(widths[i], c.length); });
  const fmtRow = (cells: string[]) => cells.map((c, i) => c.padEnd(widths[i])).join("  ");
  lines.push(fmtRow(header));
  lines.push(widths.map((w) => "-".repeat(w)).join("  "));
  for (const row of data) lines.push(fmtRow(row));
  lines.push("");
  lines.push(`Entries (${entries.length}):`);
  for (const e of entries) {
    lines.push(
      `  ${e.tier.padEnd(11)} ${e.qid}/${e.spec}  ` +
        `target=${e.novelty_target}  prop=${e.tier_at_proposal}  deriv=${e.tier_at_derivation}`,
    );
  }
  lines.push("");
  lines.push(
    "Note: `failed/` and `legacy/` are excluded by design (no calibrated " +
      "proposal-vs-derivation pair). See _bank/README.md § 'Tier-drift metric'.",
  );
  return lines.join("\n");
}

async function main() {
  const json = process.argv.includes("--json");
  const repoRoot = findCausalSmithRoot(process.cwd());
  const entries = await collect(repoRoot);
  const rows = computeDrift(entries);
  if (json) {
    process.stdout.write(JSON.stringify({ rows, entries }, null, 2) + "\n");
  } else {
    process.stdout.write(renderTable(rows, entries) + "\n");
  }
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
