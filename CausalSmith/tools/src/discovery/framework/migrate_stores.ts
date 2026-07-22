// One-shot migration to the consolidated store layout (spec §Migration):
//   1. fold the legacy 5-file proposal payload into d0_working.json.proposals
//   2. normalize legacy prefixed discovery store names to canonical bare names
// Originals are preserved under discovery/.premigration/<n>/. Idempotent.
// `_bank/` is NEVER touched — callers must pass an active-run ctx.
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, rm, copyFile, readdir } from "node:fs/promises";
import path from "node:path";
import { artifactPath, formalizationDir, legacyRunPrefix } from "../../paths.js";
import { WorkingStateSchema } from "./stores.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { readRepairedModelJson } from "../core/core_io.js";
import { repairLatexStringsDeep } from "../core/latex_serialization.js";
import type { PipelineContext } from "../../types.js";

const PROPOSAL_KINDS = ["statements", "definitions", "assumptions", "coreEdits", "proofs"] as const;
type ProposalKind = (typeof PROPOSAL_KINDS)[number];

// Historical per-kind filenames (retired as live stores 2026-07-20); the
// migration is now the only reader.
const LEGACY_PROPOSAL_FILENAME: Record<ProposalKind, string> = {
  statements: "proposed_statement_changes.json",
  definitions: "proposed_definition_changes.json",
  assumptions: "proposed_assumptions.json",
  coreEdits: "proposed_core_edits.json",
  proofs: "proposed_proofs.json",
};

function legacyProposalPath(ctx: PipelineContext, kind: ProposalKind): string {
  const name = LEGACY_PROPOSAL_FILENAME[kind];
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", name, [`${ctx.qid}_${name}`]);
}

/** Stores whose legacy names get normalized to the canonical bare nested name. */
const NORMALIZE_NAMES = [
  "proto_core.json",
  "core.json",
  "d0_working.json",
  "d0_escalation_log.jsonl",
  "gaps.json",
  "open_obligations.json",
  "withheld_content.json",
  "proposal_review_packet.json",
  "semantic_manifest.json",
] as const;

export interface MigrationReport {
  qid: string;
  foldedKinds: ProposalKind[];
  renamed: Array<{ from: string; to: string }>;
  backupDir: string | null;
}

async function nextBackupDir(discoveryDir: string): Promise<string> {
  const root = path.join(discoveryDir, ".premigration");
  await mkdir(root, { recursive: true });
  const existing = await readdir(root);
  const n = existing.map((d) => Number(d)).filter(Number.isFinite).reduce((a, b) => Math.max(a, b), 0) + 1;
  const dir = path.join(root, String(n));
  await mkdir(dir, { recursive: true });
  return dir;
}

/** Active-run wrapper: resolves the run directory and delegates. */
export async function migrateQidStores(ctx: PipelineContext): Promise<MigrationReport> {
  return migrateStoresInDir({
    runDir: formalizationDir(ctx.repoRoot, ctx.qid),
    qid: ctx.qid,
    specialization: ctx.specialization,
  });
}

/**
 * Directory-based core: migrate one run directory (an active run OR a bank
 * entry — bank entries carry the same store layout frozen at bank time).
 * Path resolution is local so this works outside `formalizationDir`'s
 * active-run root.
 */
export async function migrateStoresInDir(args: {
  runDir: string;
  qid: string;
  specialization: string;
}): Promise<MigrationReport> {
  const { runDir, qid, specialization } = args;
  const discoveryDir = path.join(runDir, "discovery");
  const prefixes = [qid, legacyRunPrefix(qid, specialization)];
  const report: MigrationReport = { qid, foldedKinds: [], renamed: [], backupDir: null };
  if (!existsSync(runDir)) return report;
  let backupDir: string | null = null;
  const backup = async (file: string): Promise<void> => {
    if (backupDir === null) backupDir = await nextBackupDir(discoveryDir);
    await copyFile(file, path.join(backupDir, path.basename(file)));
  };
  /** First existing candidate: bare nested, bare flat, then each prefix nested/flat. */
  const resolveExisting = (name: string): string | null => {
    const candidates = [
      path.join(discoveryDir, name),
      path.join(runDir, name),
      ...prefixes.flatMap((p) => [path.join(discoveryDir, `${p}_${name}`), path.join(runDir, `${p}_${name}`)]),
    ];
    return candidates.find((c) => existsSync(c)) ?? null;
  };

  // ---- 1. fold legacy proposal files ----------------------------------------
  const legacyResolved = PROPOSAL_KINDS.map((k) => [k, resolveExisting(LEGACY_PROPOSAL_FILENAME[k])] as const)
    .filter((pair): pair is readonly [ProposalKind, string] => pair[1] !== null);
  if (legacyResolved.length > 0) {
    const workingResolved = resolveExisting("d0_working.json");
    if (workingResolved === null) {
      // No working cursor: the proposals cannot be folded into anything. This run
      // never entered D0 or lost its cursor — surface, don't guess.
      throw new Error(
        `qid ${qid}: legacy proposal file(s) [${legacyResolved.map(([k]) => k).join(", ")}] exist but there is no ` +
          `d0_working.json to fold them into — inspect the run before migrating`,
      );
    }
    const working = WorkingStateSchema.parse(JSON.parse(await readFile(workingResolved, "utf8")));
    // Pre-defense-era snapshots can carry decoded control-escape corruption in
    // proof/statement TeX; repair before folding into the live store.
    repairLatexStringsDeep(working);
    if (working.proposals !== undefined) {
      throw new Error(
        `qid ${qid}: both working.proposals and legacy proposal file(s) [${legacyResolved.map(([k]) => k).join(", ")}] exist — ` +
          `the two channels may have diverged; reconcile by hand (compare contents, keep one) before migrating`,
      );
    }
    await backup(workingResolved);
    const folded: { statements: unknown[]; definitions: unknown[]; assumptions: unknown[]; coreEdits: unknown[]; proofs: Array<{ id: string; proof_tex: string }> } = {
      statements: [],
      definitions: [],
      assumptions: [],
      coreEdits: [],
      proofs: [],
    };
    for (const [kind, p] of legacyResolved) {
      // Legacy proposal files predate the escape defense and are exactly where
      // under-escaped / corrupted TeX lives — read through the full defense.
      const parsed = await readRepairedModelJson(p);
      if (!Array.isArray(parsed)) throw new Error(`qid ${qid}: legacy proposal file ${p} is not a JSON array`);
      folded[kind] = parsed;
      report.foldedKinds.push(kind);
    }
    const merged = WorkingStateSchema.parse({ ...working, proposals: folded });
    await writeJsonAtomic(workingResolved, merged);
    for (const [, p] of legacyResolved) {
      await backup(p);
      await rm(p); // original leaves the live tree; the backup copy is the archive
    }
  }

  // ---- 2. normalize legacy names --------------------------------------------
  // Legacy names come in TWO prefix forms: `<qid>_<name>` (most discovery
  // stores) and `<qid>_<spec>_<name>` (run-prefixed stores like gaps.json — see
  // gapsJsonPath/legacyRunPrefix). Cover both, in nested and flat layouts.
  for (const name of NORMALIZE_NAMES) {
    const canonical = path.join(discoveryDir, name);
    if (existsSync(canonical)) continue;
    const found = resolveExisting(name);
    if (!found) continue;
    await mkdir(discoveryDir, { recursive: true });
    await backup(found);
    await rename(found, canonical);
    report.renamed.push({ from: path.basename(found), to: name });
  }

  // ---- 3. normalize the reviews DIRECTORY -----------------------------------
  // `reviews/` carries the run's review artifacts; legacy runs used
  // `<qid>_<spec>_reviews/`. Some historical runs SPLIT their reviews across
  // both names (different stages wrote to different dirs), so this merges
  // file-by-file rather than renaming wholesale: a file present only in the
  // legacy dir moves over; a byte-identical duplicate is dropped from the
  // legacy side; a DIFFERING collision refuses loudly (never guess which
  // review is authoritative). Pure renames are lossless — no per-file backup.
  const bareReviews = path.join(runDir, "reviews");
  for (const p of prefixes) {
    const legacyReviews = path.join(runDir, `${p}_reviews`);
    if (!existsSync(legacyReviews)) continue;
    if (!existsSync(bareReviews)) {
      await rename(legacyReviews, bareReviews);
      report.renamed.push({ from: `${p}_reviews`, to: "reviews" });
      break;
    }
    for (const file of await readdir(legacyReviews)) {
      const src = path.join(legacyReviews, file);
      const dst = path.join(bareReviews, file);
      if (!existsSync(dst)) {
        await rename(src, dst);
        report.renamed.push({ from: `${p}_reviews/${file}`, to: `reviews/${file}` });
        continue;
      }
      const [a, b] = await Promise.all([readFile(src), readFile(dst)]);
      if (a.equals(b)) {
        await rm(src); // identical duplicate — keep the canonical copy only
        continue;
      }
      throw new Error(
        `qid ${qid}: reviews merge collision — '${file}' exists in BOTH ${legacyReviews} and ${bareReviews} ` +
          `with different contents; resolve by hand before migrating (never guess which review is authoritative)`,
      );
    }
    if ((await readdir(legacyReviews)).length === 0) {
      await rm(legacyReviews, { recursive: true });
      report.renamed.push({ from: `${p}_reviews`, to: "reviews (merged)" });
    }
    break;
  }

  report.backupDir = backupDir;
  return report;
}
