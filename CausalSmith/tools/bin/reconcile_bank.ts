#!/usr/bin/env -S npx tsx
/**
 * Bootstrap reconciler: scan `_bank/accepted/*` and
 * mint a `BankedTheorem` node per entry under
 * `doc/study/nodes/banked_theorem/`.
 *
 * Research-bank only: this is the one-shot bootstrap that backfills
 * BankedTheorem nodes for pre-graph proposer-output entries. Study-mode
 * entries (under `_literature_bank/`) are minted live by the pipeline's
 * post-Stage-5 close hook (`pipeline.ts → closeOpenQuestion`); they do not
 * need a bootstrap pass and intentionally have no tier structure to scan.
 *
 * Phase 1 scope (spec §13 Phase 1): we leave `instantiates` and `uses` empty.
 * Phase 2's S0.5 canonicalization will backfill them once Method/Assumption
 * nodes enter the graph.
 *
 * Flags:
 *   --dry-run         Print would-mint summary; do not write.
 *   --overwrite       Always rewrite matching nodes (default: skip identical).
 *   --bank-dir <p>    Override bank source (default <repo>/doc/research/_bank).
 *   --study-dir <p>   Override study graph root (default <repo>/doc/study).
 */
import { existsSync, readFileSync } from "node:fs";
import { mkdir, readdir, readFile, rename, stat, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import {
  loadAllNodes,
  buildIndex,
  writeIndexAtomic,
  serializeIndex,
} from "../src/shared/graph.js";
import { withGraphWriteLock } from "../src/shared/graph_lock.js";
import { SCHEMA_VERSION, type BankedTheorem } from "../src/shared/kb_types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

interface CliOpts {
  dryRun: boolean;
  overwrite: boolean;
  bankDir: string;
  studyDir: string;
}

const BANK_TIERS_TO_INCLUDE = ["accepted"] as const;


function parseArgs(argv: string[]): CliOpts {
  const dryRun = argv.includes("--dry-run");
  const overwrite = argv.includes("--overwrite");
  const bankIdx = argv.indexOf("--bank-dir");
  const studyIdx = argv.indexOf("--study-dir");
  const repoRoot = (bankIdx === -1 || studyIdx === -1)
    ? findCausalSmithRoot(process.cwd())
    : process.cwd();
  const bankDir = bankIdx >= 0
    ? path.resolve(argv[bankIdx + 1])
    : path.join(repoRoot, "doc", "research", "_bank");
  const studyDir = studyIdx >= 0
    ? path.resolve(argv[studyIdx + 1])
    : path.join(repoRoot, "doc", "study");
  return { dryRun, overwrite, bankDir, studyDir };
}

interface BankEntry {
  tier: string;
  dirName: string;
  fullPath: string;
}

async function scanBankEntries(bankDir: string): Promise<BankEntry[]> {
  const entries: BankEntry[] = [];
  for (const tier of BANK_TIERS_TO_INCLUDE) {
    const tierDir = path.join(bankDir, tier);
    let names: string[];
    try {
      names = await readdir(tierDir);
    } catch (err: unknown) {
      if ((err as { code?: string })?.code === "ENOENT") continue;
      throw err;
    }
    for (const name of names) {
      if (name.startsWith(".") || name === "README.md") continue;
      const full = path.join(tierDir, name);
      const st = await stat(full).catch(() => null);
      if (!st || !st.isDirectory()) continue;
      entries.push({ tier, dirName: name, fullPath: full });
    }
  }
  return entries;
}

function splitDirName(dirName: string): { qid: string; spec: string } | null {
  // bt_id = <qid>_<spec>. The spec slug is the trailing token after the
  // LAST underscore (e.g. `pid_did_anticipation_bounded_v1` -> qid
  // `pid_did_anticipation_bounded`, spec `v1`). This matches the convention
  // in CausalSmith/doc/research/_bank/.
  const idx = dirName.lastIndexOf("_");
  if (idx <= 0 || idx >= dirName.length - 1) return null;
  return { qid: dirName.slice(0, idx), spec: dirName.slice(idx + 1) };
}

async function loadAsBankedTheorem(entry: BankEntry): Promise<BankedTheorem | null> {
  const fallback = splitDirName(entry.dirName);
  if (!fallback) return null;
  // Try the canonical state file first.
  const stateFile = path.join(entry.fullPath, `${entry.dirName}_state.json`);
  let qid = fallback.qid;
  let spec = fallback.spec;
  try {
    const raw = await readFile(stateFile, "utf8");
    const parsed = JSON.parse(raw) as {
      proposed_from?: { chosen_qid?: string; chosen_specialization?: string };
    };
    if (parsed.proposed_from?.chosen_qid) qid = parsed.proposed_from.chosen_qid;
    if (parsed.proposed_from?.chosen_specialization) spec = parsed.proposed_from.chosen_specialization;
  } catch (err: unknown) {
    if ((err as { code?: string })?.code !== "ENOENT") throw err;
    // No state.json — fall back to the dir-name split (already set).
  }
  const bt: BankedTheorem = {
    schema_version: SCHEMA_VERSION,
    bt_id: entry.dirName,
    qid,
    spec,
    instantiates: [],
    uses: [],
  };
  return bt;
}

function canonicalize(bt: BankedTheorem): string {
  // Sorted-key JSON for stable on-disk comparison.
  return (
    JSON.stringify(bt, (_k, v) => {
      if (v && typeof v === "object" && !Array.isArray(v)) {
        const o = v as Record<string, unknown>;
        const out: Record<string, unknown> = {};
        for (const k of Object.keys(o).sort()) out[k] = o[k];
        return out;
      }
      return v;
    }, 2) + "\n"
  );
}

async function writeNodeAtomicIfChanged(
  studyDir: string,
  bt: BankedTheorem,
  overwrite: boolean,
): Promise<"wrote" | "skipped"> {
  const dir = path.join(studyDir, "nodes", "banked_theorem");
  await mkdir(dir, { recursive: true });
  const finalPath = path.join(dir, `${bt.bt_id}.json`);
  const tmpPath = `${finalPath}.new`;
  const serialized = canonicalize(bt);
  if (!overwrite) {
    try {
      const existing = await readFile(finalPath, "utf8");
      if (existing === serialized) return "skipped";
    } catch (err: unknown) {
      if ((err as { code?: string })?.code !== "ENOENT") throw err;
    }
  }
  await writeFile(tmpPath, serialized, "utf8");
  await rename(tmpPath, finalPath);
  return "wrote";
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  const entries = await scanBankEntries(opts.bankDir);
  const mints: BankedTheorem[] = [];
  for (const entry of entries) {
    const bt = await loadAsBankedTheorem(entry);
    if (!bt) {
      console.warn(`WARN: skipping ${entry.fullPath} (could not derive bt_id)`);
      continue;
    }
    mints.push(bt);
    console.warn(
      `WARN: bt_id=${bt.bt_id} minted with empty instantiates/uses; Phase 2 canonicalization will populate.`,
    );
  }

  if (opts.dryRun) {
    for (const bt of mints) console.log(`would mint ${bt.bt_id}`);
    console.log(`(dry-run) ${mints.length} bt nodes`);
    return;
  }

  let wrote = 0;
  let skipped = 0;
  await withGraphWriteLock(opts.studyDir, async () => {
    for (const bt of mints) {
      const result = await writeNodeAtomicIfChanged(opts.studyDir, bt, opts.overwrite);
      if (result === "wrote") wrote += 1;
      else skipped += 1;
    }
    const nodes = await loadAllNodes(opts.studyDir);
    await writeIndexAtomic(opts.studyDir, buildIndex(nodes));
  });
  console.log(
    `Reconciled ${mints.length} banked_theorem nodes (${wrote} written, ${skipped} unchanged).`,
  );
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});

// silence unused import warning if serializeIndex ever gets used; kept for future expansion
void serializeIndex;
