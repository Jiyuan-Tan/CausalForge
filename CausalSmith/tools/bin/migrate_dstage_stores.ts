#!/usr/bin/env -S npx tsx
/** One-shot D-stage store migration (spec §Migration).
 *
 *  Active runs:   migrate_dstage_stores.ts <qid> <specialization> [<qid> <spec> ...]
 *                 (refuses a qid whose run is live — heartbeat)
 *  Accepted bank: migrate_dstage_stores.ts --bank-accepted
 *                 (migrates doc/research/_bank/accepted/* ONLY — no other bank
 *                 subdirectory is ever touched; entries are frozen runs, so no
 *                 heartbeat is needed)
 */
import process from "node:process";
import path from "node:path";
import { readdir, readFile, stat } from "node:fs/promises";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { migrateQidStores, migrateStoresInDir } from "../src/discovery/framework/migrate_stores.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import type { PipelineContext } from "../src/types.js";

async function migrateAcceptedBank(repoRoot: string): Promise<void> {
  const acceptedDir = path.join(repoRoot, "doc", "research", "_bank", "accepted");
  const entries = await readdir(acceptedDir);
  for (const entry of entries.sort()) {
    const runDir = path.join(acceptedDir, entry);
    if (!(await stat(runDir)).isDirectory()) continue;
    const statePath = path.join(runDir, "state.json");
    let qid: string | undefined;
    let specialization: string | undefined;
    try {
      const state = JSON.parse(await readFile(statePath, "utf8")) as { qid?: string; specialization?: string };
      qid = state.qid;
      specialization = state.specialization;
    } catch {
      /* fall through to the loud skip below */
    }
    if (!qid || !specialization) {
      console.error(`[skip] ${entry}: could not read qid/specialization from state.json — not migrated`);
      continue;
    }
    const report = await migrateStoresInDir({ runDir, qid, specialization });
    console.log(JSON.stringify({ entry, ...report }, null, 2));
  }
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const repoRoot = findCausalSmithRoot(process.cwd());
  if (args[0] === "--bank-accepted") {
    if (args.length !== 1) throw new Error("--bank-accepted takes no further arguments");
    await migrateAcceptedBank(repoRoot);
    return;
  }
  if (args.length === 0 || args.length % 2 !== 0) {
    throw new Error(
      "Usage: migrate_dstage_stores.ts <qid> <specialization> [<qid> <specialization> ...] | --bank-accepted",
    );
  }
  for (let i = 0; i < args.length; i += 2) {
    const [qid, specialization] = [args[i], args[i + 1]];
    const ctx = { repoRoot, qid, specialization, dryRun: false, resume: false } as PipelineContext;
    // withRunHeartbeat throws `causalsmith_qid_busy` when the run is live — exactly the refusal we want.
    const report = await withRunHeartbeat(repoRoot, qid, specialization, () => migrateQidStores(ctx));
    console.log(JSON.stringify(report, null, 2));
  }
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 1;
});
