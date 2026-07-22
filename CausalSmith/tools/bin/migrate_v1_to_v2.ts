#!/usr/bin/env -S npx tsx
/**
 * One-shot migrator: rewrite `schema_version: 1` → `schema_version: 2` on
 * every node JSON under `<studyDir>/nodes/<type>/*.json`. Atomic writes
 * (tempfile + rename) so a partial failure leaves each file either
 * fully-migrated or untouched.
 *
 * Usage:
 *   npx tsx CausalSmith/tools/bin/migrate_v1_to_v2.ts [--dry-run] [--dir <studyDir>]
 *
 * Defaults `studyDir` to `<CausalSmith>/doc/study` discovered by walking up
 * from cwd, matching `build_index.ts`.
 *
 * This migrator only touches the discriminating `schema_version` integer.
 * It does NOT fill in the new tier-1 Insight fields (`background`,
 * `theorems`, `extensions`, `verification_status`); those land via Stage S2
 * write-time defaults in a later step. The point of this script is to make
 * `loadAllNodes` accept the post-bump constant immediately.
 */
import { existsSync, readFileSync } from "node:fs";
import { readdir, readFile, rename, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


interface MigrationCounts {
  migrated: number;
  already_v2: number;
  unknown_version: number;
  scanned: number;
}

async function writeAtomic(finalPath: string, contents: string): Promise<void> {
  const tmpPath = `${finalPath}.new`;
  await writeFile(tmpPath, contents, "utf8");
  await rename(tmpPath, finalPath);
}

async function migrateNodesDir(
  nodesDir: string,
  dryRun: boolean,
): Promise<MigrationCounts> {
  const counts: MigrationCounts = {
    migrated: 0,
    already_v2: 0,
    unknown_version: 0,
    scanned: 0,
  };
  let typeDirs: string[];
  try {
    typeDirs = await readdir(nodesDir);
  } catch (err: unknown) {
    if ((err as { code?: string })?.code === "ENOENT") return counts;
    throw err;
  }
  for (const typeName of typeDirs) {
    const typeDir = path.join(nodesDir, typeName);
    let entries: string[];
    try {
      entries = await readdir(typeDir);
    } catch {
      continue;
    }
    for (const entry of entries) {
      if (!entry.endsWith(".json") || entry.startsWith(".")) continue;
      const full = path.join(typeDir, entry);
      counts.scanned += 1;
      const raw = await readFile(full, "utf8");
      const parsed = JSON.parse(raw) as Record<string, unknown>;
      const version = parsed.schema_version;
      if (version === 2) {
        counts.already_v2 += 1;
        continue;
      }
      if (version !== 1) {
        counts.unknown_version += 1;
        process.stderr.write(
          `[migrate] WARN: ${full} has schema_version=${String(version)} (expected 1 or 2); skipping\n`,
        );
        continue;
      }
      // Preserve original key ordering: rewrite the file by re-stringifying with
      // schema_version flipped, keeping every other field exactly where it was.
      const migrated: Record<string, unknown> = {};
      for (const k of Object.keys(parsed)) {
        migrated[k] = k === "schema_version" ? 2 : parsed[k];
      }
      const serialized = JSON.stringify(migrated, null, 2) + "\n";
      if (!dryRun) {
        await writeAtomic(full, serialized);
      }
      counts.migrated += 1;
    }
  }
  return counts;
}

async function main() {
  const args = process.argv.slice(2);
  const dryRun = args.includes("--dry-run");
  const dirFlagIdx = args.indexOf("--dir");
  const studyDir =
    dirFlagIdx >= 0
      ? path.resolve(args[dirFlagIdx + 1])
      : path.join(findCausalSmithRoot(process.cwd()), "doc", "study");
  const nodesDir = path.join(studyDir, "nodes");
  process.stderr.write(
    `[migrate] target: ${nodesDir}${dryRun ? " (dry-run)" : ""}\n`,
  );
  const counts = await migrateNodesDir(nodesDir, dryRun);
  process.stderr.write(
    `[migrate] scanned=${counts.scanned} migrated=${counts.migrated} already_v2=${counts.already_v2} unknown=${counts.unknown_version}\n`,
  );
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
