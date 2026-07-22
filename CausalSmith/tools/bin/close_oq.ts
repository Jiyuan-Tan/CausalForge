#!/usr/bin/env -S npx tsx
/**
 * Manual repair CLI for the post-Stage-5 close hook (Phase 3, spec §9 row 8).
 *
 * Usage:
 *   npx tsx tools/bin/close_oq.ts <qid> <spec> <oq_id> \
 *       [--instantiates m1,m2,...] [--uses a1,a2,...]
 *
 * Invoke when Stage 5 banked the qid successfully but the in-pipeline close
 * hook failed (e.g. transient lock contention or filesystem error). The CLI
 * forwards to the same `closeOpenQuestion` function the pipeline calls, so
 * idempotency, status-transition discipline, and atomicity behave identically.
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import {
  closeOpenQuestion,
  BankedTheoremAlreadyExists,
  OpenQuestionNotInProgress,
  OpenQuestionMissing,
  GraphLockTimeout,
} from "../src/shared/close_open_question.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


function parseListFlag(args: string[], flag: string): string[] | undefined {
  const idx = args.indexOf(flag);
  if (idx === -1) return undefined;
  const raw = args[idx + 1];
  args.splice(idx, 2);
  if (!raw) {
    throw new Error(`${flag} requires a comma-separated list (e.g. ${flag} iv,did)`);
  }
  return raw
    .split(",")
    .map((s) => s.trim())
    .filter((s) => s.length > 0);
}

function usage(): never {
  console.error(
    "Usage: close_oq <qid> <spec> <oq_id> [--instantiates m1,m2] [--uses a1,a2]",
  );
  process.exit(1);
}

async function main(): Promise<void> {
  const args = [...process.argv.slice(2)];
  let instantiates: string[] | undefined;
  let uses: string[] | undefined;
  try {
    instantiates = parseListFlag(args, "--instantiates");
    uses = parseListFlag(args, "--uses");
  } catch (err) {
    console.error(String(err instanceof Error ? err.message : err));
    process.exit(1);
  }

  const [qid, spec, oq_id, extra] = args;
  if (!qid || !spec || !oq_id || extra) usage();

  const repoRoot = findCausalSmithRoot(process.cwd());
  const graphRoot = path.join(repoRoot, "doc", "study");

  try {
    const result = await closeOpenQuestion(
      {
        qid,
        spec,
        oq_id,
        bankMetadata: {
          instantiates: instantiates ?? [],
          uses: uses ?? [],
        },
      },
      { graphRoot },
    );
    console.log(
      `closed OpenQuestion ${oq_id} → BankedTheorem ${result.bt_id}\n  banked_theorem: ${result.banked_theorem_path}\n  open_question:  ${result.open_question_path}\n  index_rebuilt:  ${result.index_rebuilt}`,
    );
  } catch (err: unknown) {
    if (err instanceof BankedTheoremAlreadyExists) {
      console.error(
        `BankedTheorem ${err.bt_id} already exists at ${err.path}. If the index is stale, run \`npx tsx tools/bin/build_index.ts\`. Otherwise delete the stale node and rerun.`,
      );
      process.exit(1);
    }
    if (err instanceof OpenQuestionNotInProgress) {
      console.error(
        `OpenQuestion ${err.oq_id} status is \`${err.observedStatus}\`. Only an \`in_progress\` OQ may be closed. If a previous attempt partially closed it, no action needed; otherwise inspect the JSON manually.`,
      );
      process.exit(1);
    }
    if (err instanceof OpenQuestionMissing) {
      console.error(
        `OpenQuestion ${err.oq_id} not found at ${err.path}. Confirm the oq_id and graphRoot.`,
      );
      process.exit(1);
    }
    if (err instanceof GraphLockTimeout) {
      console.error(
        `Could not acquire the graph write lock — another writer is holding it. Wait or stop the other run, then retry.`,
      );
      process.exit(1);
    }
    console.error(`close_oq failed: ${err instanceof Error ? err.message : String(err)}`);
    process.exit(1);
  }
}

main();
