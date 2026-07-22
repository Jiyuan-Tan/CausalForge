/**
 * Cross-process mutex around `lake build` for the CausalSmith package.
 *
 * Once per-qid parallel runs are allowed (see `shared/run_heartbeat.ts`), two
 * concurrent pipelines can independently call `LeanLspClient.build()`. Both
 * invocations target the same `.lake/build` directory, which is not safe under
 * parallel lake invocations — `.olean` writes race and the cache can end up
 * inconsistent. Wrap `lake build` in an exclusive file lock so the LLM stages
 * remain parallel but compilation is serialized.
 *
 * Lock file: `<repoRoot>/.lake-build.lock` (gitignore this).
 *
 * Uses `proper-lockfile`, same as `shared/graph_lock.ts`. A 60-min stale window
 * accommodates Mathlib-scale rebuilds; in practice each acquisition completes
 * in seconds-to-minutes and the lock is released promptly.
 */
import lockfile from "proper-lockfile";
import { stat, writeFile } from "node:fs/promises";
import path from "node:path";

const STALE_MS = 60 * 60_000;
const RETRIES = { retries: 30, factor: 1.5, minTimeout: 200, maxTimeout: 10_000 };

async function ensureLockfileTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await writeFile(target, "{}\n", "utf8");
  }
}

export async function withLakeBuildLock<T>(
  repoRoot: string,
  action: () => Promise<T>,
): Promise<T> {
  const lockPath = path.join(repoRoot, ".lake-build.lock");
  await ensureLockfileTarget(lockPath);
  const release = await lockfile.lock(lockPath, {
    stale: STALE_MS,
    retries: RETRIES,
    realpath: false,
  });
  try {
    return await action();
  } finally {
    await release();
  }
}

// Promotion holds the lock across a full build + library_index + embed + doc:gen
// chain, so a run waiting to promote behind another may wait many minutes. Use a
// far more patient retry budget than the per-command lake lock (worst case ≈ 1h of
// waiting, comfortably longer than any single promotion) so a queued promotion
// waits its turn instead of erroring out.
const PROMOTE_RETRIES = { retries: 300, factor: 1.3, minTimeout: 1_000, maxTimeout: 30_000 };

/**
 * Cross-process mutex serializing the WHOLE substrate-promotion step across
 * concurrent `--study` runs. Unlike `withLakeBuildLock` (per-cwd, per-command),
 * this wraps the entire promotion — root-graph edit + `lake build` +
 * `library_index` + `embed:library` + `doc:gen` — so two runs can never
 * interleave their Causalean root edits or race on the shared `.lake` build dir.
 *
 * Keyed on the CAUSALEAN root (the shared resource every promotion mutates), so
 * all runs — regardless of their own package cwd — contend on the same lock:
 * `<causaleanRoot>/.substrate-promote.lock` (gitignore this).
 */
export async function withPromotionLock<T>(
  causaleanRoot: string,
  action: () => Promise<T>,
): Promise<T> {
  const lockPath = path.join(causaleanRoot, ".substrate-promote.lock");
  await ensureLockfileTarget(lockPath);
  const release = await lockfile.lock(lockPath, {
    stale: STALE_MS,
    retries: PROMOTE_RETRIES,
    realpath: false,
  });
  try {
    return await action();
  } finally {
    await release();
  }
}
