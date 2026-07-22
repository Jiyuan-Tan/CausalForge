/**
 * Single-writer lock for the study graph (spec §15.2 + §15.7 R11).
 *
 * Contract:
 *   - Both Phase-2 S2 and Phase-3 `close_open_question` must wrap their full
 *     [validate → write node files via tempdir+rename → swap index.json]
 *     critical section in `withGraphWriteLock`. Any non-locked write is a bug.
 *   - Stale-lock policy: 60s timeout. `proper-lockfile`'s PID-aliveness check
 *     auto-steals locks owned by dead processes.
 *   - Readers do NOT acquire the lock — they rely on atomic node writes plus
 *     the atomic `rename`-based index swap in `shared/graph.ts#writeIndexAtomic`.
 */

import lockfile from "proper-lockfile";
import { mkdir, writeFile, stat } from "node:fs/promises";
import path from "node:path";

const STALE_MS = 60_000;
const RETRIES = { retries: 10, factor: 1.5, minTimeout: 100, maxTimeout: 5_000 };

async function ensureLockfileTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    // `proper-lockfile` needs the target path to refer to a real file (it
    // creates a sibling `<target>.lock` directory). An empty JSON marker is
    // enough; the file is also gitignored.
    await writeFile(target, "{}\n", "utf8");
  }
}

export async function withGraphWriteLock<T>(
  studyDir: string,
  action: () => Promise<T>,
): Promise<T> {
  await mkdir(studyDir, { recursive: true });
  const lockfilePath = path.join(studyDir, ".graph.lock");
  await ensureLockfileTarget(lockfilePath);
  const release = await lockfile.lock(lockfilePath, {
    stale: STALE_MS,
    retries: RETRIES,
    realpath: false, // tests may use tempdirs whose realpath differs
  });
  try {
    return await action();
  } finally {
    await release();
  }
}
