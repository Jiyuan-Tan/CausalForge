/**
 * Single-writer, crash-safe updates for the append-only markdown ledgers
 * (`SUBSTRATE_DEBT.md`, `CITED_DEPENDENCIES.md`).
 *
 * These files are GLOBAL: every qid/spec appends to the same table. The previous
 * read → append-in-memory → `writeFile` sequence held no lock and was not atomic, so two runs
 * recording gates concurrently each wrote a whole file computed from a pre-read snapshot and the
 * last writer erased the other's rows — while both reported success. A crash mid-write could also
 * leave a truncated ledger. Since the ledger is the externally visible record of disclosed
 * substrate debt, a silently dropped row is a disclosure failure, not a cosmetic one.
 *
 * Mirrors `graph_lock.ts`: `proper-lockfile` on a sibling marker (PID-aliveness steals locks from
 * dead processes), then temp-file + `rename` so a reader never observes a partial ledger.
 */

import lockfile from "proper-lockfile";
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, writeFile, stat } from "node:fs/promises";
import path from "node:path";

const STALE_MS = 60_000;
const RETRIES = { retries: 10, factor: 1.5, minTimeout: 100, maxTimeout: 5_000 };

async function ensureLockfileTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    // `proper-lockfile` needs its target to be a real file; it creates a sibling `.lock` dir.
    await writeFile(target, "{}\n", "utf8");
  }
}

/**
 * Serialize same-process writers per path. `proper-lockfile` guards across PROCESSES, but it
 * resolves in-process contention only by retry+backoff, which is both slow and (past the retry
 * budget) failure-prone when several stages in one run record gates at once. Queueing here means
 * the file lock is only ever contended between distinct processes.
 */
const inProcessQueue = new Map<string, Promise<unknown>>();

/**
 * Apply `mutate` to the ledger at `file` under an exclusive lock, writing atomically.
 *
 * `mutate` receives the CURRENT body (read inside the lock — never a stale snapshot) seeded with
 * `header` when the file does not exist, and returns the new body. It must be pure and must not
 * perform I/O. Returns `file` when the body changed, `undefined` when the mutation was a no-op.
 */
export async function updateLedgerFile(
  file: string,
  header: string,
  mutate: (body: string) => string,
): Promise<string | undefined> {
  const prior = inProcessQueue.get(file) ?? Promise.resolve();
  // Chain off the prior turn's SETTLEMENT (not its value) so one failed update cannot poison the
  // queue for later writers.
  const mine = prior.then(
    () => lockedUpdate(file, header, mutate),
    () => lockedUpdate(file, header, mutate),
  );
  inProcessQueue.set(file, mine.catch(() => undefined));
  return mine;
}

async function lockedUpdate(
  file: string,
  header: string,
  mutate: (body: string) => string,
): Promise<string | undefined> {
  await mkdir(path.dirname(file), { recursive: true });
  const lockPath = `${file}.lock`;
  await ensureLockfileTarget(lockPath);
  const release = await lockfile.lock(lockPath, {
    stale: STALE_MS,
    retries: RETRIES,
    realpath: false, // tests use tempdirs whose realpath may differ
  });
  try {
    const before = existsSync(file) ? await readFile(file, "utf8") : header;
    const after = mutate(before);
    if (after === before) return undefined;
    const tmp = `${file}.new`;
    await writeFile(tmp, after, "utf8");
    await rename(tmp, file);
    return file;
  } finally {
    await release();
  }
}
