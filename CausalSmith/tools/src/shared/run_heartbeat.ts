/**
 * Per-qid run heartbeat for causalsmith pipelines.
 *
 * Replaces the global `findActiveStates` gate in `initializeOrLoadState` with
 * a per-qid concurrency lock. Two `/causalsmith` invocations on distinct qids
 * can run side by side; a second invocation on the same qid is refused.
 *
 * Heartbeat file: `<formalizationDir(qid)>/logs/.run.active`
 *   line 1: `<pid> <specialization> <iso-timestamp> <unique-owner-token>`
 *
 * The actual mutex is `proper-lockfile`'s atomic sibling lock directory; the
 * heartbeat file is owner metadata for operators. This makes stale recovery
 * and simultaneous contenders single-writer safe.
 *
 * Bypass: `CAUSALSMITH_ALLOW_PARALLEL=1` skips the check entirely (preserves the
 * existing escape hatch used by tests and by operators who know what they're
 * doing).
 *
 * Legacy migration: a live PID recorded by the former heartbeat-only scheme is
 * still honored even when no sibling lock directory exists.
 */
import { existsSync, mkdirSync, readFileSync, statSync, unlinkSync, utimesSync, writeFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { randomUUID } from "node:crypto";
import lockfile from "proper-lockfile";

import { ensureLogsDir } from "../paths.js";

const LOCK_STALE_MS = 30 * 60 * 1000;
// Refresh the metadata mtime for operator visibility; proper-lockfile updates
// its own mutex mtime independently.
const HEARTBEAT_REFRESH_INTERVAL_MS = 5 * 60 * 1000;

function isPidAlive(pid: number): boolean {
  if (!Number.isFinite(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

export interface ExistingHeartbeat {
  pid: number;
  specialization: string;
  timestamp: string;
  ownerToken: string;
  path: string;
}

function readHeartbeat(hbPath: string): ExistingHeartbeat | null {
  if (!existsSync(hbPath)) return null;
  let raw = "";
  try {
    raw = readFileSync(hbPath, "utf8").trim();
  } catch {
    return null;
  }
  const [pidStr, specialization = "", timestamp = "", ownerToken = ""] = raw.split(/\s+/);
  const pid = Number(pidStr);
  if (!Number.isFinite(pid)) return null;
  return { pid, specialization, timestamp, ownerToken, path: hbPath };
}

export async function withRunHeartbeat<T>(
  repoRoot: string,
  qid: string,
  specialization: string,
  action: () => Promise<T>,
): Promise<T> {
  return withRunHeartbeatAt(ensureLogsDir(repoRoot, qid), qid, specialization, action);
}

/**
 * Run a single-writer heartbeat in an explicit log directory.
 *
 * Presentation mode owns a different output tree from formalization mode, but
 * needs the same protection: concurrent writers must never mutate one paper
 * bundle at the same time.  Keep the locking mechanics centralized here while
 * letting each mode choose its own durable log directory.
 */
export async function withRunHeartbeatAt<T>(
  logDirectory: string,
  qid: string,
  specialization: string,
  action: () => Promise<T>,
): Promise<T> {
  if (process.env.CAUSALSMITH_ALLOW_PARALLEL === "1") {
    return action();
  }
  // The heartbeat is colocated with the durable per-run logs, so a stale lock
  // is visible to the operator alongside the agent-call transcript.
  mkdirSync(logDirectory, { recursive: true });
  const hbPath = path.join(logDirectory, ".run.active");

  // Honor a live owner from the former heartbeat-only implementation. New
  // contenders are serialized by the sibling `.run.active.lock` directory.
  const existing = readHeartbeat(hbPath);
  if (existing && isPidAlive(existing.pid)) {
    let ageMs = Number.POSITIVE_INFINITY;
    try {
      ageMs = Date.now() - statSync(hbPath).mtimeMs;
    } catch {
      // missing race; treat as stale
    }
    const ageS = Math.round(ageMs / 1000);
    throw Object.assign(
      new Error(
        `another causalsmith run is active on qid ${qid} ` +
          `(spec ${existing.specialization || "?"}, PID ${existing.pid}, ` +
          `heartbeat age ${ageS}s at ${hbPath}). ` +
          `Wait for it to finish, kill PID ${existing.pid} and remove the ` +
          `heartbeat if you are certain it is stale, or set ` +
          `CAUSALSMITH_ALLOW_PARALLEL=1 to bypass.`,
      ),
      { code: "causalsmith_qid_busy" },
    );
  }

  if (!existsSync(hbPath)) {
    try {
      writeFileSync(hbPath, "\n", { flag: "wx" });
    } catch {
      // Another contender created the lock target.
    }
  }
  let release: (() => Promise<void>) | null = null;
  try {
    release = await lockfile.lock(hbPath, {
      stale: LOCK_STALE_MS,
      update: HEARTBEAT_REFRESH_INTERVAL_MS,
      retries: 0,
      realpath: false,
    });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ELOCKED") {
      const winner = readHeartbeat(hbPath);
      throw Object.assign(
        new Error(
          `another causalsmith run just claimed qid ${qid}` +
            `${winner ? ` (spec ${winner.specialization || "?"}, PID ${winner.pid})` : ""}.`,
        ),
        { code: "causalsmith_qid_busy" },
      );
    }
    throw err;
  }

  const ownerToken = randomUUID();
  const payload = `${process.pid} ${specialization} ${new Date().toISOString()} ${ownerToken}\n`;
  writeFileSync(hbPath, payload);
  // Periodic mtime refresh — see HEARTBEAT_REFRESH_INTERVAL_MS comment.
  const refreshTimer = setInterval(() => {
    try {
      if (readHeartbeat(hbPath)?.ownerToken !== ownerToken) return;
      const now = new Date();
      utimesSync(hbPath, now, now);
    } catch {
      // best-effort: heartbeat may have been stolen or deleted out-of-band.
    }
  }, HEARTBEAT_REFRESH_INTERVAL_MS);
  // Don't keep the event loop alive solely on this timer.
  if (typeof refreshTimer.unref === "function") refreshTimer.unref();
  try {
    return await action();
  } finally {
    clearInterval(refreshTimer);
    try {
      // Only unlink if we still own it. A unique token (not merely PID) also
      // distinguishes overlapping calls made by the same long-lived process.
      const current = readHeartbeat(hbPath);
      if (current?.ownerToken === ownerToken) {
        unlinkSync(hbPath);
      }
    } catch {
      // best-effort
    }
    if (release) await release();
  }
}
