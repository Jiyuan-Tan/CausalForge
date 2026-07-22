/**
 * Single-concurrent `--extend` cap per spec §15.5.
 *
 * Implements a PID-stamped heartbeat at `<studyRoot>/.extend.active`. If an
 * existing heartbeat is present with a live PID and a recent mtime
 * (≤ 5 min), throw `extend_already_running`. Otherwise steal (treat as
 * stale) and proceed.
 *
 * The hand-rolled heartbeat is used rather than `proper-lockfile` so that
 * the lock survives across process boundaries with an explicit stale
 * window — `proper-lockfile`'s default `stale` heuristic would race the
 * graph-write lockfile semantics elsewhere.
 */
import { readFileSync, statSync, unlinkSync, writeFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";

const STALE_AFTER_MS = 5 * 60 * 1000;

function isPidAlive(pid: number): boolean {
  if (!Number.isFinite(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

export async function withExtendHeartbeat<T>(
  studyRoot: string,
  action: () => Promise<T>,
): Promise<T> {
  const hbPath = path.join(studyRoot, ".extend.active");
  const payload = `${process.pid} ${new Date().toISOString()}\n`;
  while (true) {
    try {
      // why: exclusive create closes the concurrent --extend startup race.
      writeFileSync(hbPath, payload, { flag: "wx" });
      break;
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code !== "EEXIST") throw err;
    }
    let raw = "";
    try {
      raw = readFileSync(hbPath, "utf8").trim();
    } catch {
      // unreadable; treat as stale
    }
    const pidStr = raw.split(/\s+/)[0] ?? "";
    const pid = Number(pidStr);
    let ageMs = Number.POSITIVE_INFINITY;
    try {
      ageMs = Date.now() - statSync(hbPath).mtimeMs;
    } catch {
      // missing race; retry exclusive create
      continue;
    }
    if (isPidAlive(pid) && ageMs < STALE_AFTER_MS) {
      throw Object.assign(
        new Error(
          `Another --extend run is in progress (PID ${pid}; heartbeat at ${hbPath}). Wait for it to finish or remove the heartbeat file manually if you are certain it is stale.`,
        ),
        { code: "extend_already_running" },
      );
    }
    try {
      unlinkSync(hbPath);
    } catch {
      // already gone
    }
  }
  try {
    return await action();
  } finally {
    try {
      const currentPid = Number(readFileSync(hbPath, "utf8").trim().split(/\s+/)[0] ?? "");
      if (currentPid === process.pid) unlinkSync(hbPath);
    } catch {
      // best-effort
    }
  }
}
