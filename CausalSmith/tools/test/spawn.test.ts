// CausalSmith/tools/test/spawn.test.ts
import { describe, it, expect } from "vitest";
import { execa } from "execa";
import { readFileSync, rmSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { spawnWithInactivityTimeout } from "../src/workers/spawn.js";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURE = path.join(HERE, "fixtures", "spawn_held_pipe.mts");

let fixtureSeq = 0;

/**
 * Run the fixture in a STANDALONE node process: vitest's worker delivers the
 * child `exit` event only once stdio closes (~when the pipe-holder dies), which
 * is exactly the coupling the exit-driven settle routes around, so an in-worker
 * call cannot observe it. Production runs the pipeline as a plain node/tsx
 * process, matching the fixture. Invoked via `node --import tsx/esm` (NOT
 * `npx tsx`, whose IPC-server startup hits `EPERM` on the pipe under a
 * restricted sandbox/CI). The fixture writes its result to a FILE (not stdout)
 * so a piped-stdout flush race can never truncate it.
 */
async function runFixture(cmd: string, inactivityMs: number, maxTotalMs?: number) {
  const outPath = path.join(os.tmpdir(), `spawn_fixture_${process.pid}_${fixtureSeq++}.json`);
  const argv = ["--import", "tsx/esm", FIXTURE, cmd, String(inactivityMs), outPath];
  if (maxTotalMs !== undefined) argv.push(String(maxTotalMs));
  try {
    await execa(process.execPath, argv, { cwd: path.join(HERE, "..") });
    return JSON.parse(readFileSync(outPath, "utf8")) as {
      elapsed: number;
      exitCode: number | null;
      killedDueToInactivity: boolean;
      killedDueToTotalTimeout: boolean;
      stdout: string;
    };
  } finally {
    rmSync(outPath, { force: true });
  }
}

describe("spawnWithInactivityTimeout", () => {
  // Regression: the verify chain (lake build / embed / doc:gen) is waited on via
  // this helper. When a command SUCCEEDS but leaves a detached descendant that
  // inherited the stdout fd, the pipe never EOFs, so execa's promise never
  // settles. Before the exit-driven settle, the only escape was the 30-min
  // inactivity watchdog -> kill -> exitCode null -> the caller treated the
  // already-successful build as a FAILURE and rolled it back. We now settle on
  // process exit with the REAL exit code, promptly.
  it("settles on child exit even when a SILENT descendant holds the stdout pipe open", async () => {
    // Backgrounds a silent `sleep` that holds stdout for 30s; the quiet-window
    // settle returns ~1s after exit (hard-capped at 10s), NOT after waiting out
    // the pipe. Threshold is generous (< 12s) so the exit-settle is unambiguously
    // distinguished from the 30s pipe-EOF even under heavy shared-cluster load
    // (the interval can be starved; measured ~1.3s idle, up to several s loaded).
    const r = await runFixture("sleep 30 & echo done; exit 0", 10_000);
    expect(r.exitCode).toBe(0);
    expect(r.killedDueToInactivity).toBe(false);
    expect(r.stdout).toContain("done");
    expect(r.elapsed).toBeLessThan(12_000);
  }, 60_000);

  it("still settles (bounded) when a CHATTY descendant keeps writing to the held pipe", async () => {
    // The descendant emits forever, so the quiet window never trips and
    // inactivity never fires; only the absolute post-exit cap (10s) bounds it.
    // Without that cap this would hang indefinitely.
    const r = await runFixture("while true; do echo tick; sleep 0.3; done & echo done; exit 0", 60_000);
    expect(r.exitCode).toBe(0);
    expect(r.killedDueToInactivity).toBe(false);
    expect(r.stdout).toContain("done");
    // Returns near the post-exit cap, NOT the 60s inactivity timeout.
    expect(r.elapsed).toBeLessThan(20_000);
  }, 60_000);

  it("does NOT flag total-timeout when the child EXITED before the cap", async () => {
    // Child exits 0 at once; a chatty descendant delays the exit-settle to the
    // 10s post-exit cap. maxTotalMs (3s) elapses in that window — but must NOT
    // flag a timeout, because the child already succeeded. (Regression: the
    // total-timer previously fired and mislabeled a success as timed-out.)
    const r = await runFixture(
      "while true; do echo tick; sleep 0.3; done & echo done; exit 0",
      60_000,
      3_000,
    );
    expect(r.exitCode).toBe(0);
    expect(r.killedDueToTotalTimeout).toBe(false);
    expect(r.killedDueToInactivity).toBe(false);
  }, 60_000);

  it("maxTotalMs tree-kills a steadily-emitting child and flags killedDueToTotalTimeout", async () => {
    // A cold `lake build` emits steady progress, so inactivity never trips — the
    // wall-clock cap is what must fire. A tight loop stands in for that here.
    const start = Date.now();
    const r = await spawnWithInactivityTimeout(
      "bash",
      ["-lc", "while true; do echo tick; sleep 0.2; done"],
      { inactivityTimeoutMs: 60_000, maxTotalMs: 2_000 },
    );
    expect(r.killedDueToTotalTimeout).toBe(true);
    expect(r.killedDueToInactivity).toBe(false);
    // Fired near the 2s cap, NOT the 60s inactivity timeout.
    expect(Date.now() - start).toBeLessThan(20_000);
  }, 30_000);

  it("still reports a genuine nonzero exit", async () => {
    const r = await spawnWithInactivityTimeout("bash", ["-lc", "echo boom; exit 3"], {
      inactivityTimeoutMs: 10_000,
    });
    expect(r.exitCode).toBe(3);
    expect(r.killedDueToInactivity).toBe(false);
    expect(r.stdout).toContain("boom");
  }, 20_000);
});
