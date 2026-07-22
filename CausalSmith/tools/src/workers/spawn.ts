import { execa } from "execa";
import { spawn as cpSpawn } from "node:child_process";

export interface SpawnWithTimeoutOpts {
  cwd?: string;
  env?: NodeJS.ProcessEnv;
  inactivityTimeoutMs: number;
  /**
   * Optional WALL-CLOCK cap. When set, the whole child tree is killed (SIGKILL
   * of the process group, same path as the inactivity watchdog) after this many
   * ms even while it is actively producing output, and `killedDueToTotalTimeout`
   * is set on the result. Needed for bounded warm-ups where inactivity alone is
   * useless: a cold `lake build` emits steady progress, so it never goes silent.
   */
  maxTotalMs?: number;
  input?: string;
  liveness?: {
    intervalMs: number;
    /**
     * `info.hasOutput` is true once the child has emitted ANY stdout/stderr; a
     * startup-stuck detector must treat a child that is already producing output
     * as started (the marker in its rollout may lag a slow MCP cold-start).
     */
    check: (info: {
      lastOutputAt: number;
      hasOutput: boolean;
    }) => Promise<{ ok: true } | { ok: false; reason: string }>;
  };
}

export interface SpawnWithTimeoutResult {
  stdout: string;
  stderr: string;
  killedDueToInactivity: boolean;
  killedDueToLiveness?: string;
  /** Set when the child tree was killed for exceeding `maxTotalMs` (wall-clock). */
  killedDueToTotalTimeout?: boolean;
  /** Child exit code; null when the child was killed or never settled. */
  exitCode: number | null;
}

/**
 * Kill `pid` AND its entire descendant tree.
 *
 * Why this exists (Windows lean-lsp hang, 2026-06-04): a claude/codex worker
 * that invokes a `mcp__lean-lsp__*` tool spawns `lean-lsp-mcp.exe`, which spawns
 * `python → lake → lean`. A bare `child.kill("SIGKILL")` on Windows kills only
 * the top `claude.exe`/`codex.exe`; the MCP grandchildren survive AND inherited
 * the worker's stdout write handle, so the pipe never closes and `await child`
 * hangs forever. `taskkill /T` tears down the whole tree so the pipe closes and
 * the await settles. On POSIX we spawn the child DETACHED (its own process
 * group) and SIGKILL the whole group: a bare SIGKILL of the direct child
 * (`bash -lc`) orphaned codex and its lean-lsp tree (`lean-lsp-mcp → python →
 * lake serve → lean workers`), which kept running — and kept EDITING the
 * worktree — after an inactivity kill, accumulating processes against the
 * cluster's limits.
 */
function killTree(pid: number | undefined, fallback: () => void): void {
  if (pid == null) {
    fallback();
    return;
  }
  if (process.platform === "win32") {
    try {
      cpSpawn("taskkill", ["/pid", String(pid), "/T", "/F"], { stdio: "ignore" });
    } catch {
      fallback();
    }
  } else {
    try {
      // Negative pid = the child's process group (child is spawned detached).
      process.kill(-pid, "SIGKILL");
    } catch {
      fallback();
    }
  }
}

export async function spawnWithInactivityTimeout(
  cmd: string,
  args: string[],
  opts: SpawnWithTimeoutOpts,
): Promise<SpawnWithTimeoutResult> {
  const child = execa(cmd, args, {
    cwd: opts.cwd,
    env: opts.env,
    reject: false,
    input: opts.input,
    // POSIX: own process group so killTree can SIGKILL the whole tree.
    detached: process.platform !== "win32",
  });

  let lastOutput = Date.now();
  let killedDueToInactivity = false;
  let killedDueToLiveness: string | undefined;

  // Parallel copy of the child's output. execa buffers internally too, but when
  // an inherited-pipe grandchild keeps stdout open after a kill (see killTree),
  // the execa promise can fail to settle; these buffers are the fallback source
  // so the worker still gets whatever the child managed to emit.
  const stdoutChunks: Buffer[] = [];
  const stderrChunks: Buffer[] = [];

  // Resolves once a kill path fires AND a short grace has elapsed without the
  // execa promise settling. Racing this against `child` guarantees the await
  // can never hang indefinitely on a grandchild-held pipe.
  let resolveKilled!: () => void;
  const killedPromise = new Promise<void>((res) => {
    resolveKilled = res;
  });
  let killing = false;
  function killNow(): void {
    if (killing) return;
    killing = true;
    killTree(child.pid, () => {
      try {
        child.kill("SIGKILL");
      } catch {
        /* already gone */
      }
    });
    // Grace window: a clean tree-kill closes the pipe and lets `await child`
    // settle on its own (preferred — full execa-captured output). If it hasn't
    // settled shortly after, fall back to the buffered copy.
    setTimeout(() => resolveKilled(), 5_000).unref?.();
  }

  // Exit-driven settle. The process 'exit' event fires when the child itself
  // terminates — BEFORE its stdio streams necessarily close. When a DETACHED
  // descendant inherited the stdout/stderr fd and keeps it open (see killTree),
  // execa's own promise never settles (it waits for stream EOF), so a command
  // that already SUCCEEDED would otherwise stall until the inactivity watchdog
  // killed it and reported it as a failure. We force-settle from the buffered
  // copy once the child has EXITED *and* its output has been QUIET for a grace
  // window. Gating on quiescence (not a blind post-exit timer) means a large
  // final payload still draining into `stdoutChunks` keeps `lastOutput` fresh and
  // we keep waiting — so we never truncate — while a held-open-but-silent pipe
  // still lets us return ~1 grace after exit instead of stalling for the whole
  // inactivity timeout. `exitedCode` is `undefined` until the child exits.
  const POST_EXIT_QUIET_MS = 1_000;
  // Absolute cap: a detached descendant that inherited the pipe and keeps WRITING
  // forever (not merely holding it open) would keep `lastOutput` fresh, so the
  // quiet window never trips and — with inactivity also never firing — the wait
  // would hang indefinitely. Cap the post-exit wait so we always settle. The
  // exitEvent branch then reaps the group, killing that chatty descendant.
  const POST_EXIT_MAX_MS = 10_000;
  let exitedCode: number | null | undefined;
  let exitedAt = 0;
  let resolveExited!: (v: { stdout: string; stderr: string; exitCode: number | null }) => void;
  const exitedPromise = new Promise<{ stdout: string; stderr: string; exitCode: number | null }>((res) => {
    resolveExited = res;
  });
  child.on("exit", (code) => {
    exitedCode = code;
    exitedAt = Date.now();
  });
  const exitSettleTimer = setInterval(() => {
    if (exitedCode === undefined) return;
    // Settle once the child has exited AND either output has gone quiet (clean
    // drain — nothing truncated) OR the absolute post-exit cap has elapsed
    // (bounded fallback for a still-emitting descendant).
    const quiet = Date.now() - lastOutput >= POST_EXIT_QUIET_MS;
    const capped = Date.now() - exitedAt >= POST_EXIT_MAX_MS;
    if (quiet || capped) {
      clearInterval(exitSettleTimer);
      resolveExited({
        stdout: Buffer.concat(stdoutChunks).toString("utf8"),
        stderr: Buffer.concat(stderrChunks).toString("utf8"),
        exitCode: exitedCode,
      });
    }
  }, 250);
  exitSettleTimer.unref?.();

  // Once the child has EXITED, the exit-settle path owns completion — no kill
  // may fire, else a step that already succeeded could be flagged
  // inactivity/liveness/total-timed-out (e.g. the child exits ~0 just before the
  // wall-clock cap, then the timer fires and mislabels the success). Every
  // kill-triggering timer below no-ops once `exitedCode` is set.
  // why: short inactivity budgets should be checked before the old fixed 30s poll delay.
  const watchdogIntervalMs = Math.min(
    30_000,
    Math.max(250, Math.floor(opts.inactivityTimeoutMs / 2)),
  );
  const watchdog = setInterval(() => {
    if (exitedCode !== undefined) return;
    if (Date.now() - lastOutput > opts.inactivityTimeoutMs) {
      killedDueToInactivity = true;
      clearInterval(watchdog);
      killNow();
    }
  }, watchdogIntervalMs);

  // Wall-clock cap (opt-in). Unlike the inactivity watchdog, this fires even
  // while the child is actively emitting output — for bounded warm-ups where a
  // steadily-progressing cold build must still be bounded.
  let killedDueToTotalTimeout = false;
  let totalTimer: NodeJS.Timeout | undefined;
  if (opts.maxTotalMs != null && opts.maxTotalMs > 0) {
    totalTimer = setTimeout(() => {
      if (exitedCode !== undefined) return; // exited before the cap → not a total-timeout
      killedDueToTotalTimeout = true;
      killNow();
    }, opts.maxTotalMs);
    totalTimer.unref?.();
  }

  let livenessTimer: NodeJS.Timeout | undefined;
  if (opts.liveness) {
    const { intervalMs, check } = opts.liveness;
    livenessTimer = setInterval(async () => {
      const result = await check({
        lastOutputAt: lastOutput,
        hasOutput: stdoutChunks.length + stderrChunks.length > 0,
      }).catch((err) => ({
        ok: false as const,
        reason: `liveness check threw: ${err instanceof Error ? err.message : String(err)}`,
      }));
      if (!result.ok) {
        if (exitedCode !== undefined) return; // exited already → don't mislabel as a liveness kill
        killedDueToLiveness = result.reason;
        if (livenessTimer) clearInterval(livenessTimer);
        killNow();
      }
    }, intervalMs);
  }

  child.stdout?.on("data", (d: Buffer) => {
    lastOutput = Date.now();
    stdoutChunks.push(Buffer.from(d));
  });
  child.stderr?.on("data", (d: Buffer) => {
    lastOutput = Date.now();
    stderrChunks.push(Buffer.from(d));
  });

  try {
    const settled = await Promise.race([
      child.then((r) => ({
        kind: "exit" as const,
        stdout: r.stdout,
        stderr: r.stderr,
        exitCode: r.exitCode ?? null,
      })),
      killedPromise.then(() => ({ kind: "killed" as const })),
      exitedPromise.then((e) => ({ kind: "exitEvent" as const, ...e })),
    ]);
    if (settled.kind === "exitEvent") {
      // We settled because the child EXITED but its stdio pipe was still held
      // open by a detached descendant. That descendant is still alive; reap it so
      // a straggler lean-lsp/lake/esbuild does not accumulate against the
      // cluster's process cap.
      //   POSIX: `process.kill(-pid)` targets the child's process group, whose id
      //   is the exited leader's pid — still reserved while a member lives (else a
      //   no-op ESRCH, swallowed by killTree's fallback). So the group is reaped.
      //   Windows: BEST-EFFORT only. `taskkill /pid <pid> /T` walks the tree from
      //   a LIVE pid; once the direct child has exited it cannot anchor the walk,
      //   so an orphaned descendant may survive (a correct fix needs a Job Object,
      //   out of scope here). Dev-only impact — the production cluster is POSIX.
      killTree(child.pid, () => {});
    }
    if (settled.kind === "exit" || settled.kind === "exitEvent") {
      return {
        stdout: settled.stdout,
        stderr: settled.stderr,
        killedDueToInactivity,
        killedDueToLiveness,
        killedDueToTotalTimeout,
        exitCode: settled.exitCode,
      };
    }
    // Killed and the execa promise did not settle within the grace window
    // (inherited-pipe edge case): reconstruct output from the buffered copy so
    // the worker returns instead of hanging forever.
    return {
      stdout: Buffer.concat(stdoutChunks).toString("utf8"),
      stderr: Buffer.concat(stderrChunks).toString("utf8"),
      killedDueToInactivity,
      killedDueToLiveness,
      killedDueToTotalTimeout,
      exitCode: null,
    };
  } finally {
    clearInterval(watchdog);
    clearInterval(exitSettleTimer);
    if (totalTimer) clearTimeout(totalTimer);
    if (livenessTimer) clearInterval(livenessTimer);
    // Never leave the execa promise unhandled (reject:false means it resolves,
    // but guard anyway) — and make sure the tree is gone if we bailed via buffers.
    void child.catch(() => {});
  }
}
