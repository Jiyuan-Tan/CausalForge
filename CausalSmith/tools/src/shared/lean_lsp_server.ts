import { spawn, type ChildProcess } from "node:child_process";
import net from "node:net";
import { localConfig, leanProjectPathFor } from "../local_config.js";

/**
 * A long-lived, SHARED `lean-lsp-mcp` server in streamable-HTTP mode.
 *
 * Why this exists (2026-06-17): every codex run we dispatch normally injects the
 * lean-lsp MCP in *stdio* mode (`-c mcp_servers.lean-lsp.command=…`), so each
 * codex PROCESS spawns its OWN `lean-lsp-mcp` → its OWN `lake serve`, and pays
 * the ~52s import-elaboration cold-start before its first probe. An F3 loop fans
 * out into many codex processes (reviewer + its subagents + per-target fillers +
 * convergence reviewers, times every loop iteration) so that cold-start is paid
 * a dozen+ times per run — the dominant slowness.
 *
 * `lean-lsp-mcp` already supports a shared model: in `--transport streamable-http`
 * it keeps ONE `LeanLSPClient` (= one `lake serve`) per project as a module-level
 * singleton, reused across ALL connecting sessions, and explicitly does NOT close
 * it on session end (see lean_lsp_mcp/server.py `app_lifespan` + client_utils
 * `_shared_clients`). So one HTTP server → one `lake serve`; every codex attaches
 * via `-c mcp_servers.<name>.url=…` instead of spawning its own. The cold-start is
 * paid ONCE for the server's lifetime; every later probe (across all codex
 * processes and their subagents) reuses the warm client.
 *
 * Lifecycle: `startSharedLeanLsp` boots the server and resolves once the port is
 * accepting connections (the `lake serve` cold-start itself is lazy — paid by the
 * first codex tool call, then shared). `stop()` kills the server, whose process
 * exit closes the shared `lake serve`.
 */
export interface SharedLeanLsp {
  /** `http://127.0.0.1:<port>/mcp` — pass to codex via `-c mcp_servers.<name>.url=`. */
  url: string;
  port: number;
  /** Kill the server (and, via its process exit, the shared `lake serve`). */
  stop: () => Promise<void>;
}

/** Ask the OS for a free TCP port by binding to :0, then releasing it. */
function findFreePort(): Promise<number> {
  return new Promise((resolve, reject) => {
    const srv = net.createServer();
    srv.unref();
    srv.on("error", reject);
    srv.listen(0, "127.0.0.1", () => {
      const addr = srv.address();
      if (addr && typeof addr === "object") {
        const { port } = addr;
        srv.close(() => resolve(port));
      } else {
        srv.close(() => reject(new Error("could not determine a free port")));
      }
    });
  });
}

/** Resolve once a TCP connection to (host, port) succeeds, or reject on timeout. */
function waitForPort(port: number, host: string, timeoutMs: number): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  return new Promise((resolve, reject) => {
    const tryOnce = () => {
      const sock = net.connect({ port, host });
      sock.once("connect", () => {
        sock.destroy();
        resolve();
      });
      sock.once("error", () => {
        sock.destroy();
        if (Date.now() > deadline) {
          reject(new Error(`lean-lsp HTTP server did not open port ${port} within ${Math.round(timeoutMs / 1000)}s`));
        } else {
          setTimeout(tryOnce, 300);
        }
      });
    };
    tryOnce();
  });
}

/**
 * Boot a shared streamable-HTTP `lean-lsp-mcp` for `repoRoot`'s lean project.
 * Resolves once the server is accepting connections. The caller is responsible
 * for calling `stop()` (typically in a `finally`).
 *
 * `maxOpenFiles` raises `LEAN_LSP_MAX_OPEN_FILES` (server default 4) so several
 * concurrent codex subagents, each opening a DIFFERENT target file, do not evict
 * each other's open documents and force re-elaboration.
 */
export async function startSharedLeanLsp(
  repoRoot: string,
  opts: { maxOpenFiles?: number; readyTimeoutMs?: number } = {},
): Promise<SharedLeanLsp> {
  const cfg = localConfig();
  const projectPath = leanProjectPathFor(repoRoot).replace(/\\/g, "/");
  const port = await findFreePort();
  const host = "127.0.0.1";

  const child: ChildProcess = spawn(
    cfg.leanLspMcpBinary,
    [
      "--transport",
      "streamable-http",
      "--host",
      host,
      "--port",
      String(port),
      "--lean-project-path",
      projectPath,
    ],
    {
      cwd: repoRoot,
      env: {
        ...process.env,
        MCP_TIMEOUT: String(cfg.mcpTimeoutMs),
        LEAN_LSP_MAX_OPEN_FILES: String(opts.maxOpenFiles ?? 8),
      },
      stdio: ["ignore", "pipe", "pipe"],
    },
  );

  // Surface a same-tick spawn failure (bad binary path) instead of hanging on
  // waitForPort until the timeout.
  let spawnError: Error | null = null;
  child.on("error", (err) => {
    spawnError = err instanceof Error ? err : new Error(String(err));
  });
  // Drain pipes so the child never blocks on a full stdout/stderr buffer; keep a
  // short tail for diagnostics if startup fails.
  let logTail = "";
  const onChunk = (buf: Buffer) => {
    logTail = (logTail + buf.toString("utf8")).slice(-4000);
  };
  child.stdout?.on("data", onChunk);
  child.stderr?.on("data", onChunk);

  const url = `http://${host}:${port}/mcp`;
  const stop = async (): Promise<void> => {
    if (child.exitCode !== null || child.signalCode !== null) return;
    await new Promise<void>((resolve) => {
      const done = () => resolve();
      child.once("exit", done);
      child.kill("SIGTERM");
      // Hard-kill if it ignores SIGTERM (its process exit is what closes the
      // shared `lake serve`, so we must ensure it actually dies).
      setTimeout(() => {
        if (child.exitCode === null && child.signalCode === null) child.kill("SIGKILL");
      }, 4000).unref();
    });
  };

  try {
    await waitForPort(port, host, opts.readyTimeoutMs ?? 60_000);
  } catch (err) {
    await stop();
    if (spawnError) {
      throw new Error(`failed to spawn lean-lsp-mcp ('${cfg.leanLspMcpBinary}'): ${(spawnError as Error).message}`);
    }
    throw new Error(`${(err as Error).message}\n  server log tail: ${logTail.trim().slice(-800)}`);
  }
  if (spawnError) {
    await stop();
    throw new Error(`failed to spawn lean-lsp-mcp ('${cfg.leanLspMcpBinary}'): ${(spawnError as Error).message}`);
  }

  return { url, port, stop };
}
