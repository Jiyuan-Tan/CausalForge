// Single source of truth for machine-specific paths the pipeline needs.
//
// Edit ONE file — `tools/config/local.json` (gitignored; copy from
// `local.example.json`) — instead of hunting hardcoded paths across workers.
// Every value may also be overridden by an env var (env wins over the file),
// so CI / cluster runs can set env without editing the file.
//
// Fields:
//   gitBashPath      — Windows only: absolute path to git-bash `bash.exe`. The
//                      headless `claude` CLI refuses to run without it
//                      (CLAUDE_CODE_GIT_BASH_PATH). Leave null on Linux.
//   leanLspMcpBinary — `lean-lsp-mcp` server binary (PATH name or absolute).
//   leanProjectPath  — optional override for lean-lsp `--lean-project-path`;
//                      null ⇒ use the run's repoRoot (the lake project that
//                      transitively sees Causalean).
//   mcpTimeoutMs     — MCP_TIMEOUT for the (slow-cold-starting) lean-lsp server.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

export interface LocalConfig {
  gitBashPath?: string;
  leanLspMcpBinary: string;
  leanProjectPath?: string;
  mcpTimeoutMs: number;
}

const CONFIG_DIR = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "config",
);
const LOCAL_JSON = path.join(CONFIG_DIR, "local.json");

let cached: LocalConfig | null = null;

function parsePositiveIntegerConfig(name: string, value: unknown): number {
  const n = Number(String(value).trim());
  if (!Number.isFinite(n) || !Number.isInteger(n) || n <= 0) {
    // why: NaN timeout values propagate into MCP startup and hide config typos.
    throw new Error(`Invalid ${name}: ${String(value)} (expected a positive integer milliseconds value)`);
  }
  return n;
}

export function localConfig(): LocalConfig {
  if (cached) return cached;
  let file: Partial<LocalConfig> = {};
  try {
    if (fs.existsSync(LOCAL_JSON)) {
      file = JSON.parse(fs.readFileSync(LOCAL_JSON, "utf8")) as Partial<LocalConfig>;
    }
  } catch (err) {
    // Malformed local.json → fall back to env + defaults. Do NOT swallow
    // silently: a single-backslash Windows path (`E:\App\bash.exe`) is invalid
    // JSON, and a silent fallback strips `gitBashPath`, which makes every
    // headless `claude` worker fail on Windows with a misleading git-bash error.
    // Warn loudly so the real cause is visible. (Use forward slashes or `\\`.)
    console.warn(
      `[local_config] FAILED to parse ${LOCAL_JSON}: ${
        err instanceof Error ? err.message : String(err)
      }\n  -> falling back to env vars + defaults. gitBashPath/leanLspMcpBinary may be unset.` +
        `\n  -> Windows paths must use forward slashes or escaped backslashes (e.g. "E:/App/bash.exe").`,
    );
  }
  cached = {
    gitBashPath:
      process.env.CLAUDE_CODE_GIT_BASH_PATH ?? file.gitBashPath ?? undefined,
    leanLspMcpBinary:
      process.env.CAUSALSMITH_LEAN_LSP_MCP ?? file.leanLspMcpBinary ?? "lean-lsp-mcp",
    leanProjectPath:
      process.env.CAUSALSMITH_LEAN_PROJECT_PATH ?? file.leanProjectPath ?? undefined,
    // 10 min default: heavy concrete scaffolds (measure-theoretic estimator /
    // model-class defs) elaborate well past the old 2-min limit, so a reviewer's
    // lean-lsp vacuity probe on the active file times out even after a successful
    // pre-warm. Raised so probes on heavy-but-valid scaffolds can complete; the
    // F2.5 probe-unavailable downgrade is the backstop if they still don't.
    // Override via MCP_TIMEOUT env or local config file.
    mcpTimeoutMs: parsePositiveIntegerConfig(
      "MCP_TIMEOUT",
      process.env.MCP_TIMEOUT ?? file.mcpTimeoutMs ?? 600000,
    ),
  };
  return cached;
}

/** Lean-lsp project root: the configured override, else the run's repoRoot. */
export function leanProjectPathFor(repoRoot: string): string {
  return localConfig().leanProjectPath || repoRoot;
}

/**
 * Inject worker-required env once at CLI startup so every spawned worker
 * inherits it: the `claude` CLI needs `CLAUDE_CODE_GIT_BASH_PATH` on Windows,
 * and lean-lsp wants a generous `MCP_TIMEOUT`. Idempotent; never overrides an
 * env var the caller already set.
 */
export function applyWorkerEnv(): void {
  const c = localConfig();
  if (c.gitBashPath && !process.env.CLAUDE_CODE_GIT_BASH_PATH) {
    process.env.CLAUDE_CODE_GIT_BASH_PATH = c.gitBashPath;
  }
  if (!process.env.MCP_TIMEOUT) {
    process.env.MCP_TIMEOUT = String(c.mcpTimeoutMs);
  }
}
