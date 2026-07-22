import { open, readdir, stat } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { localConfig, leanProjectPathFor } from "../local_config.js";
import { MODELS } from "../models.js";

/**
 * Canonical codex dispatcher. Used by every research stage today and (per
 * spec §8.2) the future study pipeline as well. Logic is verbatim from the
 * prior `workers/codex.ts`; that path is now a re-export shim so existing
 * imports continue to work.
 */
export interface CodexRunInput {
  prompt: string;
  model?: string;
  reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
  cwd: string;
  /**
   * Lean project's package root when the agent itself runs from a narrower
   * scratch directory. Defaults to the cwd for existing callers.
   */
  leanProjectPath?: string;
  inactivityTimeoutMs?: number;
  startupTimeoutMs?: number;
  /**
   * Configure the `lean-lsp` MCP server for this codex run. `--full-auto` does
   * NOT auto-enable MCP — servers must be configured explicitly (per OpenAI
   * Codex docs), so we inject the server inline via `-c mcp_servers.lean-lsp.*`
   * rather than touching global `~/.codex/config.toml`.
   *
   * DEFAULT-ON: every codex call gets lean-lsp unless it explicitly opts out
   * with `leanLsp: false`. Rationale (user policy 2026-06-04): the F2.5 gate
   * was loose precisely because a Lean-reviewing stage lacked lean-lsp and its
   * "required" probes silently no-op'd; making it the default removes that whole
   * class of bug. Pure-math discovery stages pay a lean-lsp cold-start they do
   * not use — opt those out with `leanLsp: false` if the latency matters.
   */
  leanLsp?: boolean;
  /**
   * Enable codex's NATIVE sub-agent fan-out (`spawn_agent`) for THIS call —
   * codex spawning its own server-side worker threads inside one `codex exec`
   * session (distinct from the pipeline's own fan-out of N independent codex
   * processes, which always applies and is what drives per-object accuracy).
   *
   * DEFAULT-OFF (opt-in). Two hard preconditions before setting it true:
   *   1. THIS call's PROMPT must actually invoke `spawn_agent` — otherwise the
   *      flag only registers an idle multi-agent session for no benefit.
   *   2. The call must be dispatched at LOW concurrency (ideally a lone codex,
   *      not inside a wide `mapLimit` wave). Many concurrent multi-agent
   *      sessions DEADLOCK the shared app-server daemon (2026-06-28: a client
   *      parks in `futex_wait` forever while pinging liveness, defeating the
   *      inactivity timeout, so the whole run hangs). The concurrent reviewer/
   *      filler waves must therefore leave this OFF.
   * `CAUSALSMITH_CODEX_MULTI_AGENT=1` forces it on globally (escape hatch / debug).
   */
  multiAgent?: boolean;
  /**
   * Enable codex's hosted live web search (`-c tools.web_search=true`: the native
   * Responses `web_search` tool — server-side search + open_page, no approval and
   * NO sandbox network egress). DEFAULT-ON: the literature scout (Stage -1.1),
   * the D-0.5 citation reviewer, and D0 salvage all depend on reading the web,
   * and the tool is inert unless the prompt calls it. Opt out with
   * `webSearch: false` for stages that never touch the web (e.g. pure proof fill)
   * if the extra tool surface is unwanted.
   */
  webSearch?: boolean;
}

/**
 * Inline `-c mcp_servers.lean-lsp.*` flags so codex can call the lean-lsp MCP
 * tools. DEFAULT-ON: emitted for every call unless `input.leanLsp === false`.
 * Forward slashes avoid TOML backslash-escaping on Windows; the Python lean-lsp
 * server accepts them.
 *
 * SHARED-SERVER MODE: when `CAUSALSMITH_SHARED_LEAN_LSP_URL` is set (a launcher —
 * e.g. the F3 loop — booted one streamable-HTTP `lean-lsp-mcp` via
 * `startSharedLeanLsp` and exported its URL), every codex run attaches to that
 * ONE server instead of spawning its own stdio `lean-lsp-mcp`/`lake serve`. This
 * collapses N per-process cold-starts to 1 for the whole run, and the warm
 * `lake serve` is shared across the reviewer, its subagents, and the fillers.
 * We DISABLE the inherited stdio `lean-lsp` (so it does not also auto-spawn its
 * own server) and register the shared one under a distinct name. The stdio entry
 * is kept structurally valid (command/args present) but `enabled=false`, so the
 * disable is robust whether or not the global `~/.codex/config.toml` defines
 * `lean-lsp`.
 */
function leanLspCodexFlags(input: CodexRunInput): string[] {
  if (input.leanLsp === false) return [];
  const cfg = localConfig();
  const projectPath = (input.leanProjectPath ?? leanProjectPathFor(input.cwd)).replace(/\\/g, "/");
  const sharedUrl = process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL?.trim();
  if (sharedUrl) {
    const kv = [
      // Keep a structurally-valid stdio entry but turn it OFF so it does not
      // spawn its own server alongside the shared one.
      `mcp_servers.lean-lsp.command=${JSON.stringify(cfg.leanLspMcpBinary)}`,
      `mcp_servers.lean-lsp.args=["--lean-project-path", ${JSON.stringify(projectPath)}]`,
      `mcp_servers.lean-lsp.enabled=false`,
      // The shared streamable-HTTP server (one `lake serve` for the whole run).
      `mcp_servers.leanshared.url=${JSON.stringify(sharedUrl)}`,
    ];
    return kv.map((s) => `-c ${shellQuote(s)}`);
  }
  const kv = [
    `mcp_servers.lean-lsp.command=${JSON.stringify(cfg.leanLspMcpBinary)}`,
    `mcp_servers.lean-lsp.args=["--lean-project-path", ${JSON.stringify(projectPath)}]`,
    `mcp_servers.lean-lsp.env.MCP_TIMEOUT=${JSON.stringify(String(cfg.mcpTimeoutMs))}`,
  ];
  return kv.map((s) => `-c ${shellQuote(s)}`);
}

/**
 * Thrown when the codex child was watchdog-killed or exited nonzero. Callers
 * that tolerate job-level failure (the F3 per-job dispatch, bucket fixes)
 * already wrap dispatches in `.catch`; stage-level callers let it propagate so
 * the run fails LOUDLY and resumably — previously a 20-min-inactivity kill
 * returned truncated stdout. `parseStageOutput` now returns `parse_failed`, and
 * callers fail closed instead of advancing on garbage.
 */
export class CodexRunError extends Error {
  constructor(
    message: string,
    public readonly stdout: string,
    public readonly stderr: string,
  ) {
    super(message);
    this.name = "CodexRunError";
  }
}

export async function runCodex(input: CodexRunInput): Promise<{ stdout: string; stderr: string }> {
  // The nvm prelude is cluster-specific (default shell node is too old there).
  // Guard it so a machine without nvm — e.g. local Windows git-bash, where
  // codex + a recent node are already on PATH — skips the nvm steps instead of
  // aborting the `&&` chain before `codex exec` ever runs. On the cluster
  // `~/.nvm/nvm.sh` exists, so the strict `source && nvm use` semantics are
  // preserved exactly (a failed `nvm use` still aborts via the `if` body).
  const setup = [
    "unset npm_config_prefix",
    "if [ -s ~/.nvm/nvm.sh ]; then . ~/.nvm/nvm.sh && nvm use 20.20.2 >/dev/null 2>&1; fi",
  ].join(" && ");
  const cmd = [
    "codex exec --full-auto",
    `-C ${shellQuote(input.cwd)}`,
    "--skip-git-repo-check",
    // Windows: the default `elevated` sandbox setup helper fails to spawn on
    // codex-cli 0.133.x (`windows sandbox: spawn setup refresh`, OS error 740 —
    // see openai/codex#24098, #25362). The `unelevated` sandbox is the documented
    // workaround and runs commands fine; verified `SANDBOX_OK`. Key is ignored on
    // non-Windows hosts (the cluster), so it is safe to pass unconditionally.
    //
    // NOTE: we deliberately do NOT enable `sandbox_workspace_write.network_access`.
    // Stages that need to read a paper use codex's HOSTED `web_search` tool
    // (search + open_page) — server-side, outside the sandbox. That tool is NOT
    // on by default; it is enabled by the `tools.web_search` override below. So the
    // sandbox stays network-off (no raw egress to the autonomous agent) while the
    // hosted web search is available to stages that need it (Stage -1.1 scout,
    // D-0.5 citation review, D0 salvage).
    "-c windows.sandbox=unelevated",
    // Default fallback tier is mechanical (gpt-5.6-terra); every hard-math / kernel caller
    // passes an explicit `input.model` (codexKernel = gpt-5.5), so this default only applies
    // to unspecified/clerical codex calls.
    `-c model=${shellQuote(input.model ?? MODELS.codexMechanical)}`,
    `-c model_reasoning_effort=${shellQuote(input.reasoningEffort ?? "high")}`,
    // Hosted live web search (`web_search`, server-side, no sandbox egress).
    // DEFAULT-ON; opt out with `webSearch: false`. Inert unless the prompt calls
    // it. NB: the interactive `--search` flag does NOT exist on `codex exec`;
    // the equivalent is the `tools.web_search` config override.
    ...(input.webSearch === false ? [] : ["-c tools.web_search=true"]),
    // codex's native sub-agent fan-out (`spawn_agent`, a SERVER-SIDE thread inside ONE
    // `codex exec` session — distinct from the pipeline's OWN fan-out of N independent
    // `codex exec` processes via mapLimit, which is where the per-object accuracy comes
    // from and is unaffected by this flag). DORMANT in practice: NO prompt invokes
    // `spawn_agent` — the only mention is the reviewer prompt telling codex NOT to spawn —
    // so enabling it adds a multi-agent session to the shared app-server daemon for no
    // benefit. Under the pipeline's concurrent dispatch (×6) those idle sessions DEADLOCK
    // the daemon (2026-06-28): one client parks in `futex_wait` forever while still emitting
    // liveness pings, so the 20-min inactivity timeout below never fires and the run hangs
    // (seen 2× — 6h41m and 29m). Gated OFF by default (OPT-IN): the pipeline already fans out N
    // independent `codex exec` processes itself, so the concurrent reviewer/filler waves (P1, P2,
    // proof fillers, …) must NOT also let each codex spawn server-side sub-agents. Enable PER CALL
    // with `multiAgent: true` (see CodexRunInput for the two preconditions — the prompt must use
    // `spawn_agent` AND the call must run at low concurrency), or globally with
    // CAUSALSMITH_CODEX_MULTI_AGENT=1 (escape hatch). NOTE: the v2 concurrency knob is
    // `multi_agent.max_concurrent_threads_per_session` — the legacy `agents.max_threads`
    // ERRORS when `multi_agent_v2` is enabled.
    ...(input.multiAgent === true || process.env.CAUSALSMITH_CODEX_MULTI_AGENT === "1"
      ? [
          "-c features.multi_agent_v2=true",
          "-c multi_agent.non_code_mode_only=false",
          "-c multi_agent.max_concurrent_threads_per_session=4",
        ]
      : []),
    ...leanLspCodexFlags(input),
  ].join(" ");
  const script = `${setup} && ${cmd}`;

  const spawnedAt = Date.now();
  // Shared hosts can legitimately queue the code-mode host for several
  // minutes before the first rollout record or child output appears.  A live
  // run on 2026-07-12 took ~229s to reach code-mode startup, so the former
  // 180s default killed healthy queued reviewers.  This remains only the
  // pre-start window; once started, the independent inactivity watchdog below
  // still detects genuinely silent hangs.
  const startupTimeoutMs = input.startupTimeoutMs ?? 10 * 60 * 1000;
  // Per-call marker appended to the prompt and searched for in the rollout
  // file. The old check accepted ANY fresh ~/.codex/sessions/*.jsonl, so with
  // two pipeline runs in flight the OTHER run's session satisfied it and the
  // stuck-startup detector never fired. The marker scopes the check to THIS
  // call; codex records the submitted prompt in the rollout's first records.
  const marker = `causalsmith-session-marker:${spawnedAt.toString(36)}-${Math.random()
    .toString(36)
    .slice(2, 10)}`;
  const promptWithMarker = `${input.prompt}\n\n[${marker}] — machine tag for run-liveness tracking; ignore.`;
  const result = await spawnWithInactivityTimeout("bash", ["-lc", script], {
    cwd: input.cwd,
    env: process.env,
    // Fix ②: LONG inactivity timeout — resets on ANY child output, so a worker that is still making
    // progress (a hard lean-lsp elaboration, a slow filler) is NEVER killed and its work is never
    // lost; only a genuinely SILENT hang (no output for the whole window) trips it, and then it throws
    // a resumable CodexRunError (below) rather than hanging. Deliberately NO wall-clock `maxTotalMs`
    // here, since that would kill an actively-producing worker. 25m: because it measures INACTIVITY
    // (no output at all), 25m of total silence is already a strong genuine-hang signal, while a
    // long-but-live proof attempt keeps emitting output and is never cut off.
    inactivityTimeoutMs: input.inactivityTimeoutMs ?? 25 * 60 * 1000,
    input: promptWithMarker,
    liveness: {
      intervalMs: 15_000,
      check: async ({ hasOutput }) => {
        if (await codexSessionStarted(spawnedAt, marker)) return { ok: true };
        // A codex that is already emitting stdout/stderr has STARTED — the
        // session-rollout marker can lag a slow lean-lsp MCP cold-start, so the
        // marker alone is not a reliable startup signal. Only a codex that is
        // BOTH marker-less AND silent past the startup window is genuinely
        // stuck; a real hang AFTER startup is caught by the inactivity timeout.
        // (`hasOutput` is unambiguous to THIS child, so it also avoids the
        // cross-run session aliasing the marker was added to prevent.)
        if (Date.now() - spawnedAt > startupTimeoutMs && !hasOutput) {
          return {
            ok: false,
            reason: `codex produced no output and no session-rollout marker within ${Math.round(
              startupTimeoutMs / 1000,
            )}s — assumed stuck`,
          };
        }
        return { ok: true };
      },
    },
  });
  const killed =
    result.killedDueToLiveness ??
    (result.killedDueToInactivity
      ? `inactivity timeout (${Math.round((input.inactivityTimeoutMs ?? 25 * 60 * 1000) / 60000)}m without output)`
      : null);
  if (killed) {
    throw new CodexRunError(
      `codex killed: ${killed}. stderr-tail=${result.stderr.trim().slice(-300)}`,
      result.stdout,
      result.stderr,
    );
  }
  if (result.exitCode !== null && result.exitCode !== 0) {
    throw new CodexRunError(
      `codex exited ${result.exitCode}. stderr-tail=${result.stderr.trim().slice(-300)}`,
      result.stdout,
      result.stderr,
    );
  }
  return { stdout: result.stdout, stderr: result.stderr };
}

async function codexSessionStarted(after: number, marker: string): Promise<boolean> {
  const root = path.join(os.homedir(), ".codex", "sessions");
  const candidates: string[] = [];
  await collectNewerJsonl(root, after, 3, candidates);
  for (const file of candidates) {
    if (await fileHeadContains(file, marker)) return true;
  }
  return false;
}

async function collectNewerJsonl(
  dir: string,
  after: number,
  depth: number,
  out: string[],
): Promise<void> {
  let entries;
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory() && depth > 0) {
      await collectNewerJsonl(full, after, depth - 1, out);
      continue;
    }
    if (entry.isFile() && entry.name.endsWith(".jsonl")) {
      const s = await stat(full).catch(() => null);
      if (s && s.mtimeMs > after) out.push(full);
    }
  }
}

/** Search the first 256KB of a file for `needle` (the prompt — and with it the
 * marker — lands in a rollout's first few records, after ~20KB of base
 * instructions). */
async function fileHeadContains(file: string, needle: string): Promise<boolean> {
  try {
    const fh = await open(file, "r");
    try {
      const buf = Buffer.alloc(256 * 1024);
      const { bytesRead } = await fh.read(buf, 0, buf.length, 0);
      return buf.toString("utf8", 0, bytesRead).includes(needle);
    } finally {
      await fh.close();
    }
  } catch {
    return false;
  }
}

function shellQuote(value: string): string {
  return `'${value.replaceAll("'", "'\\''")}'`;
}
