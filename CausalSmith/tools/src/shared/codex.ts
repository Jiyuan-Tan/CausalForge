import { open, readdir, stat, mkdir, readFile, writeFile, copyFile, chmod } from "node:fs/promises";
import { createHash } from "node:crypto";
import lockfile from "proper-lockfile";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { codexHome, redactSecrets, resolveProviderAuth, workerEnv } from "../auth.js";
import {
  localConfig,
  leanProjectPathFor,
  type LocalConfig,
} from "../local_config.js";
import { MODELS } from "../models.js";
import type { ModelTokenUsage } from "../token_usage.js";

/**
 * Canonical codex dispatcher. Used by every research stage today and (per
 * spec §8.2) the future study pipeline as well. Logic is verbatim from the
 * prior `workers/codex.ts`; that path is now a re-export shim so existing
 * imports continue to work.
 */
/**
 * Absolute path to the shared Node resolver sourced by every codex shell.
 * Forward slashes so the string survives bash on Windows too.
 */
const NODE_ENV_SCRIPT = path
  .resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "scripts", "node_env.sh")
  .replace(/\\/g, "/");

export interface CodexRunInput {
  prompt: string;
  model?: string;
  reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
  cwd: string;
  /**
   * This call intentionally edits production files outside the paper-local
   * scratch directory. Formalization stages F2.5--F4 normally run Codex from
   * `<leanDir>/tmp` so disposable probes cannot pollute the package root; a
   * source-producing nested call (F2 redirect or F3 filler) must opt back into
   * its explicit `cwd`, so the dispatcher and prompt agree on the production
   * tree the worker is meant to edit.
   */
  productionWrite?: boolean;
  /**
   * Lean project's package root when the agent itself runs from a narrower
   * scratch directory. Defaults to the cwd for existing callers.
   */
  leanProjectPath?: string;
  inactivityTimeoutMs?: number;
  startupTimeoutMs?: number;
  /**
   * Configure the `lean-lsp` MCP server for this codex run. `codex exec` does
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
  /** Per-call sandbox narrowing. Cold referees use `read-only` even when the
   *  host configuration permits workspace writes. A call may never broaden
   *  the configured sandbox through this field. */
  sandboxMode?: "read-only";
  /** Ignore inherited user config while retaining CODEX_HOME authentication.
   * Cold referees use this so user MCP/tool settings cannot widen the call. */
  ignoreUserConfig?: boolean;
  /** Receives exact cumulative usage from this Codex session, including native subagents. */
  onUsage?: (usage: ModelTokenUsage) => void;
}

const CODEX_REASONING_EFFORTS = new Set<CodexRunInput["reasoningEffort"]>([
  "minimal",
  "low",
  "medium",
  "high",
  "xhigh",
]);

/**
 * Resolve a task-scoped operator override without changing the checked-in model plan.
 * This is useful when one coordinated run must pin every Codex role to the same effort;
 * callers that do not set the environment variable retain their normal per-role plan.
 */
export function resolveCodexReasoningEffort(
  requested: CodexRunInput["reasoningEffort"],
): NonNullable<CodexRunInput["reasoningEffort"]> {
  const override = process.env.CAUSALSMITH_CODEX_EFFORT_OVERRIDE?.trim();
  if (!override) return requested ?? "high";
  if (!CODEX_REASONING_EFFORTS.has(override as CodexRunInput["reasoningEffort"])) {
    throw new Error(
      `invalid CAUSALSMITH_CODEX_EFFORT_OVERRIDE=${JSON.stringify(override)}; ` +
        "expected minimal, low, medium, high, or xhigh",
    );
  }
  return override as NonNullable<CodexRunInput["reasoningEffort"]>;
}

export type CodexSandboxMode = LocalConfig["codexSandbox"];

/**
 * Decide which Codex sandbox can actually execute local tools on this host.
 *
 * `workspace-write` is the portable default. On Linux it requires a working
 * user/network namespace (directly or through bubblewrap). Some managed cluster
 * containers deny both: Codex then starts normally, but every read, shell
 * command, and `apply_patch` fails with `bwrap: loopback: Failed RTM_NEWADDR`.
 * Because detecting that failure does NOT prove the host is otherwise confined,
 * this function never broadens permissions automatically.
 *
 * An operator who has verified an outer sandbox may explicitly opt into Codex's
 * non-bypass `danger-full-access` mode in `tools/config/local.json` or with
 * `CAUSALSMITH_CODEX_SANDBOX`. The environment overrides the file. Invalid
 * values fail closed.
 */
export function resolveCodexSandboxMode(args: {
  env?: NodeJS.ProcessEnv;
  configured?: string;
} = {}): CodexSandboxMode {
  const env = args.env ?? process.env;
  const configured = (env.CAUSALSMITH_CODEX_SANDBOX ?? args.configured)?.trim();
  if (configured) {
    if (configured === "workspace-write" || configured === "danger-full-access") {
      return configured;
    }
    throw new Error(
      `CAUSALSMITH_CODEX_SANDBOX must be workspace-write or danger-full-access; got ${configured}`,
    );
  }
  return "workspace-write";
}

/** Canonical, explicitly configured mode for every real Codex dispatch. */
export function codexSandboxMode(): CodexSandboxMode {
  return resolveCodexSandboxMode({ configured: localConfig().codexSandbox });
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
 * Prepare the SEPARATE codex home used in api mode, and log it in with the key.
 *
 * Why a separate home at all: codex allows exactly one login method per
 * CODEX_HOME. Forcing api auth on a home that holds ChatGPT credentials makes
 * codex DELETE them ("API key login is required, but ChatGPT is currently being
 * used. Logging out."). Pointing api-mode runs at their own home is what keeps
 * `~/.codex` — and the operator's subscription — intact.
 *
 * The operator's global `config.toml` is COPIED in on first creation (not
 * symlinked: codex rewrites its own config, and a symlink would let a pipeline
 * run edit the real one), so model/tool settings carry over. Re-login happens
 * only when the home has no `auth.json` or the configured key changed, tracked
 * by a fingerprint sidecar so the key itself is never re-read from codex's
 * storage format.
 */
const codexApiHomeReady = new Map<string, Promise<void>>();

export async function ensureCodexApiHome(home: string, apiKey: string): Promise<void> {
  const fingerprint = createHash("sha256").update(apiKey).digest("hex");
  const memoKey = `${home}::${fingerprint}`;
  const existing = codexApiHomeReady.get(memoKey);
  if (existing) return existing;
  const task = bootstrapCodexApiHome(home, apiKey, fingerprint);
  codexApiHomeReady.set(memoKey, task);
  try {
    await task;
  } catch (err) {
    // why: a failed bootstrap must not be cached as "ready" for the whole run.
    codexApiHomeReady.delete(memoKey);
    throw err;
  }
}

/** Already logged in with THIS key? (`auth.json` present and the stamp matches.) */
async function codexApiHomeBootstrapped(home: string, fingerprint: string): Promise<boolean> {
  const [stamp, hasAuth] = await Promise.all([
    readFile(codexApiHomeStamp(home), "utf8").then((s) => s.trim()).catch(() => ""),
    stat(path.join(home, "auth.json")).then(() => true).catch(() => false),
  ]);
  return hasAuth && stamp === fingerprint;
}

function codexApiHomeStamp(home: string): string {
  return path.join(home, ".causalsmith_api_key.sha256");
}

/** Strip the key out of child output before it can reach a run log. */
function redactKey(text: string, apiKey: string): string {
  return apiKey ? text.split(apiKey).join("***") : text;
}

async function bootstrapCodexApiHome(
  home: string,
  apiKey: string,
  fingerprint: string,
): Promise<void> {
  await mkdir(home, { recursive: true });
  // 0700 explicitly: `mkdir`'s mode is masked by the process umask (0002 on this
  // cluster yields 0775), and this directory holds a credential. Best-effort —
  // a filesystem that refuses chmod must not fail the run.
  await chmod(home, 0o700).catch(() => {});
  if (await codexApiHomeBootstrapped(home, fingerprint)) return;
  // Cross-process lock: the in-process memo covers one run's mapLimit fan-out,
  // but concurrent sessions share this tree (and this home). Without it two
  // `codex login` calls race on the same `auth.json` while a third worker is
  // reading it.
  await withCodexApiHomeLock(home, async () => {
    // Re-check inside the lock: the process we queued behind may have just done it.
    if (await codexApiHomeBootstrapped(home, fingerprint)) return;
    const configPath = path.join(home, "config.toml");
    const operatorConfig = path.join(os.homedir(), ".codex", "config.toml");
    if (!(await stat(configPath).then(() => true).catch(() => false))) {
      await copyFile(operatorConfig, configPath).catch(() => {
        /* no global config to inherit — codex's own defaults apply */
      });
    }
    const result = await spawnWithInactivityTimeout("codex", ["login", "--with-api-key"], {
      cwd: home,
      env: { ...process.env, CODEX_HOME: home, OPENAI_API_KEY: apiKey },
      inactivityTimeoutMs: 2 * 60 * 1000,
      maxTotalMs: 5 * 60 * 1000,
      input: apiKey,
    });
    if (result.exitCode !== 0) {
      throw new CodexRunError(
        `codex login --with-api-key failed in CODEX_HOME=${home} (exit ${result.exitCode}). ` +
          `stderr-tail=${redactKey(result.stderr.trim(), apiKey).slice(-300)}`,
        redactKey(result.stdout, apiKey),
        redactKey(result.stderr, apiKey),
      );
    }
    await writeFile(codexApiHomeStamp(home), `${fingerprint}\n`, { encoding: "utf8", mode: 0o600 });
  });
}

/** `proper-lockfile` mutex over one codex api home, mirroring `shared/build_mutex.ts`. */
async function withCodexApiHomeLock<T>(home: string, action: () => Promise<T>): Promise<T> {
  const lockTarget = path.join(home, ".causalsmith_bootstrap.lock");
  if (!(await stat(lockTarget).then(() => true).catch(() => false))) {
    await writeFile(lockTarget, "{}\n", { encoding: "utf8", mode: 0o600 });
  }
  const release = await lockfile.lock(lockTarget, {
    stale: 10 * 60_000,
    // Budget must exceed what the lock PROTECTS (a cold `codex login`, capped at
    // maxTotalMs = 5 min) or a process queued behind a legitimately slow holder
    // throws ELOCKED and fails its stage for no reason. ~60 retries ≈ 9 min.
    retries: { retries: 60, factor: 1.5, minTimeout: 200, maxTimeout: 10_000 },
    realpath: false,
    // proper-lockfile's DEFAULT onCompromised rethrows from a refresh timer, i.e.
    // as an uncaught exception that kills the whole run — not just this bootstrap.
    // On an NFS home a stalled mtime update is a transient, so warn instead.
    onCompromised: (err: Error) => {
      console.warn(`[codex-auth] bootstrap lock compromised (continuing): ${err.message}`);
    },
  });
  try {
    return await action();
  } finally {
    await release();
  }
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
  // Put a Node satisfying `engines.node` on PATH for the shell codex spawns
  // (it runs `npx`/`lake`). Delegated to scripts/node_env.sh — the single
  // resolver shared with the skills and docs — which accepts any Node at or
  // above the floor and finds nvm via $NVM_DIR rather than assuming $HOME.
  // The previous inline `~/.nvm` prelude silently no-opped wherever $NVM_DIR
  // pointed outside $HOME, leaving whatever node was on PATH.
  //
  // Kept non-fatal: `codex` is a standalone binary that need not have node at
  // all, so a machine without one should still reach `codex exec` rather than
  // abort the `&&` chain. node_env.sh prints its own diagnostic to stderr.
  const setup = `. ${shellQuote(NODE_ENV_SCRIPT)} || true`;
  const sandboxMode = input.sandboxMode ?? codexSandboxMode();
  // Billing path. In api mode the key rides in via `workerEnv()` (which also
  // points CODEX_HOME at the dedicated home) and `forced_login_method="api"`
  // makes the choice explicit, so a home that somehow held ChatGPT credentials
  // fails loudly there instead of quietly billing the subscription. That flag is
  // NEVER emitted in subscription mode: against `~/.codex` it evicts the login.
  const auth = resolveProviderAuth("openai");
  if (auth.mode === "api") {
    // No fail-open `&& auth.apiKey` guard here: skipping the bootstrap on a
    // keyless api resolution would still let `workerEnv()` redirect CODEX_HOME,
    // i.e. run codex against a home that was never logged in. `resolveProviderAuth`
    // already refuses that combination, so this asserts the invariant instead.
    if (!auth.apiKey) throw new Error("codex api auth resolved without a key");
    await ensureCodexApiHome(codexHome(), auth.apiKey);
  }
  const cmd = [
    // `codex exec` is non-interactive, so approval remains `never`; this selects
    // only the explicitly configured local-tool sandbox. Never use the blanket
    // --dangerously-bypass-approvals-and-sandbox flag.
    `codex exec --sandbox ${sandboxMode}`,
    ...(input.ignoreUserConfig === true ? ["--ignore-user-config"] : []),
    `-C ${shellQuote(input.cwd)}`,
    "--skip-git-repo-check",
    // Windows: the default `elevated` sandbox setup helper fails to spawn on
    // codex-cli 0.133.x (`windows sandbox: spawn setup refresh`, OS error 740 —
    // see openai/codex#24098, #25362). The `unelevated` sandbox is the documented
    // workaround and runs commands fine; verified `SANDBOX_OK`. Key is ignored on
    // non-Windows hosts (the cluster), so it is safe to pass unconditionally.
    //
    // We deliberately do NOT enable `sandbox_workspace_write.network_access`.
    // In workspace-write mode, stages read papers through hosted `web_search`
    // without raw sandbox egress. An explicit danger-full-access machine setting
    // delegates both filesystem and network confinement to the outer environment.
    "-c windows.sandbox=unelevated",
    ...(auth.mode === "api" ? ['-c forced_login_method="api"'] : []),
    // Default fallback tier is mechanical (gpt-5.6-terra); every hard-math / kernel caller
    // passes an explicit `input.model` (codexKernel = gpt-5.5), so this default only applies
    // to unspecified/clerical codex calls.
    `-c model=${shellQuote(input.model ?? MODELS.codexMechanical)}`,
    `-c model_reasoning_effort=${shellQuote(resolveCodexReasoningEffort(input.reasoningEffort))}`,
    // Hosted live web search (`web_search`, server-side, no sandbox egress).
    // DEFAULT-ON; opt out with `webSearch: false`. Inert unless the prompt calls
    // it. NB: the interactive `--search` flag does NOT exist on `codex exec`;
    // the equivalent is the `tools.web_search` config override.
    `-c tools.web_search=${input.webSearch === false ? "false" : "true"}`,
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
    ...(input.multiAgent === false
      ? [
          "-c features.multi_agent_v2=false",
          "-c multi_agent.non_code_mode_only=true",
        ]
      : input.multiAgent === true || process.env.CAUSALSMITH_CODEX_MULTI_AGENT === "1"
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
    // Carries OPENAI_API_KEY + the dedicated CODEX_HOME in api mode; identical
    // to process.env otherwise.
    env: workerEnv(),
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
  // Telemetry is best-effort and must never change the model call's outcome.
  try {
    const sessionFile = await findCodexSessionFile(spawnedAt, marker);
    if (sessionFile && input.onUsage) {
      const usage = await extractCodexTokenUsage(sessionFile);
      if (usage) input.onUsage(usage);
    }
  } catch (err) {
    console.warn(`[token-usage] could not read Codex usage: ${String(err)}`);
  }
  const killed =
    result.killedDueToLiveness ??
    (result.killedDueToInactivity
      ? `inactivity timeout (${Math.round((input.inactivityTimeoutMs ?? 25 * 60 * 1000) / 60000)}m without output)`
      : null);
  if (killed) {
    // Redact BEFORE slicing: a key straddling the 300-char cut must not survive
    // in a fragment. These messages are persisted to doc/research/_agent_logs/.
    throw new CodexRunError(
      `codex killed: ${killed}. stderr-tail=${redactSecrets(result.stderr.trim()).slice(-300)}`,
      redactSecrets(result.stdout),
      redactSecrets(result.stderr),
    );
  }
  if (result.exitCode !== null && result.exitCode !== 0) {
    throw new CodexRunError(
      `codex exited ${result.exitCode}. stderr-tail=${redactSecrets(result.stderr.trim()).slice(-300)}`,
      redactSecrets(result.stdout),
      redactSecrets(result.stderr),
    );
  }
  return { stdout: result.stdout, stderr: result.stderr };
}

async function codexSessionStarted(after: number, marker: string): Promise<boolean> {
  return (await findCodexSessionFile(after, marker)) !== null;
}

async function findCodexSessionFile(after: number, marker: string): Promise<string | null> {
  // Must follow the ACTIVE codex home: api mode relocates CODEX_HOME, and a
  // hardcoded `~/.codex/sessions` would then never see the marker, so the
  // startup watchdog would kill every healthy worker at the startup window.
  const root = path.join(codexHome(), "sessions");
  const candidates: string[] = [];
  await collectNewerJsonl(root, after, 3, candidates);
  for (const file of candidates) {
    if (await fileHeadContains(file, marker)) return file;
  }
  return null;
}

/** Read the final cumulative token counter from a Codex rollout JSONL. */
export async function extractCodexTokenUsage(file: string): Promise<ModelTokenUsage | null> {
  let latest: ModelTokenUsage | null = null;
  for (const line of (await readFile(file, "utf8")).split(/\r?\n/)) {
    if (!line.trim()) continue;
    try {
      const event = JSON.parse(line) as {
        type?: string;
        payload?: {
          type?: string;
          info?: { total_token_usage?: Partial<ModelTokenUsage> & { cache_write_input_tokens?: number } };
        };
      };
      const raw = event.type === "event_msg" && event.payload?.type === "token_count"
        ? event.payload.info?.total_token_usage
        : undefined;
      if (!raw) continue;
      latest = {
        input_tokens: raw.input_tokens ?? 0,
        cached_input_tokens: raw.cached_input_tokens ?? 0,
        cache_creation_input_tokens:
          raw.cache_creation_input_tokens ?? raw.cache_write_input_tokens ?? 0,
        output_tokens: raw.output_tokens ?? 0,
        reasoning_output_tokens: raw.reasoning_output_tokens ?? 0,
        total_tokens: raw.total_tokens ?? (raw.input_tokens ?? 0) + (raw.output_tokens ?? 0),
      };
    } catch {
      // Non-JSON or truncated final lines carry no usable counter.
    }
  }
  return latest;
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
