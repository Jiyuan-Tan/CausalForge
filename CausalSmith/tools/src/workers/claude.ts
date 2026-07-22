import path from "node:path";
import os from "node:os";
import fsSync from "node:fs";
import { fileURLToPath } from "node:url";
import { spawnWithInactivityTimeout } from "./spawn.js";
import { localConfig, leanProjectPathFor } from "../local_config.js";
import type { ClaudeModel } from "../models.js";

export interface ClaudeRunInput {
  prompt: string;
  /** A `claude` CLI --model value: an alias (opus/sonnet/haiku) or a pinned id.
   *  See src/models.ts for the env-overridable role defaults. */
  model: ClaudeModel;
  cwd: string;
  allowedTools?: string[];
  /** Grant the `Task` sub-agent tool (default ON — codex-parity fan-out). Set
   *  `false` for narrow judges where a spawned subagent is never appropriate. */
  allowSubagents?: boolean;
  /** Grant the hosted web tools `WebFetch`/`WebSearch` (default ON — parity with
   *  codex `--search`). Inert unless the prompt calls them; opt out with
   *  `webSearch: false` for stages that never need the web. */
  webSearch?: boolean;
  mcpConfigPath?: string;
  jsonSchema?: object;
  systemPromptFile?: string;
  inactivityTimeoutMs?: number;
  /**
   * Configure the `lean-lsp` MCP server for this claude call. DEFAULT-ON (user
   * policy 2026-06-04): every claude call gets the lean-lsp server + the
   * `mcp__lean-lsp__*` read/query tools merged into its allow-list, unless it
   * opts out with `leanLsp: false`. Safe even for the deliberately tool-narrow
   * draft stages: `--strict-mcp-config` advertises ONLY lean-lsp, so third-party
   * servers (Google Drive, etc.) stay invisible regardless. An explicit
   * `mcpConfigPath` still wins (the caller fully controls the MCP set).
   */
  leanLsp?: boolean;
}

/**
 * Read/query lean-lsp tools merged into every claude call's allow-list when
 * lean-lsp is enabled (default). Excludes the heavy/slow ones (`lean_build`,
 * `lean_profile_proof`, `lean_run_code`) — stages that need those request them
 * explicitly. The preamble's allow-list is built from the final tool set, so
 * these must be present for claude to be permitted to call them.
 */
const LEAN_LSP_TOOLS = [
  "mcp__lean-lsp__lean_diagnostic_messages",
  "mcp__lean-lsp__lean_goal",
  "mcp__lean-lsp__lean_term_goal",
  "mcp__lean-lsp__lean_hover_info",
  "mcp__lean-lsp__lean_local_search",
  "mcp__lean-lsp__lean_leansearch",
  "mcp__lean-lsp__lean_loogle",
  "mcp__lean-lsp__lean_state_search",
  "mcp__lean-lsp__lean_multi_attempt",
  "mcp__lean-lsp__lean_file_outline",
  "mcp__lean-lsp__lean_completions",
  "mcp__lean-lsp__lean_declaration_file",
];

// Hard non-interactivity contract for every Claude pipeline call. Opus's default
// disposition is to ask clarifying questions and offer alternatives when a
// prompt looks unusual (e.g. a 40k-char single-shot prompt asking for a JSON
// blob); codex does not have this disposition. Without this contract Stage -1.2
// drafts come back as "Which do you want?" instead of the JSON object the
// orchestrator parses, and the run dies as `invalid-draft` on every angle.
// Non-interactivity rules common to every Claude pipeline call.
const NON_INTERACTIVE_OUTPUT_RULES = [
  "You are a non-interactive batch worker invoked by an automated pipeline.",
  "The user is NOT present and cannot answer. Your stdout is parsed verbatim.",
  "",
  "OUTPUT RULES (hard, non-negotiable):",
  "- Emit ONLY the artifact the prompt asks for (typically a single JSON object on stdout).",
  "- Never ask clarifying questions, never offer alternatives, never say 'Which do you want?', 'Should I…?', 'Let me know…', or any phrase that expects a reply.",
  "- Do not include preamble, commentary, apologies, or trailing prose around the artifact.",
  "- If the prompt is ambiguous, make a reasonable choice and proceed; document the choice INSIDE the artifact (e.g. in a `decisions` field) rather than asking.",
  "- The orchestrator extracts the FIRST top-level JSON object from stdout via balanced-brace scan. Anything outside that object is discarded; anything that breaks JSON parse fails the stage.",
].join("\n");

function buildClaudePreamble(allowedTools: string[]): string {
  const hasTools = allowedTools.length > 0;
  const toolRules = hasTools
    ? [
        "",
        "TOOL RULES (hard, non-negotiable):",
        `- The ONLY tools available to you are: ${allowedTools.join(", ")}. No others. No Bash, no Glob, no Grep, no MCP, no Google Drive, no GitHub — unless that exact name is in the list above.`,
        "- If the prompt instructs you to write a file (e.g. 'edit the proposal at <path>'), use the Write or Edit tool. Do NOT emit the file content as a JSON field; the orchestrator reads the file from disk.",
        "- The stdout JSON receipt is a SEPARATE artifact from the file you write. Emit it after the file write completes, exactly as the prompt's REQUIRED OUTPUT FORMAT specifies.",
        "- Do NOT narrate tool use in your stdout text (e.g. `Tool: Read {...}`, `[Tool uses: ...]`, `Let me read…`, ` ```bash …``` `). Use the structured tool-call channel; stdout is reserved for the final JSON receipt.",
        "- Do NOT invent tools or reference tools that are not in the allow-list above.",
      ]
    : [
        "",
        "TOOL RULES (hard, non-negotiable):",
        "- You have ZERO tools available for this call. No Read, no Glob, no Grep, no Bash, no Write, no Edit, no MCP servers, no Google Drive, no GitHub.",
        "- Do NOT emit narration of tool use such as `Tool: Read {...}`, `[Tool uses: Read, Read]`, `Let me read the file`, `I'll grep for…`, ` ```bash …``` `, or any similar text. That narration is treated as raw output and breaks JSON parse.",
        "- The prompt is fully self-contained. Every literature reference, skeleton, prior review, and gap inventory you might want has been INLINED below.",
        "- If the prompt mentions a file path (e.g. a `proposal_path`), treat it as the OUTPUT path the orchestrator will populate from your JSON. Do NOT attempt to read it.",
        "- If you find yourself wanting to read a file or run a command, instead synthesize the content from what is already in the prompt and emit it inside the JSON. The prompt is the world.",
      ];
  return [NON_INTERACTIVE_OUTPUT_RULES, ...toolRules].join("\n");
}

// Empty MCP config: passed as the load-bearing target of --strict-mcp-config so
// that the user's MCP servers (Google Drive, etc.) are NOT auto-loaded into
// pipeline workers via --setting-sources user. We still need user settings for
// OAuth, but we must not advertise third-party tools to the proposer; Opus has
// been observed to offer to "draft in Drive" when those servers leak in.
const EMPTY_MCP_CONFIG_PATH = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "..",
  "config",
  "empty_mcp.json",
);

const CONFIG_DIR = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "..",
  "config",
);

/**
 * Write a `--mcp-config` JSON exposing the `lean-lsp` server so a worker stage
 * (F1 feasibility gate; F2/F3 if they opt in) actually gets the
 * `mcp__lean-lsp__*` tools instead of advertising tools no server provides.
 * Binary resolves from `CAUSALSMITH_LEAN_LSP_MCP` else PATH (`lean-lsp-mcp`);
 * `leanProjectPath` is the Causalean lake-project root (the run's repoRoot).
 * Returns the config path to feed `runClaude({ mcpConfigPath })`.
 */
export function writeLeanLspMcpConfig(repoRoot: string): string {
  const cfg = localConfig();
  const config = {
    mcpServers: {
      "lean-lsp": {
        command: cfg.leanLspMcpBinary,
        args: ["--lean-project-path", leanProjectPathFor(repoRoot)],
        // lean-lsp cold-starts slowly (~50s on first load); give it headroom.
        env: { MCP_TIMEOUT: String(cfg.mcpTimeoutMs) },
      },
    },
  };
  const out = path.join(CONFIG_DIR, "lean_mcp.generated.json");
  fsSync.writeFileSync(out, JSON.stringify(config, null, 2));
  return out;
}

/**
 * Write a `--mcp-config` that ATTACHES to a shared streamable-HTTP `lean-lsp-mcp`
 * (booted once per run via `startSharedLeanLsp`, URL in
 * `CAUSALSMITH_SHARED_LEAN_LSP_URL`) instead of spawning a per-call stdio server +
 * its own `lake serve`. Mirrors codex.ts's shared-server branch so claude stages
 * (scaffolder, reviewer) share the ONE warm `lake serve` rather than each paying
 * the cold-start. Registered under the name `lean-lsp` so the `mcp__lean-lsp__*`
 * allow-list still matches.
 */
export function writeLeanLspSharedConfig(sharedUrl: string): string {
  const config = { mcpServers: { "lean-lsp": { type: "http", url: sharedUrl } } };
  // Unique per shared-server so two concurrent `--study` runs in the SAME
  // checkout do not clobber each other's URL: each run owns one shared server on
  // its own port, and its claude stages read THAT port's config. Keyed on the
  // URL's port; written to the OS temp dir (ephemeral, read once at claude
  // startup) rather than the repo config dir, so no per-port files accumulate in
  // the tree. A fixed file would let run B's URL overwrite run A's before A's
  // claude reads it, attaching A to B's server (which B later tears down).
  let port = "0";
  try {
    port = new URL(sharedUrl).port || "0";
  } catch {
    /* malformed URL → fall back to a shared name; single-run case is unaffected */
  }
  const out = path.join(os.tmpdir(), `causalsmith_lean_mcp.shared.${port}.json`);
  fsSync.writeFileSync(out, JSON.stringify(config, null, 2));
  return out;
}

export interface ClaudeRunDiagnostic {
  rawStdout: string;
  rawStderr: string;
  parsedText: string;
}

export class ClaudeRunError extends Error {
  constructor(
    message: string,
    public readonly stdout: string,
    public readonly stderr: string,
  ) {
    super(message);
    this.name = "ClaudeRunError";
  }
}

export async function runClaude(input: ClaudeRunInput): Promise<string> {
  // NOTE: --bare would suppress hooks/LSP/CLAUDE.md and isolate the call, but it
  // also restricts auth to ANTHROPIC_API_KEY / apiKeyHelper only (keychain OAuth
  // is never read). Without an API key in the environment this hangs at login,
  // returning "Not logged in" instead of JSON and crashing the intervention
  // judge. We drop --bare and rely on --setting-sources user + --tools to keep
  // the call narrow; parseStreamJson only consumes assistant/result events so
  // non-bare init lines are ignored.
  // lean-lsp is default-ON: merge the lean read/query tools into the allow-list
  // (so the preamble permits them) unless the caller opts out with leanLsp:false.
  const useLean = input.leanLsp !== false;
  const baseTools = input.allowedTools ?? ["Read", "Glob", "Grep"];
  // Sub-agent fan-out parity with codex (see shared/codex.ts: features.multi_agent_v2).
  // Grant the `Task` tool so an opus worker can DECOMPOSE large work across subagents.
  // Like codex's spawn_agent, it is inert unless the worker's PROMPT asks for delegation
  // (a worker with no fan-out instruction simply never calls it). Opt out with
  // `allowSubagents: false` for narrow judges where a spawned agent is never wanted.
  const withTask = input.allowSubagents === false ? baseTools : [...baseTools, "Task"];
  // Hosted web tools default-ON (parity with codex `--search`); inert unless the
  // worker's PROMPT calls them. Opt out with `webSearch: false`.
  const withWeb = input.webSearch === false ? withTask : [...withTask, "WebFetch", "WebSearch"];
  const allowedTools = useLean
    ? Array.from(new Set([...withWeb, ...LEAN_LSP_TOOLS]))
    : Array.from(new Set(withWeb));
  // NB: the prompt is fed via STDIN (see `input:` below), NOT as the `-p`
  // positional. A large F-stage prompt (~70k chars) exceeds the Windows
  // CreateProcess command-line limit (~32k) and the spawn fails silently;
  // stdin has no such limit and works identically on Linux.
  const args = [
    "-p",
    "--model",
    input.model,
    "--output-format",
    "stream-json",
    "--verbose",
    "--setting-sources",
    "user",
    "--disable-slash-commands",
    "--tools",
    allowedTools.join(","),
    "--append-system-prompt",
    buildClaudePreamble(allowedTools),
  ];

  // MCP isolation: an explicit `mcpConfigPath` always wins. Otherwise lean-lsp
  // is default-ON (write a lean-lsp-only config rooted at the run's cwd); opt
  // out with leanLsp:false to lock to the empty config. Either way
  // --strict-mcp-config means ONLY the advertised server is loaded, so
  // user-level MCP servers (Google Drive, etc.) never leak in via
  // --setting-sources user.
  // A launcher (e.g. `--study`, the F3 loop) may have booted ONE shared warm
  // lean-lsp server and exported its URL; attach to it instead of spawning a
  // per-call stdio server + cold `lake serve`. An explicit mcpConfigPath still
  // wins; leanLsp:false still locks to the empty config.
  const sharedLeanUrl = process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL?.trim();
  const mcpConfigPath =
    input.mcpConfigPath ??
    (useLean
      ? sharedLeanUrl
        ? writeLeanLspSharedConfig(sharedLeanUrl)
        : writeLeanLspMcpConfig(input.cwd)
      : EMPTY_MCP_CONFIG_PATH);
  args.push("--strict-mcp-config", "--mcp-config", mcpConfigPath);
  if (input.jsonSchema) args.push("--json-schema", JSON.stringify(input.jsonSchema));
  if (input.systemPromptFile) args.push("--system-prompt-file", input.systemPromptFile);

  const result = await spawnWithInactivityTimeout("claude", args, {
    cwd: input.cwd,
    env: process.env,
    inactivityTimeoutMs: input.inactivityTimeoutMs ?? 20 * 60 * 1000,
    input: input.prompt,
  });
  const killed =
    result.killedDueToLiveness ??
    (result.killedDueToTotalTimeout
      ? "total timeout"
      : result.killedDueToInactivity
        ? `inactivity timeout (${Math.round((input.inactivityTimeoutMs ?? 20 * 60 * 1000) / 60000)}m without output)`
        : null);
  if (killed || result.exitCode === null || result.exitCode !== 0) {
    // why: a crashed/killed Claude stream may contain partial JSON that must not count as success.
    lastDiagnostic = {
      rawStdout: result.stdout,
      rawStderr: result.stderr,
      parsedText: "",
    };
    const reason = killed ?? `exit ${result.exitCode}`;
    throw new ClaudeRunError(
      `claude failed: ${reason}. stdout-tail=${result.stdout.trim().slice(-300)} stderr-tail=${result.stderr.trim().slice(-300)}`,
      result.stdout,
      result.stderr,
    );
  }
  const parsed = parseStreamJson(result.stdout);
  // Stash diagnostics on the function so callers can inspect after the fact
  // when the parsed text is unexpectedly empty (Bug B follow-up — see
  // PIPELINE_NOTES). This is opt-in: only `runIntervention` reads it.
  lastDiagnostic = {
    rawStdout: result.stdout,
    rawStderr: result.stderr,
    parsedText: parsed,
  };
  return parsed;
}

let lastDiagnostic: ClaudeRunDiagnostic | null = null;
export function getLastClaudeDiagnostic(): ClaudeRunDiagnostic | null {
  return lastDiagnostic;
}

export function parseStreamJson(stdout: string | undefined | null): string {
  const texts: string[] = [];
  // Defensive: a failed/timed-out `claude` spawn can yield undefined stdout.
  // Returning "" lets callers (runIntervention) fall into their deterministic
  // synthesis fallback and checkpoint cleanly instead of crashing on `.split`.
  if (typeof stdout !== "string" || stdout.length === 0) return "";
  for (const line of stdout.split(/\r?\n/)) {
    if (!line.trim()) continue;
    try {
      const parsed = JSON.parse(line) as Record<string, unknown>;
      if (parsed.type === "assistant" && typeof parsed.message === "object") {
        const message = parsed.message as {
          content?: Array<{ type?: string; text?: string; name?: string; input?: unknown }>;
        };
        for (const block of message.content ?? []) {
          if (block.type === "text" && block.text) texts.push(block.text);
          // When --json-schema is passed, Claude emits the payload via the
          // StructuredOutput tool rather than as a text block. The result-event
          // `result` field is empty in that mode, so without this branch
          // downstream `parseIntervention` / `parseReview` see "" and treat a
          // perfectly valid structured emit as parse_failure.
          if (
            block.type === "tool_use" &&
            block.name === "StructuredOutput" &&
            block.input &&
            typeof block.input === "object"
          ) {
            texts.push(JSON.stringify(block.input));
          }
        }
      }
      if (parsed.type === "result") {
        // The terminal result event's `result` string REPEATS the final
        // assistant turn's text. Pushing it unconditionally doubles every
        // single-turn reply (causalsmith P1 froze duplicated statement bodies
        // this way). Keep it only when it adds text we haven't collected —
        // e.g. non-verbose runs where assistant events are absent.
        if (typeof parsed.result === "string" && parsed.result.length > 0) {
          const r = parsed.result.trim();
          if (!texts.join("\n").includes(r)) texts.push(parsed.result);
        }
        // Belt-and-suspenders mirror of the tool_use branch above: some CLI
        // versions only surface the structured payload on the terminal result
        // event, not on the assistant message.
        if (parsed.structured_output && typeof parsed.structured_output === "object") {
          texts.push(JSON.stringify(parsed.structured_output));
        }
      }
    } catch {
      // why: stream-json stdout can include banners/warnings; only assistant/result events are payload.
      console.debug(`[claude] dropping non-json stream line: ${line.slice(0, 200)}`);
    }
  }
  return texts.join("\n").trim();
}
