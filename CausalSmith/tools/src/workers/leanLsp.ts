import { readFile } from "node:fs/promises";
import path from "node:path";
import { McpClient, type McpClientOpts } from "./mcp.js";
import { spawnWithInactivityTimeout } from "./spawn.js";
import { localConfig, leanProjectPathFor } from "../local_config.js";
import { withLakeBuildLock } from "../shared/build_mutex.js";

// ---------------------------------------------------------------------------
// Result types — mirror the Pydantic models the MCP server returns.
// ---------------------------------------------------------------------------

export interface LeanDiagnostic {
  file: string;
  line?: number;
  endLine?: number;
  severity: "error" | "warning" | "information";
  message: string;
}

export interface GoalState {
  line_context: string;
  goals?: string[];
  goals_before?: string[];
  goals_after?: string[];
}

export interface TermGoalState {
  line_context: string;
  expected_type: string | null;
}

export interface HoverInfo {
  symbol: string;
  info: string;
  diagnostics: LeanDiagnostic[];
}

export interface MultiAttemptOutcome {
  snippet: string;
  goals: string[] | null;
  diagnostics: LeanDiagnostic[];
  /** Raw MCP body per snippet; preserved so callers can introspect. */
  raw?: unknown;
}

export interface MultiAttemptResult {
  outcomes: MultiAttemptOutcome[];
  /** Original parsed payload (whatever the server returned). */
  raw: unknown;
}

export interface LocalSearchHit {
  name: string;
  kind: string;
  file: string;
}

export interface StateSearchHit {
  name: string;
}

export interface PremiseHit {
  name: string;
  score?: number;
}

export interface EnrichedSorry {
  file: string;
  line: number;
  label?: string;
  goal: string;
  suggestions: string[];
}

export interface LeanLspClient {
  diagnostics(
    file: string,
    opts?: { startLine?: number; endLine?: number; declarationName?: string },
  ): Promise<LeanDiagnostic[]>;
  goal(file: string, line: number, column?: number): Promise<GoalState>;
  termGoal(file: string, line: number, column?: number): Promise<TermGoalState>;
  hoverInfo(file: string, line: number, column: number): Promise<HoverInfo>;
  multiAttempt(
    file: string,
    line: number,
    snippets: string[],
    column?: number,
  ): Promise<MultiAttemptResult>;
  localSearch(query: string, limit?: number): Promise<LocalSearchHit[]>;
  stateSearch(
    file: string,
    line: number,
    column: number,
    numResults?: number,
  ): Promise<StateSearchHit[]>;
  hammerPremise(
    file: string,
    line: number,
    column: number,
    numResults?: number,
  ): Promise<PremiseHit[]>;
  findSorries(files: string[]): Promise<EnrichedSorry[]>;
  /**
   * Hard COMPILE ERRORS (not sorries) in the given files, as `EnrichedSorry`-
   * shaped work records (`goal` carries the error message, prefixed `COMPILE
   * ERROR …`). Lets Stage 3 re-pick-up a file that a crashed/failed Codex edit
   * left non-compiling — invisible to the sorry-only `findSorries`. Optional so
   * lightweight test fakes need not implement it.
   */
  findErrors?(files: string[]): Promise<EnrichedSorry[]>;
  build(opts?: { clean?: boolean; outputLines?: number }): Promise<{
    success: boolean;
    log: string;
    errors: string[];
  }>;
  /** Targeted `lake build <modules>` — builds only the given module(s) + their import closure (oleans on disk), skipping the rest of the package. Used to pre-warm a specific scaffold for review. */
  buildTargets(modules: string[]): Promise<{ success: boolean; log: string; errors: string[] }>;
  close(): Promise<void>;
}

// ---------------------------------------------------------------------------
// MCP-backed implementation. Spawns `lean-lsp-mcp` (stdio transport) and
// multiplexes JSON-RPC calls over a single long-lived child.
// ---------------------------------------------------------------------------

export interface McpLeanLspClientOpts {
  /** Lean project root (passed via `--lean-project-path`). */
  repoRoot: string;
  /** Override the MCP server binary; defaults to `lean-lsp-mcp`. */
  binary?: string;
  /** Extra args appended after the path flag. */
  extraArgs?: string[];
  /**
   * Full argv override. When set, `binary`/`extraArgs`/`--lean-project-path`
   * composition is skipped. Used by the test harness to spawn a mock server
   * via `node mock.mjs` without injecting the Lean-specific flag.
   */
  argv?: string[];
  /** Per-tool timeouts (ms). Falls back to sensible defaults. */
  timeouts?: Partial<Record<
    | "diagnostics"
    | "goal"
    | "termGoal"
    | "hoverInfo"
    | "multiAttempt"
    | "localSearch"
    | "stateSearch"
    | "hammerPremise"
    | "build",
    number
  >>;
  /** Optional sink for MCP stderr (server logs INFO there). */
  onStderr?: (chunk: string) => void;
}

const DEFAULT_TIMEOUTS = {
  diagnostics: 4 * 60 * 1000,
  goal: 2 * 60 * 1000,
  termGoal: 2 * 60 * 1000,
  hoverInfo: 60 * 1000,
  multiAttempt: 5 * 60 * 1000,
  localSearch: 30 * 1000,
  stateSearch: 60 * 1000,
  hammerPremise: 60 * 1000,
  build: 25 * 60 * 1000,
};

/**
 * Run `lake build` for the package. With `targets`, builds only those modules
 * (+ their import closure) instead of the whole package — used to pre-warm a
 * specific scaffold for review without compiling the entire catalogue. The MCP
 * `lean_build` tool has no target parameter, so a targeted build must spawn
 * `lake` directly; this is the shared implementation for both client backends.
 */
async function runLakeBuild(
  repoRoot: string,
  targets?: string[],
): Promise<{ success: boolean; log: string; errors: string[] }> {
  return withLakeBuildLock(repoRoot, async () => {
    // why: targets can be LLM/file derived, so pass argv directly instead of interpolating a shell command.
    const result = await spawnWithInactivityTimeout("lake", ["build", ...(targets ?? [])], {
      cwd: repoRoot,
      env: process.env,
      inactivityTimeoutMs: 20 * 60 * 1000,
    });
    const log = [result.stdout, result.stderr].filter(Boolean).join("\n");
    const failureReasons = [
      result.exitCode === null
        ? "exit code null"
        : result.exitCode !== 0
          ? `exit code ${result.exitCode}`
          : null,
      result.killedDueToInactivity ? "inactivity timeout" : null,
      result.killedDueToLiveness ? `liveness kill: ${result.killedDueToLiveness}` : null,
      result.killedDueToTotalTimeout ? "total timeout" : null,
    ].filter((x): x is string => x !== null);
    let errors = log
      .split(/\r?\n/)
      .filter((line) => /error/i.test(line))
      .slice(-40);
    if (failureReasons.length > 0 && errors.length === 0) {
      // why: process-level build failure is still a failure even when Lake emitted no "error" line.
      errors = [`lake build failed: ${failureReasons.join("; ")}`];
    }
    return {
      success: failureReasons.length === 0 && errors.length === 0,
      log: log.split(/\r?\n/).slice(-40).join("\n"),
      errors,
    };
  });
}

export class McpLeanLspClient implements LeanLspClient {
  private mcp: McpClient;
  private readonly timeouts: typeof DEFAULT_TIMEOUTS;

  constructor(private readonly opts: McpLeanLspClientOpts) {
    const cmd = opts.argv ? opts.argv[0] : opts.binary ?? localConfig().leanLspMcpBinary;
    const args = opts.argv
      ? opts.argv.slice(1)
      // why: match the generated MCP config's Lake project root resolution.
      : ["--lean-project-path", leanProjectPathFor(opts.repoRoot), ...(opts.extraArgs ?? [])];
    const mcpOpts: McpClientOpts = {
      cmd,
      args,
      cwd: opts.repoRoot,
      env: process.env,
      onStderr: opts.onStderr,
      defaultCallTimeoutMs: 5 * 60 * 1000,
    };
    this.mcp = new McpClient(mcpOpts);
    this.timeouts = { ...DEFAULT_TIMEOUTS, ...(opts.timeouts ?? {}) };
  }

  private rel(file: string): string {
    const r = path.isAbsolute(file) ? path.relative(this.opts.repoRoot, file) : file;
    return r.split(path.sep).join("/");
  }

  async diagnostics(
    file: string,
    opts: { startLine?: number; endLine?: number; declarationName?: string } = {},
  ): Promise<LeanDiagnostic[]> {
    const rel = this.rel(file);
    const args: Record<string, unknown> = { file_path: rel };
    if (opts.startLine !== undefined) args.start_line = opts.startLine;
    if (opts.endLine !== undefined) args.end_line = opts.endLine;
    if (opts.declarationName !== undefined) args.declaration_name = opts.declarationName;
    const r = await this.mcp.callTool("lean_diagnostic_messages", args, {
      timeoutMs: this.timeouts.diagnostics,
    });
    return parseDiagnostics(r.value, rel);
  }

  async goal(file: string, line: number, column?: number): Promise<GoalState> {
    const rel = this.rel(file);
    const args: Record<string, unknown> = { file_path: rel, line };
    if (column !== undefined) args.column = column;
    const r = await this.mcp.callTool("lean_goal", args, {
      timeoutMs: this.timeouts.goal,
    });
    return parseGoal(r.value);
  }

  async termGoal(file: string, line: number, column?: number): Promise<TermGoalState> {
    const rel = this.rel(file);
    const args: Record<string, unknown> = { file_path: rel, line };
    if (column !== undefined) args.column = column;
    const r = await this.mcp.callTool("lean_term_goal", args, {
      timeoutMs: this.timeouts.termGoal,
    });
    return parseTermGoal(r.value);
  }

  async hoverInfo(file: string, line: number, column: number): Promise<HoverInfo> {
    const rel = this.rel(file);
    const r = await this.mcp.callTool(
      "lean_hover_info",
      { file_path: rel, line, column },
      { timeoutMs: this.timeouts.hoverInfo },
    );
    return parseHover(r.value, rel);
  }

  async multiAttempt(
    file: string,
    line: number,
    snippets: string[],
    column?: number,
  ): Promise<MultiAttemptResult> {
    const rel = this.rel(file);
    const args: Record<string, unknown> = { file_path: rel, line, snippets };
    if (column !== undefined) args.column = column;
    const r = await this.mcp.callTool("lean_multi_attempt", args, {
      timeoutMs: this.timeouts.multiAttempt,
    });
    return parseMultiAttempt(r.value, rel);
  }

  async localSearch(query: string, limit = 10): Promise<LocalSearchHit[]> {
    const r = await this.mcp.callTool(
      "lean_local_search",
      { query, limit, project_root: this.opts.repoRoot },
      { timeoutMs: this.timeouts.localSearch },
    );
    return parseLocalSearch(r.value);
  }

  async stateSearch(
    file: string,
    line: number,
    column: number,
    numResults = 5,
  ): Promise<StateSearchHit[]> {
    const rel = this.rel(file);
    const r = await this.mcp.callTool(
      "lean_state_search",
      { file_path: rel, line, column, num_results: numResults },
      { timeoutMs: this.timeouts.stateSearch },
    );
    return parseStateSearch(r.value);
  }

  async hammerPremise(
    file: string,
    line: number,
    column: number,
    numResults = 16,
  ): Promise<PremiseHit[]> {
    const rel = this.rel(file);
    const r = await this.mcp.callTool(
      "lean_hammer_premise",
      { file_path: rel, line, column, num_results: numResults },
      { timeoutMs: this.timeouts.hammerPremise },
    );
    return parsePremise(r.value);
  }

  async findSorries(files: string[]): Promise<EnrichedSorry[]> {
    const out: EnrichedSorry[] = [];
    // Per-PASS fail-fast: this loop is fully serial (one diagnostics call per
    // file + one goal call per sorry). Against a wedged LSP every call burns
    // its full timeout — a 20-sorry artifact could spend over an hour in
    // nothing but timeouts. After the first timeout, degrade the REST OF THIS
    // PASS to the comment-stripped text scan (records still surface as work);
    // the next pass retries the LSP fresh.
    let lspDown = false;
    for (const file of files) {
      const rel = this.rel(file);
      const abs = path.isAbsolute(file) ? file : path.join(this.opts.repoRoot, file);
      const text = await readFile(abs, "utf8");
      const lines = text.split(/\r?\n/);
      // Gate detection on the LSP diagnostic stream: if the file has zero
      // "declaration uses 'sorry'" warnings, we report no sorries even if
      // the source text happens to contain the word.
      let hasSorryWarning = false;
      if (lspDown) {
        hasSorryWarning = true;
      } else {
        try {
          const diags = await this.diagnostics(rel);
          hasSorryWarning = diags.some(isSorryDiagnostic);
        } catch (err) {
          // Fall back to the comment-stripped regex scan alone (better than
          // nothing — comments are still filtered) and fail-fast the pass.
          console.warn(
            `[leanLsp] findSorries: diagnostics failed for ${rel} — text-scan fallback for the rest of this pass (${err instanceof Error ? err.message : String(err)})`,
          );
          lspDown = true;
          hasSorryWarning = true;
        }
      }
      if (!hasSorryWarning) continue;
      const sorryLines = findSorryLines(lines);
      for (const idx of sorryLines) {
        const label = findNearestDeclaration(lines, idx);
        let goalText = "";
        if (lspDown) {
          goalText = "(LSP unavailable this pass — text-scan record, goal unknown)";
        } else {
          try {
            const g = await this.goal(rel, idx + 1);
            goalText = formatGoal(g);
          } catch (err) {
            goalText = `(failed to get goal: ${err instanceof Error ? err.message : String(err)})`;
            if (/timed out/i.test(String(err))) lspDown = true;
          }
        }
        let suggestions: string[] = [];
        if (label && !lspDown) {
          try {
            const hits = await this.localSearch(label, 3);
            suggestions = hits.map((h) => `${h.name} [${h.kind}] @ ${h.file}`);
          } catch {
            suggestions = [];
          }
        }
        out.push({ file: rel, line: idx + 1, label, goal: goalText, suggestions });
      }
    }
    return out;
  }

  async findErrors(files: string[]): Promise<EnrichedSorry[]> {
    const out: EnrichedSorry[] = [];
    for (const file of files) {
      const rel = this.rel(file);
      const abs = path.isAbsolute(file) ? file : path.join(this.opts.repoRoot, file);
      let lines: string[] = [];
      try {
        lines = (await readFile(abs, "utf8")).split(/\r?\n/);
      } catch {
        continue;
      }
      let diags: LeanDiagnostic[];
      try {
        diags = await this.diagnostics(rel);
      } catch (err) {
        // LOUD skip: a silent `continue` here meant a dead/timing-out LSP made
        // compile errors permanently invisible while text-clean files counted
        // as done — a run could complete "clean" on a non-compiling artifact.
        console.warn(
          `[leanLsp] findErrors: diagnostics unavailable for ${rel} ` +
            `(${err instanceof Error ? err.message : String(err)}) — compile errors in this file are NOT checked this round`,
        );
        continue;
      }
      for (const d of diags) {
        // Hard, build-breaking errors only: skip the sorry warning and the
        // non-fatal style linters (doc-string/long-line/whitespace), which do
        // not fail `lake build`.
        if (d.severity !== "error") continue;
        if (isSorryDiagnostic(d)) continue;
        if (isStyleLintDiagnostic(d)) continue;
        const line = d.line ?? 1;
        const label = findNearestDeclaration(lines, Math.min(line - 1, lines.length - 1));
        const firstLine = d.message.split(/\r?\n/)[0];
        out.push({
          file: rel,
          line,
          label,
          goal: `COMPILE ERROR (not a sorry — a crashed/failed proof edit left this): ${firstLine}`,
          suggestions: [],
        });
      }
    }
    return out;
  }

  async build(
    opts: { clean?: boolean; outputLines?: number } = {},
  ): Promise<{ success: boolean; log: string; errors: string[] }> {
    const r = await this.mcp.callTool(
      "lean_build",
      {
        clean: opts.clean ?? false,
        output_lines: opts.outputLines ?? 40,
      },
      { timeoutMs: this.timeouts.build },
    );
    return parseBuild(r.value);
  }

  async buildTargets(
    modules: string[],
  ): Promise<{ success: boolean; log: string; errors: string[] }> {
    return runLakeBuild(this.opts.repoRoot, modules);
  }

  async close(): Promise<void> {
    await this.mcp.shutdown();
  }
}

// ---------------------------------------------------------------------------
// CLI fallback — kept for environments without the MCP server. Implements the
// LeanLspClient interface but only covers `diagnostics`, `findSorries`,
// `localSearch`, and `build`; the richer methods throw `notImplemented`.
// ---------------------------------------------------------------------------

export class CliLeanLspClient implements LeanLspClient {
  constructor(private readonly repoRoot: string) {}

  private rel(file: string): string {
    const r = path.isAbsolute(file) ? path.relative(this.repoRoot, file) : file;
    return r.split(path.sep).join("/");
  }

  async diagnostics(file: string): Promise<LeanDiagnostic[]> {
    const rel = this.rel(file);
    const result = await spawnWithInactivityTimeout(
      "bash",
      ["-lc", `lake env lean --json ${shellQuote(rel)}`],
      { cwd: this.repoRoot, env: process.env, inactivityTimeoutMs: 5 * 60 * 1000 },
    );
    const combined = [result.stdout, result.stderr].filter(Boolean).join("\n");
    const diagnostics: LeanDiagnostic[] = [];
    for (const line of combined.split(/\r?\n/)) {
      if (!line.trim()) continue;
      const parsed = safeJson(line) as
        | { severity?: string; pos?: { line?: number }; data?: string }
        | null;
      if (!parsed) continue;
      const severity = normalizeSeverity(parsed.severity);
      if (!severity) continue;
      diagnostics.push({
        file: rel,
        line: parsed.pos?.line,
        severity,
        message: parsed.data ?? line,
      });
    }
    const failure =
      result.exitCode === null ||
      result.exitCode !== 0 ||
      result.killedDueToInactivity ||
      result.killedDueToLiveness ||
      result.killedDueToTotalTimeout;
    if (failure && diagnostics.length === 0) {
      const reason = [
        result.exitCode === null
          ? "exit code null"
          : result.exitCode !== 0
            ? `exit code ${result.exitCode}`
            : null,
        result.killedDueToInactivity ? "inactivity timeout" : null,
        result.killedDueToLiveness ? `liveness kill: ${result.killedDueToLiveness}` : null,
        result.killedDueToTotalTimeout ? "total timeout" : null,
      ].filter(Boolean).join("; ");
      // why: failed `lake env lean --json` without parseable diagnostics must be visible to callers.
      diagnostics.push({
        file: rel,
        severity: "error",
        message: `lake env lean failed (${reason || "unknown failure"}): ${combined.trim().slice(-800)}`,
      });
    }
    return diagnostics;
  }

  async goal(file: string, line: number): Promise<GoalState> {
    const rel = this.rel(file);
    const text = await readFile(path.join(this.repoRoot, rel), "utf8");
    const lines = text.split(/\r?\n/);
    const start = Math.max(0, line - 12);
    const end = Math.min(lines.length, line + 8);
    const ctx = lines.slice(start, end).map((l, i) => `${start + i + 1}: ${l}`).join("\n");
    return {
      line_context: lines[line - 1] ?? "",
      goals: [`(CLI fallback — Lean LSP unavailable)\n${ctx}`],
    };
  }

  async termGoal(): Promise<TermGoalState> {
    throw new Error("termGoal not supported by CLI fallback");
  }

  async hoverInfo(): Promise<HoverInfo> {
    throw new Error("hoverInfo not supported by CLI fallback");
  }

  async multiAttempt(): Promise<MultiAttemptResult> {
    throw new Error("multiAttempt not supported by CLI fallback");
  }

  async localSearch(query: string, limit = 10): Promise<LocalSearchHit[]> {
    const safe = query.replace(/[^\w.]/g, "");
    if (!safe) return [];
    const result = await spawnWithInactivityTimeout(
      "bash",
      [
        "-lc",
        `grep -R --line-number --include='*.lean' ${shellQuote(safe)} CausalSmith Causalean | head -n ${Number(limit)}`,
      ],
      { cwd: this.repoRoot, env: process.env, inactivityTimeoutMs: 60_000 },
    );
    return result.stdout
      .split(/\r?\n/)
      .filter(Boolean)
      .map((line) => {
        const m = /^(.*?):(\d+):(.*)$/.exec(line);
        return { name: m?.[3]?.trim() ?? safe, kind: "grep", file: m?.[1] ?? line };
      });
  }

  async stateSearch(): Promise<StateSearchHit[]> {
    throw new Error("stateSearch not supported by CLI fallback");
  }

  async hammerPremise(): Promise<PremiseHit[]> {
    throw new Error("hammerPremise not supported by CLI fallback");
  }

  async findSorries(files: string[]): Promise<EnrichedSorry[]> {
    const out: EnrichedSorry[] = [];
    for (const file of files) {
      const rel = this.rel(file);
      const abs = path.isAbsolute(file) ? file : path.join(this.repoRoot, file);
      const text = await readFile(abs, "utf8");
      const lines = text.split(/\r?\n/);
      let hasSorryWarning = false;
      try {
        const diags = await this.diagnostics(rel);
        hasSorryWarning = diags.some(isSorryDiagnostic);
      } catch {
        hasSorryWarning = true;
      }
      if (!hasSorryWarning) continue;
      const sorryLines = findSorryLines(lines);
      for (const idx of sorryLines) {
        const label = findNearestDeclaration(lines, idx);
        const goal = await this.goal(rel, idx + 1);
        const suggestions = label
          ? (await this.localSearch(label, 3)).map(
              (h) => `${h.name} [${h.kind}] @ ${h.file}`,
            )
          : [];
        out.push({ file: rel, line: idx + 1, label, goal: formatGoal(goal), suggestions });
      }
    }
    return out;
  }

  async build(): Promise<{ success: boolean; log: string; errors: string[] }> {
    return runLakeBuild(this.repoRoot);
  }

  async buildTargets(
    modules: string[],
  ): Promise<{ success: boolean; log: string; errors: string[] }> {
    return runLakeBuild(this.repoRoot, modules);
  }

  async close(): Promise<void> {
    // no-op
  }
}

// ---------------------------------------------------------------------------
// Factory
// ---------------------------------------------------------------------------

export interface CreateLeanLspClientOpts {
  repoRoot: string;
  /** "mcp" (default) or "cli". */
  mode?: "mcp" | "cli";
  binary?: string;
  onStderr?: (chunk: string) => void;
}

export function createLeanLspClient(opts: CreateLeanLspClientOpts): LeanLspClient {
  const envMode = process.env.CAUSALSMITH_LEAN_BACKEND;
  // why: the previous "auto" contract did not actually fall back, so only documented modes are honored.
  const mode = opts.mode ?? (envMode === "cli" ? "cli" : "mcp");
  if (mode === "cli") return new CliLeanLspClient(opts.repoRoot);
  return new McpLeanLspClient({
    repoRoot: opts.repoRoot,
    binary: opts.binary,
    onStderr: opts.onStderr,
  });
}

// ---------------------------------------------------------------------------
// Parsers — tolerate slight schema drift between server versions.
// ---------------------------------------------------------------------------

function parseDiagnostics(value: unknown, file: string): LeanDiagnostic[] {
  if (!isObject(value)) return [];
  // Lean-LSP MCP wraps the payload as `{result:{success,timed_out,items:[...]}}`;
  // `lake env lean --json` returns `{diagnostics:[...]}` at top level; some
  // older MCP versions returned `{items:[...]}` at top level. Try each shape.
  const result = isObject(value.result) ? value.result : null;
  const list = (value.diagnostics ??
    value.items ??
    result?.diagnostics ??
    result?.items ??
    []) as unknown;
  if (!Array.isArray(list)) return [];
  return list.flatMap((entry): LeanDiagnostic[] => {
    if (!isObject(entry)) return [];
    const severity = normalizeSeverity(asString(entry.severity)) ?? "error";
    return [
      {
        file: asString(entry.file) ?? file,
        line: asInt(entry.line ?? (entry.range as { start?: { line?: number } })?.start?.line),
        endLine: asInt((entry.range as { end?: { line?: number } })?.end?.line),
        severity,
        message:
          asString(entry.message) ??
          asString(entry.text) ??
          // Lean 4's lake env lean --json (and some LSP modes) emit the
          // diagnostic body in a `data` field instead of `message`. The
          // `hasSorry` warning specifically arrives this way:
          //   {"kind":"hasSorry","data":"declaration uses `sorry`",...}
          // Without this fallback, isSorryDiagnostic sees an empty string and
          // mis-reports zero sorries.
          asString((entry as { data?: unknown }).data) ??
          "",
      },
    ];
  });
}

function parseGoal(value: unknown): GoalState {
  if (!isObject(value)) return { line_context: "" };
  return {
    line_context: asString(value.line_context) ?? "",
    goals: asStringArray(value.goals),
    goals_before: asStringArray(value.goals_before),
    goals_after: asStringArray(value.goals_after),
  };
}

function parseTermGoal(value: unknown): TermGoalState {
  if (!isObject(value)) return { line_context: "", expected_type: null };
  return {
    line_context: asString(value.line_context) ?? "",
    expected_type: asString(value.expected_type) ?? null,
  };
}

function parseHover(value: unknown, file: string): HoverInfo {
  if (!isObject(value)) return { symbol: "", info: "", diagnostics: [] };
  const diagnostics = Array.isArray(value.diagnostics)
    ? (value.diagnostics as unknown[]).flatMap((d): LeanDiagnostic[] => {
        if (!isObject(d)) return [];
        const severity = normalizeSeverity(asString(d.severity)) ?? "information";
        return [
          {
            file,
            line: asInt(d.line),
            endLine: asInt(d.endLine),
            severity,
            message: asString(d.message) ?? "",
          },
        ];
      })
    : [];
  return {
    symbol: asString(value.symbol) ?? "",
    info: asString(value.info) ?? "",
    diagnostics,
  };
}

function parseMultiAttempt(value: unknown, file: string): MultiAttemptResult {
  if (!isObject(value)) return { outcomes: [], raw: value };
  const rawOutcomes = (value.outcomes ?? value.attempts ?? value.results ?? []) as unknown;
  const outcomes: MultiAttemptOutcome[] = [];
  if (Array.isArray(rawOutcomes)) {
    for (const entry of rawOutcomes) {
      if (!isObject(entry)) continue;
      outcomes.push({
        snippet: asString(entry.snippet) ?? asString(entry.tactic) ?? "",
        goals: asStringArray(entry.goals) ?? null,
        diagnostics: Array.isArray(entry.diagnostics)
          ? parseDiagnostics({ diagnostics: entry.diagnostics }, file)
          : [],
        raw: entry,
      });
    }
  }
  return { outcomes, raw: value };
}

function parseLocalSearch(value: unknown): LocalSearchHit[] {
  if (!isObject(value)) return [];
  const items = (value.items ?? []) as unknown;
  if (!Array.isArray(items)) return [];
  return items.flatMap((item): LocalSearchHit[] => {
    if (!isObject(item)) return [];
    return [
      {
        name: asString(item.name) ?? "",
        kind: asString(item.kind) ?? "",
        file: asString(item.file) ?? "",
      },
    ];
  });
}

function parseStateSearch(value: unknown): StateSearchHit[] {
  if (!isObject(value)) return [];
  const items = (value.items ?? []) as unknown;
  if (!Array.isArray(items)) return [];
  return items.flatMap((item): StateSearchHit[] => {
    if (!isObject(item)) return [];
    const name = asString(item.name);
    return name ? [{ name }] : [];
  });
}

function parsePremise(value: unknown): PremiseHit[] {
  if (!isObject(value)) return [];
  const items = (value.items ?? value.premises ?? []) as unknown;
  if (!Array.isArray(items)) return [];
  return items.flatMap((item): PremiseHit[] => {
    if (!isObject(item)) return [];
    const name = asString(item.name);
    if (!name) return [];
    const score = asNumber(item.score);
    return [score === null ? { name } : { name, score }];
  });
}

function parseBuild(value: unknown): { success: boolean; log: string; errors: string[] } {
  if (!isObject(value)) {
    const text = typeof value === "string" ? value : "";
    return { success: !/error/i.test(text), log: text, errors: [] };
  }
  const log = asString(value.log) ?? (Array.isArray(value.log_tail) ? value.log_tail.join("\n") : "") ?? "";
  const errors = Array.isArray(value.errors)
    ? (value.errors as unknown[]).map((e) => (typeof e === "string" ? e : JSON.stringify(e)))
    : [];
  // why: an explicit MCP success boolean is authoritative, even when errors is empty.
  const success = typeof value.success === "boolean" ? value.success : errors.length === 0 && !/error/i.test(log);
  return { success, log, errors };
}

function formatGoal(g: GoalState): string {
  const parts: string[] = [];
  if (g.line_context) parts.push(`line: ${g.line_context}`);
  if (g.goals?.length) parts.push(`goals:\n${g.goals.join("\n---\n")}`);
  if (g.goals_before?.length) parts.push(`goals_before:\n${g.goals_before.join("\n---\n")}`);
  if (g.goals_after?.length) parts.push(`goals_after:\n${g.goals_after.join("\n---\n")}`);
  return parts.join("\n\n");
}

// ---------------------------------------------------------------------------
// Tiny helpers
// ---------------------------------------------------------------------------

function isObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function asString(v: unknown): string | undefined {
  return typeof v === "string" ? v : undefined;
}

function asInt(v: unknown): number | undefined {
  if (typeof v === "number" && Number.isFinite(v)) return Math.trunc(v);
  return undefined;
}

function asNumber(v: unknown): number | null {
  return typeof v === "number" && Number.isFinite(v) ? v : null;
}

function asStringArray(v: unknown): string[] | undefined {
  if (!Array.isArray(v)) return undefined;
  return v.filter((x): x is string => typeof x === "string");
}

function safeJson(line: string): unknown | null {
  try {
    return JSON.parse(line);
  } catch {
    return null;
  }
}

function normalizeSeverity(value: string | undefined): LeanDiagnostic["severity"] | null {
  if (value === "error" || value === "warning" || value === "information") return value;
  if (value === "info") return "information";
  return null;
}

/**
 * Strip Lean comments from a line, tracking nested block-comment depth across
 * lines via `state.depth`. Handles `/- ... -/`, `/-! ... -/`, and `--` line
 * comments. Strings are NOT modeled — we don't expect `sorry` inside a string
 * literal in practice, and Lean strings can't contain `--` toggling anyway.
 */
function stripCommentsLine(
  line: string,
  state: { depth: number },
): string {
  let out = "";
  let i = 0;
  while (i < line.length) {
    if (state.depth > 0) {
      // Inside a block comment. Look for `-/` or a nested `/-`.
      if (line[i] === "-" && line[i + 1] === "/") {
        state.depth -= 1;
        i += 2;
      } else if (line[i] === "/" && line[i + 1] === "-") {
        state.depth += 1;
        i += 2;
      } else {
        i += 1;
      }
      continue;
    }
    // Not in a block comment.
    if (line[i] === "-" && line[i + 1] === "-") {
      // Line comment: drop the rest of the line.
      break;
    }
    if (line[i] === "/" && line[i + 1] === "-") {
      // Entering a block comment (handles `/-` and `/-!`).
      state.depth += 1;
      i += 2;
      continue;
    }
    out += line[i];
    i += 1;
  }
  return out;
}

/**
 * Return the 0-indexed line numbers where a real `sorry` token appears, after
 * stripping Lean comments. False positives from comments (line and block) are
 * filtered out.
 */
function findSorryLines(lines: string[]): number[] {
  const state = { depth: 0 };
  const hits: number[] = [];
  for (let idx = 0; idx < lines.length; idx++) {
    const stripped = stripCommentsLine(lines[idx], state);
    if (/\bsorry\b/.test(stripped)) hits.push(idx);
  }
  return hits;
}

/**
 * True when a diagnostic is the Lean "declaration uses 'sorry'" warning.
 * The exact wording varies slightly across Lean versions ("uses 'sorry'",
 * "uses sorry"), so match a tolerant case-insensitive substring while still
 * gating on warning severity.
 */
function isSorryDiagnostic(d: LeanDiagnostic): boolean {
  if (d.severity !== "warning") return false;
  return /declaration\s+uses\s+['`"]?sorry['`"]?/i.test(d.message);
}

/**
 * True when a diagnostic is a non-fatal STYLE linter message (doc-string
 * spacing, long lines, whitespace). These can surface with `error`-flavoured
 * text but do NOT fail `lake build`, so Stage 3 must not treat them as
 * proof-repair work items.
 */
function isStyleLintDiagnostic(d: LeanDiagnostic): boolean {
  return /doc-strings should end|exceeds the \d+ character|missing space|trailing whitespace|linter\.style|should be written as/i.test(
    d.message,
  );
}

function findNearestDeclaration(lines: string[], sorryIndex: number): string | undefined {
  for (let idx = sorryIndex; idx >= 0; idx--) {
    const match = lines[idx].match(
      /^\s*(?:private\s+)?(?:theorem|lemma|def|abbrev|instance|noncomputable\s+def)\s+([A-Za-z0-9_'.]+)/,
    );
    if (match) return match[1];
  }
  return undefined;
}

function shellQuote(value: string): string {
  return `'${value.replaceAll("'", "'\\''")}'`;
}
