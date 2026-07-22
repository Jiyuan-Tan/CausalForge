// Framework primitive 3 of 3: the logged agent-dispatch boundary. Two rules
// from hard-won debugging (CLAUDE.md "read the agent's OWN I/O"):
//   (a) every dispatch logs its RESOLVED input (byte length + sources) BEFORE
//       the call, so "the model never received X" is visible in pipeline.jsonl;
//   (b) an empty prompt is a fault, never a dispatch — the existsSync?read:""
//       fail-open class dies here.
import { appendPipelineLog } from "../log.js";
import { extractJsonObject } from "../judgment.js";
import type { PipelineContext, Stage } from "../types.js";
import type { StageDeps } from "../pipeline_support.js";
import type { CodexRunInput } from "../shared/codex.js";
import type { ClaudeRunInput } from "../workers/claude.js";

export interface DispatchAgentArgs {
  ctx: Pick<PipelineContext, "repoRoot" | "qid" | "specialization">;
  deps: { runCodex: StageDeps["runCodex"] };
  stage: Stage;
  /** Short human label for the log, e.g. "D-1.1 lit-review". */
  label: string;
  prompt: string;
  /** The files/blocks that fed the prompt — logged so a missing input is visible. */
  promptSources: string[];
  model: string;
  reasoningEffort: CodexRunInput["reasoningEffort"];
  inactivityTimeoutMs?: number;
  /** Forwarded to runCodex (e.g. the D0.5.G cold referee disables the Lean LSP). */
  leanLsp?: boolean;
  /** Defaults to ctx.repoRoot. */
  cwd?: string;
  /** Forwarded to runCodex. The F2.5/F4 reviewer fans out concurrently and must
   *  disable codex's native sub-agents (see CodexRunInput.multiAgent). */
  multiAgent?: boolean;
}

export async function dispatchAgent(args: DispatchAgentArgs): Promise<{ stdout: string; stderr: string }> {
  if (args.prompt.trim().length === 0) {
    throw new Error(
      `dispatch '${args.label}' (stage ${args.stage}) resolved to an EMPTY prompt — refusing to dispatch. ` +
        `Sources: [${args.promptSources.join(", ")}]`,
    );
  }
  const started = Date.now();
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch",
    duration_ms: 0,
    model: args.model,
    message: `${args.label}: prompt ${Buffer.byteLength(args.prompt, "utf8")} bytes from [${args.promptSources.join(", ")}]`,
  });
  const out = await args.deps.runCodex({
    prompt: args.prompt,
    cwd: args.cwd ?? args.ctx.repoRoot,
    model: args.model,
    reasoningEffort: args.reasoningEffort,
    inactivityTimeoutMs: args.inactivityTimeoutMs,
    ...(args.leanLsp !== undefined ? { leanLsp: args.leanLsp } : {}),
    ...(args.multiAgent !== undefined ? { multiAgent: args.multiAgent } : {}),
  });
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch-complete",
    duration_ms: Date.now() - started,
    model: args.model,
    message: `${args.label}: stdout ${Buffer.byteLength(out.stdout, "utf8")} bytes`,
  });
  return out;
}

/** Uniform stdout→JSON boundary: one place that knows how agent JSON is
 *  extracted and how failure is represented (value, not exception). */
export function parseAgentJson(
  stdout: string,
): { json: Record<string, unknown>; parseError?: undefined } | { json?: undefined; parseError: string } {
  try {
    return { json: extractJsonObject(stdout) as Record<string, unknown> };
  } catch (err) {
    return { parseError: err instanceof Error ? err.message : String(err) };
  }
}

/** Claude-runner twin of dispatchAgent: same two rules (empty-prompt refusal,
 *  resolved-I/O logging) around deps.runClaude. The full ClaudeRunInput passes
 *  through `input` so callers keep allowedTools/mcpConfigPath/etc. untouched. */
export async function dispatchClaudeAgent(args: {
  ctx: Pick<PipelineContext, "repoRoot" | "qid" | "specialization">;
  deps: { runClaude: StageDeps["runClaude"] };
  stage: Stage;
  label: string;
  /** The files/blocks that fed the prompt — logged so a missing input is visible. */
  promptSources: string[];
  input: ClaudeRunInput;
}): Promise<string> {
  if (args.input.prompt.trim().length === 0) {
    throw new Error(
      `dispatch '${args.label}' (stage ${args.stage}) resolved to an EMPTY prompt — refusing to dispatch. ` +
        `Sources: [${args.promptSources.join(", ")}]`,
    );
  }
  const started = Date.now();
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch",
    duration_ms: 0,
    model: args.input.model,
    message: `${args.label}: prompt ${Buffer.byteLength(args.input.prompt, "utf8")} bytes from [${args.promptSources.join(", ")}]`,
  });
  const out = await args.deps.runClaude(args.input);
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch-complete",
    duration_ms: Date.now() - started,
    model: args.input.model,
    message: `${args.label}: stdout ${Buffer.byteLength(out, "utf8")} bytes`,
  });
  return out;
}
