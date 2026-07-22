import { appendFile, mkdir } from "node:fs/promises";
import { dirname } from "node:path";
import type { PaperDeps } from "./pipeline.js";
import { PROMPT_MARKER_PREFIX } from "./prompt_io.js";

/**
 * Per-run agent-call transcript for the causalsmith pipeline — the presentation-phase
 * analogue of causalsmith's `pipeline_support.logAgentCall`. Every codex/claude dispatch
 * (P0…P5, since they all run through `PaperDeps`) appends its INPUT prompt + OUTPUT here,
 * so the reasoning behind every stage is inspectable and an expensive call is never lost
 * (the raw output lands here before any caller parses it). One file per run.
 *
 * Logging the FULL assembled input prompt alongside the output is deliberate: a wrong /
 * empty / mis-assembled prompt (e.g. a fail-open `existsSync(p)?read:""` that silently fed
 * an empty source block) is then directly visible, not inferred from the model's behaviour.
 * Best-effort: append/mkdir failures are swallowed so logging never throws into the call path.
 */
export async function logAgentCall(
  logPath: string,
  agent: string,
  prompt: string,
  model: string,
  effort: string,
  ms: number,
  output: string,
): Promise<void> {
  // Prefer the explicit `=== PROMPT: <name> ===` marker `presentationPrompt` emits: every
  // presentation prompt is prefixed with the shared prose/cross-reference contracts, so the
  // first non-empty line is the SAME for all 27 templates and is useless as a header.
  // Fall back to the first non-empty line for non-templated (ad-hoc) dispatches.
  const lines = prompt.split("\n");
  const marker = lines.find((l) => l.startsWith(PROMPT_MARKER_PREFIX));
  const name = marker?.slice(PROMPT_MARKER_PREFIX.length).replace(/\s*===\s*$/, "").trim();
  const firstBody = (lines.find((l) => l.trim().length > 0 && !l.startsWith(PROMPT_MARKER_PREFIX)) ?? "").trim();
  const stageHint = (name ? `[${name}] ${firstBody}` : firstBody).slice(0, 110);
  const entry =
    `\n===== ${agent} model=${model} effort=${effort} dur=${(ms / 1000).toFixed(0)}s :: ${stageHint} =====\n` +
    `----- INPUT (${prompt.length} chars) -----\n${prompt}\n` +
    `----- OUTPUT -----\n${output}\n`;
  await mkdir(dirname(logPath), { recursive: true }).catch(() => {});
  await appendFile(logPath, entry).catch(() => {});
}

/**
 * Wrap a `PaperDeps`'s `runClaude`/`runCodex` so EVERY dispatch transcribes its INPUT+OUTPUT
 * to `logPath` (raw output logged on return, before any caller parses it; a crashed/timed-out
 * call still gets an entry with any partial stdout the error carries, then the throw propagates).
 * The returned deps are a drop-in replacement — identical signatures and return values.
 */
export function withAgentLogging(deps: PaperDeps, logPath: string): PaperDeps {
  return {
    ...deps,
    runClaude: async (args) => {
      const t0 = Date.now();
      try {
        const out = await deps.runClaude(args);
        await logAgentCall(logPath, "claude", args.prompt, args.model, "-", Date.now() - t0, out);
        return out;
      } catch (err) {
        const partial = (err as { stdout?: string })?.stdout ?? "";
        await logAgentCall(
          logPath,
          "claude",
          args.prompt,
          args.model,
          "-",
          Date.now() - t0,
          `[CALL THREW: ${err instanceof Error ? err.message : String(err)}]\n${partial}`,
        );
        throw err;
      }
    },
    runCodex: async (args) => {
      const t0 = Date.now();
      try {
        const out = await deps.runCodex(args);
        await logAgentCall(
          logPath,
          "codex",
          args.prompt,
          args.model ?? deps.codexModel ?? "?",
          args.reasoningEffort ?? "?",
          Date.now() - t0,
          out.stdout,
        );
        return out;
      } catch (err) {
        const partial = (err as { stdout?: string })?.stdout ?? "";
        await logAgentCall(
          logPath,
          "codex",
          args.prompt,
          args.model ?? deps.codexModel ?? "?",
          args.reasoningEffort ?? "?",
          Date.now() - t0,
          `[CALL THREW: ${err instanceof Error ? err.message : String(err)}]\n${partial}`,
        );
        throw err;
      }
    },
  };
}
