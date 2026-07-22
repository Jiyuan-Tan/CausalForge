import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { renderTemplate } from "../shared/prompts.js";

/** Bump whenever the global manuscript-prose contract changes so authored-prose caches re-draft. */
export const PRESENTATION_PROSE_POLICY_VERSION = "affirmative-contribution-v4-cleveref-all";

/** Leading marker naming the template, so the per-run transcript stays diagnosable. */
export const PROMPT_MARKER_PREFIX = "=== PROMPT: ";

export async function presentationPrompt(
  name: string,
  vars: Record<string, string>,
): Promise<string> {
  const promptDir = join(import.meta.dirname, "prompts");
  const [policy, crossReferences, tpl] = await Promise.all([
    readFile(join(promptDir, "prose_style_contract.txt"), "utf8"),
    readFile(join(promptDir, "cross_reference_contract.txt"), "utf8"),
    readFile(join(promptDir, `${name}.txt`), "utf8"),
  ]);
  // The two contracts are prepended to every presentation prompt, so the first
  // non-empty line is identical across all dispatches. Emit an explicit prompt-name
  // marker that `agent_log.logAgentCall` greps for, otherwise every entry in
  // agent_calls.log gets the same header and the transcript stops being diagnosable.
  return `${PROMPT_MARKER_PREFIX}${name} ===\n\n${policy.trim()}\n\n${crossReferences.trim()}\n\n${renderTemplate(tpl, vars)}`;
}
