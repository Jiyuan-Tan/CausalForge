import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { renderTemplate } from "../shared/prompts.js";
import { hashEnvBody } from "./tex_anchors.js";

/** Bump whenever the global manuscript-prose contract changes so authored-prose caches re-draft. */
export const PRESENTATION_PROSE_POLICY_VERSION = "house-typography-related-work-v6";

/** Leading marker naming the template, so the per-run transcript stays diagnosable. */
export const PROMPT_MARKER_PREFIX = "=== PROMPT: ";

/** Prompts that emit verdicts/JSON about existing text rather than authoring
 * reader-facing prose. They receive a short digest of the global contracts —
 * enough to FLAG violations as findings — instead of the full ~4k-char contracts
 * that every dispatch previously carried (measured 1.3–2.6M chars/run, 2026-08-20
 * token audit). Every authoring prompt (renders, drafts, refinements, revisions,
 * synthesize) keeps the full contracts. */
export const VERDICT_ONLY_PROMPTS: ReadonlySet<string> = new Set([
  "proof_audit",
  "statement_equivalence",
  "statement_equivalence_batch",
  "p3_citation_support_batch",
  "p3_overclaim",
  "p1_notation_check",
]);
// p3_rubric is deliberately NOT verdict-only: it scores prose quality directly
// against the contracts, so it keeps the full text.

/** Cache-key fingerprint over a prompt and the contracts it is dispatched with, so prompt
 *  edits are self-invalidating (no hand-bumped version strings). One fingerprint PER
 *  CONSUMER group, so editing one prompt does not cold unrelated caches. The element order
 *  — names first, then the de-duplicated contracts — is load-bearing: changing it would
 *  move every existing key (formula churn must not cold a live cache). */
export async function promptFingerprint(...names: string[]): Promise<string> {
  const promptDir = join(import.meta.dirname, "prompts");
  return hashEnvBody(
    (
      await Promise.all(
        [...names, ...new Set(names.flatMap((n) => promptContractFiles(n)))].map((n) =>
          readFile(join(promptDir, `${n}.txt`), "utf8"),
        ),
      )
    ).join("§"),
  );
}

/** Contract files prepended to a prompt, per its kind — exported so cache-key
 * fingerprints hash exactly what the prompt is dispatched with (the digest lives
 * in prompts/contract_digest.txt precisely so edits to it move fingerprints). */
export const promptContractFiles = (name: string): string[] =>
  VERDICT_ONLY_PROMPTS.has(name)
    ? ["contract_digest"]
    : ["prose_style_contract", "cross_reference_contract"];

export async function presentationPrompt(
  name: string,
  vars: Record<string, string>,
): Promise<string> {
  const promptDir = join(import.meta.dirname, "prompts");
  const [tpl, ...contracts] = await Promise.all([
    readFile(join(promptDir, `${name}.txt`), "utf8"),
    ...promptContractFiles(name).map((n) => readFile(join(promptDir, `${n}.txt`), "utf8")),
  ]);
  // The contracts (or their digest, for verdict-only prompts) are prepended to every
  // presentation prompt, so the first non-empty line is identical across many
  // dispatches. Emit an explicit prompt-name marker that `agent_log.logAgentCall`
  // greps for, otherwise every entry in agent_calls.log gets the same header and the
  // transcript stops being diagnosable.
  const header = contracts.map((c) => c.trim()).join("\n\n");
  return `${PROMPT_MARKER_PREFIX}${name} ===\n\n${header}\n\n${renderTemplate(tpl, vars)}`;
}
