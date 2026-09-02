import { readFile } from "node:fs/promises";
import { parseTypedCore } from "../discovery/core/core_io.js";
import type { Core } from "../discovery/core/schema.js";

/** Remove fields that F1.5/F2 never need while preserving the typed structure. */
export function formalizationCoreContextValue(core: Core): Record<string, unknown> {
  const projected = structuredClone(core) as unknown as Record<string, unknown>;
  for (const key of [
    "tldr",
    "project_justification",
    "related_work",
    "interpretation",
    "technical_internal_limitation",
    "statement_notes",
    "comparator_promise_table",
    "bibliography",
  ]) delete projected[key];
  if (Array.isArray(projected.statements)) {
    projected.statements = projected.statements.map((value) => {
      const statement = { ...(value as Record<string, unknown>) };
      delete statement.proof_tex;
      delete statement.justification;
      delete statement.gap;
      delete statement.consumer;
      return statement;
    });
  }
  return projected;
}

/** Structural core view for F1.5 reuse-fit and F2 scaffolding. These stages
 * need exact declarations and dependency metadata, not the completed paper's
 * proof bodies, positioning prose (per-statement justification/gap/consumer,
 * the comparator table), or bibliography (F2's cited-gate docstrings come from
 * the plan's `citations[]`, which F1 mints from the raw core). Parse first so
 * projection never hides a malformed/missing core. PROMPT-ONLY: this string is
 * never persisted; later stages read core.json itself. Serialized compact —
 * indentation was ~11% of the F2/F1.5 prompt bytes. */
export async function readFormalizationCoreContext(
  corePath: string,
  label: string,
): Promise<string> {
  let raw: string;
  try {
    raw = await readFile(corePath, "utf8");
  } catch (err) {
    throw new Error(`${label}: required typed core is unreadable at ${corePath}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const core = parseTypedCore(raw, `${label}: typed core ${corePath}`);
  return JSON.stringify(formalizationCoreContextValue(core));
}
