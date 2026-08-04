import { readFile } from "node:fs/promises";
import { parseTypedCore } from "../discovery/core/core_io.js";

/** Structural core view for F1.5 reuse-fit and F2 scaffolding. These stages
 * need exact declarations and dependency metadata, not the completed paper's
 * proof bodies or publication prose. Parse first so projection never hides a
 * malformed/missing core. */
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
  const projected = structuredClone(core) as unknown as Record<string, unknown>;
  for (const key of [
    "tldr",
    "project_justification",
    "related_work",
    "interpretation",
    "technical_internal_limitation",
    "statement_notes",
  ]) delete projected[key];
  if (Array.isArray(projected.statements)) {
    projected.statements = projected.statements.map((value) => {
      const statement = { ...(value as Record<string, unknown>) };
      delete statement.proof_tex;
      return statement;
    });
  }
  return JSON.stringify(projected, null, 2);
}
