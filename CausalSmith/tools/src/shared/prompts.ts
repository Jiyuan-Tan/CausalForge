/**
 * Shared prompt-template helpers used by every study-pipeline stage.
 *
 * `loadPromptTemplate` reads a file from a caller-supplied prompts directory.
 * `renderTemplate` substitutes `{{var}}` placeholders, leaving unknown vars
 * intact (so a missing var is visible in the codex output, not silently empty).
 *
 * Replacement uses the function form of `String.replace` so values containing
 * `$1` / `$&` / `$$` are not interpreted as capture references.
 */
import { readFile } from "node:fs/promises";
import path from "node:path";

export async function loadPromptTemplate(promptsDir: string, name: string): Promise<string> {
  return readFile(path.join(promptsDir, name), "utf8");
}

export function renderTemplate(tpl: string, vars: Record<string, string>): string {
  return tpl.replace(/{{(\w+)}}/g, (_, k: string) => (k in vars ? vars[k] : `{{${k}}}`));
}
