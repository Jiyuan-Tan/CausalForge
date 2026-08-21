import { existsSync } from "node:fs";
import { readFile, readdir } from "node:fs/promises";
import path from "node:path";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";

export interface OrphanPaperModule {
  module: string;
  file: string;
}

/**
 * Whether a Lean source file contains a declaration that the paper index should
 * expose. Comments and literals are masked first, and declarations carrying a
 * `private` modifier are deliberately ignored.
 */
export function hasPublicPaperDeclaration(source: string): boolean {
  const masked = maskLeanCommentsAndStrings(source);
  const declaration =
    /^[ \t]*(?:@\[[^\]]*\][ \t\r\n]*)*((?:(?:noncomputable|private|protected|scoped|local|partial|unsafe|nonrec)\s+)*)(?:theorem|lemma|def)\b/gm;
  let match: RegExpExecArray | null;
  while ((match = declaration.exec(masked))) {
    if (!/\bprivate\b/.test(match[1])) return true;
  }
  return false;
}

/**
 * Find physical run modules with public paper declarations but no declaration
 * entry in the generated paper index.
 */
export async function findOrphanPaperModules(
  runDir: string,
  modulePrefix: string,
  indexedEntryModules: ReadonlySet<string>,
): Promise<OrphanPaperModule[]> {
  if (!existsSync(runDir)) return [];
  const files = (await readdir(runDir, { recursive: true }))
    .map(String)
    .filter((file) => file.endsWith(".lean"))
    .sort();
  const orphans: OrphanPaperModule[] = [];
  for (const file of files) {
    const normalizedFile = file.replaceAll(path.sep, "/");
    // The run-local tmp/ tree is an explicitly disposable proof-probe
    // workspace. It is excluded from graph extraction and never belongs in a
    // published module inventory, even when a probe uses public declarations.
    if (normalizedFile === "tmp.lean" || normalizedFile.startsWith("tmp/")) continue;
    const module = `${modulePrefix}.${normalizedFile.slice(0, -".lean".length).replaceAll("/", ".")}`;
    if (indexedEntryModules.has(module)) continue;
    const source = await readFile(path.join(runDir, file), "utf8");
    if (hasPublicPaperDeclaration(source)) orphans.push({ module, file: normalizedFile });
  }
  return orphans;
}

/**
 * Compiler-synthesized companion theorems that the Lean extractor omits from
 * paper/library indexes unless demonstrably hand-authored: `congr_simp` (from
 * `@[congr]`) and the on-demand equation lemmas `eq_def` / `eq_unfold` /
 * `eq_<i>`. Mirrors `isSyntheticCompanionLeaf` in `LibraryIndexCore.lean`;
 * keep the two in sync.
 */
export const SYNTHETIC_COMPANION_RE = /\.(?:congr_simp|eq_def|eq_unfold|eq_\d+)$/;
