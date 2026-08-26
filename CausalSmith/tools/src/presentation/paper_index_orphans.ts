import { existsSync } from "node:fs";
import { readFile, readdir } from "node:fs/promises";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import path from "node:path";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";

const execFileAsync = promisify(execFile);

/**
 * Files under `dir` that are untracked in git (relative paths, `/`-separated).
 * Untracked run modules are by definition another run's work-in-progress: a
 * publish/export snapshots HEAD, so an untracked file can never ship, and a
 * concurrent follow-on run extending the same substrate directory must not fail
 * this paper's index gate. Outside a git work tree (or if git is unavailable)
 * the set is empty, i.e. every file is treated as tracked — the strict
 * behaviour is unchanged.
 */
async function untrackedFilesIn(dir: string): Promise<Set<string>> {
  try {
    const { stdout } = await execFileAsync(
      "git",
      ["-C", dir, "ls-files", "--others", "--exclude-standard", "-z", "."],
      { maxBuffer: 16 * 1024 * 1024 },
    );
    return new Set(stdout.split("\0").filter(Boolean));
  } catch {
    return new Set();
  }
}

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
  const untracked = await untrackedFilesIn(runDir);
  const orphans: OrphanPaperModule[] = [];
  for (const file of files) {
    const normalizedFile = file.replaceAll(path.sep, "/");
    // The run-local tmp/ tree is an explicitly disposable proof-probe
    // workspace. It is excluded from graph extraction and never belongs in a
    // published module inventory, even when a probe uses public declarations.
    if (normalizedFile === "tmp.lean" || normalizedFile.startsWith("tmp/")) continue;
    // Git-untracked modules are in-progress work (typically a concurrent
    // follow-on run extending this substrate directory), invisible to any
    // HEAD-snapshot publish — never this paper's inventory gap. Loud, not
    // silent: once these files are committed they re-enter the check, and the
    // note below is the only trace of what was skipped before that.
    if (untracked.has(normalizedFile)) {
      console.warn(`[paper-index] skipping git-untracked module (in-progress work): ${normalizedFile}`);
      continue;
    }
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
 * `@[congr]`), the on-demand equation lemmas `eq_def` / `eq_unfold` / `eq_<i>`,
 * and the `deriving Fintype, DecidableEq` helpers `proxyType` / `proxyTypeEquiv`
 * (range-less; tripped the strict line-zero/null-source lint on a correct bundle,
 * 2026-08-26). Mirrors `isSyntheticCompanionLeaf` in `LibraryIndexCore.lean`;
 * keep the two in sync.
 */
export const SYNTHETIC_COMPANION_RE = /\.(?:congr_simp|eq_def|eq_unfold|eq_\d+|proxyType|proxyTypeEquiv)$/;
