// F5 docstring-coverage step. Docstrings are docstring-canonical (the site renders each
// declaration's docstring as its natural-language statement, and P4 refuses to emit a bundle
// with undocumented declarations), so coverage is authored HERE — the guaranteed-final
// Lean-edit point of the research run — not at presentation time.

import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { readdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import type { PipelineContext, StateJson } from "../types.js";
import { artifactPaths, readPrompt, type StageDeps } from "../pipeline_support.js";
import { isPaperTmpPath } from "../paths.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";

const execFileP = promisify(execFile);
const LAKE_TIMEOUT_MS = 1800_000;

export interface UndocumentedDecl {
  name: string;
  file: string;
  line: number;
  kind: string;
}

/** Dotted module names for every .lean source in the run dir (find-derived, sorted; the
 * disposable `tmp/` agent workspace is excluded — it is not part of the published run). */
export function moduleNamesFor(leanSubdir: string, relFiles: string[]): string[] {
  const prefix = leanSubdir.replace(/\//g, ".");
  return relFiles
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .map((f) => `${prefix}.${f.replace(/\.lean$/, "").replace(/[\\/]+/g, ".")}`)
    .sort();
}

/** The prompt's per-file declaration list (file heading, then `  L<line> <kind> <name>` rows). */
export function declListFor(undoc: UndocumentedDecl[]): string {
  const byFile = new Map<string, UndocumentedDecl[]>();
  for (const e of undoc) byFile.set(e.file, [...(byFile.get(e.file) ?? []), e]);
  return [...byFile.entries()]
    .map(([f, es]) =>
      [f, ...es.slice().sort((a, b) => a.line - b.line).map((e) => `  L${e.line} ${e.kind} ${e.name}`)].join("\n"),
    )
    .join("\n\n");
}

/**
 * Ensure every declaration in the run's Lean modules carries a docstring. Returns `null` when
 * coverage holds; otherwise a block reason for the F5 caller (same contract as the crosswalk
 * emit). One codex pass documents the gaps (docstring insertions only); the rebuild validates
 * the edits (restored byte-for-byte on a build failure) and a re-extraction confirms coverage.
 * Runs BEFORE the crosswalk emit: docstring insertion shifts line numbers, and the banked
 * crosswalk must record the post-docstring lines.
 */
export async function ensureDocstringCoverage(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<string | null> {
  const paths = artifactPaths(args.ctx, args.state);
  const relFiles = (await readdir(paths.leanDir, { recursive: true }).catch((err: NodeJS.ErrnoException) => {
    if (err.code === "ENOENT") return [] as string[]; // no Lean dir — nothing to document
    throw err; // any other readdir failure must not silently pass the gate
  })).map(String);
  const prefix = args.state.lean_subdir.replace(/\//g, ".");
  // Include the root umbrella module (`<leanDir>.lean`, a sibling of the dir): it is
  // import-only by convention, but a declaration landing there must still be covered —
  // P4 verifies coverage over every module it indexes.
  const rootModule = existsSync(`${paths.leanDir}.lean`) ? [prefix] : [];
  const modules = [...rootModule, ...moduleNamesFor(args.state.lean_subdir, relFiles)];
  if (modules.length === 0) return null;
  const indexOut = path.join(paths.formalizationDir, "docstring_coverage.json");
  const lake = (lakeArgs: string[]) =>
    execFileP("lake", ["-d", args.ctx.repoRoot, ...lakeArgs], {
      cwd: args.ctx.repoRoot,
      maxBuffer: 16 * 1024 * 1024,
      timeout: LAKE_TIMEOUT_MS,
    });
  // Build first: paper_index reads OLEANS and silently emits an empty index over stale ones.
  const extractUndocumented = async (): Promise<UndocumentedDecl[]> => {
    await lake(["build", ...modules]);
    await lake(["exe", "paper_index", "--",
      "--prefix", prefix, "--src-root", args.ctx.repoRoot, "--modules", modules.join(","), "--out", indexOut]);
    const idx = JSON.parse(await readFile(indexOut, "utf8")) as {
      entries?: { name?: unknown; file?: unknown; line?: unknown; kind?: unknown; doc?: unknown }[];
    };
    if (!Array.isArray(idx.entries)) throw new Error(`docstring extraction produced no entries array (${indexOut})`);
    return idx.entries.flatMap((e) =>
      !e.doc && typeof e.name === "string" && typeof e.file === "string"
        ? [{ name: e.name, file: e.file, line: typeof e.line === "number" ? e.line : 0,
            kind: typeof e.kind === "string" ? e.kind : "decl" }]
        : [],
    );
  };

  let undoc: UndocumentedDecl[];
  try {
    undoc = await extractUndocumented();
  } catch (err) {
    return (
      `F5 docstring coverage could not be computed (${(err instanceof Error ? err.message : String(err)).slice(0, 300)}). ` +
      `Resolve the build/extraction error then resume; the docstring gate cannot be skipped ` +
      `(P4 refuses to emit an undocumented bundle).`
    );
  }
  if (undoc.length === 0) return null;

  // Snapshot the exact bytes of every target file BEFORE the codex pass, so a build-failure
  // rollback restores only this pass's docstring edits. NEVER `git checkout` here: it reverts
  // to HEAD and destroys unrelated uncommitted work this pass did not author.
  const snapshot = new Map<string, string>();
  for (const f of new Set(undoc.map((e) => e.file))) {
    snapshot.set(f, await readFile(path.join(args.ctx.repoRoot, f), "utf8"));
  }
  const prompt = (await readPrompt(args.ctx, "stage5_docstrings.txt"))
    .replaceAll("{{package_root}}", args.ctx.repoRoot)
    .replaceAll("{{decl_list}}", declListFor(undoc));
  await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "5",
    label: "F5 docstring coverage",
    prompt,
    promptSources: ["stage5_docstrings.txt"],
    model: MODEL_PLAN.stage5.model,
    reasoningEffort: MODEL_PLAN.stage5.effort,
  });
  let residual: UndocumentedDecl[];
  try {
    residual = await extractUndocumented();
  } catch (err) {
    for (const [f, content] of snapshot) {
      await writeFile(path.join(args.ctx.repoRoot, f), content, "utf8");
    }
    return (
      `F5 docstring pass broke the build; its edits were restored byte-for-byte ` +
      `(${err instanceof Error ? err.message.slice(0, 300) : String(err)}). ` +
      `Document the declarations by hand (first paragraph = NL translation) then resume.`
    );
  }
  if (residual.length > 0) {
    return (
      `F5 docstring coverage: ${residual.length} declaration(s) still undocumented after the docstring pass — ` +
      residual.slice(0, 12).map((e) => `${e.file}:${e.line} ${e.name}`).join(", ") +
      (residual.length > 12 ? ` (+${residual.length - 12} more)` : "") +
      `. Document them (docstring-canonical workflow: first paragraph = the NL translation) then resume.`
    );
  }
  return null;
}
