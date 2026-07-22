import { join, resolve, dirname } from "node:path";
import { existsSync, readFileSync, mkdirSync } from "node:fs";
import { findCausalSmithRoot } from "../shared/repo_root.js";


/** `qid`/`spec` become literal path segments — reject anything that could escape
 *  the presentation/bank directories (separators, traversal, whitespace). */
export function assertRunSlug(label: string, value: string): void {
  if (!/^[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(value) || value.includes("..")) {
    throw new Error(`invalid ${label} "${value}": must be a [A-Za-z0-9_.-] slug`);
  }
}

/**
 * repoRoot = the CausalSmith package root (dir containing lakefile.toml with
 * name "CausalSmith"), same convention as src/cli.ts.
 */
export function bankAcceptedDir(repoRoot: string, qid: string, spec: string): string {
  assertRunSlug("qid", qid);
  assertRunSlug("spec", spec);
  return join(repoRoot, "doc", "research", "_bank", "accepted", `${qid}_${spec}`);
}

export function presentationDir(repoRoot: string, qid: string, spec: string): string {
  assertRunSlug("qid", qid);
  assertRunSlug("spec", spec);
  return join(repoRoot, "doc", "presentation", `${qid}_${spec}`);
}

/**
 * Per-run LOG directory: `<presentationDir(qid,spec)>/logs/`. Mirrors causalsmith's
 * `<formalizationDir>/logs/` convention — holds the transient run-log artifacts (the
 * agent-call I/O transcript) so the presentation-dir root stays uncluttered with only
 * the durable paper bundle. Use `ensureLogsDir` to also create it.
 */
export function logsDir(repoRoot: string, qid: string, spec: string): string {
  return join(presentationDir(repoRoot, qid, spec), "logs");
}

/** `logsDir(...)`, created (recursively) if absent. Called once at run start so the folder
 *  exists before any stage writes a log into it. */
export function ensureLogsDir(repoRoot: string, qid: string, spec: string): string {
  const dir = logsDir(repoRoot, qid, spec);
  mkdirSync(dir, { recursive: true });
  return dir;
}
