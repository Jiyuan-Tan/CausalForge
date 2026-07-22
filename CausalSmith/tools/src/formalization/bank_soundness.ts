// F5 bank-soundness gate: text-based (no LSP) scan of a banked artifact subdir plus
// its reachable CausalSmith/Mathlib closure for real `sorry` tokens and cheat tokens.
// Extracted from the retired stage3.ts (F3) so the kept F5 bank keeps its mechanical
// soundness check. Pure scanning — no Lean elaboration.

import { readFileSync } from "node:fs";
import path from "node:path";
import { stripLeanComments } from "../graph/extractor.js";
import { listLeanFiles } from "../pipeline_support.js";

/**
 * Comment-aware "does this file contain a REAL (uncommented) `sorry` token?".
 * NEVER false-negatives a genuine `sorry`; a false positive is merely a wasted check, not a
 * correctness loss. Uses the char-accurate `stripLeanComments` (nesting-, string- and
 * char-literal-aware) — the previous line-granular scanner skipped an ENTIRE line that merely
 * STARTED inside a block comment, so code after a mid-line `-/` close escaped the scan.
 */
export function textHasRealSorry(text: string): boolean {
  return /\bsorry\b/.test(stripLeanComments(text));
}

/** repoRoot-relative (forward-slash) form of a path. */
function relOf(file: string, repoRoot: string): string {
  const r = path.isAbsolute(file) ? path.relative(repoRoot, file) : file;
  return r.split(path.sep).join("/");
}

/** Artifact files plus the transitive closure of the `CausalSmith.Mathlib.*` files they import. */
function reachableFileClosure(researchFiles: string[], repoRoot: string): string[] {
  const seen = new Set<string>();
  const all: string[] = [];
  const queue = [...researchFiles];
  while (queue.length) {
    const f = queue.shift()!;
    const abs = path.isAbsolute(f) ? f : path.join(repoRoot, f);
    if (seen.has(abs)) continue;
    seen.add(abs);
    all.push(abs);
    let src: string;
    try {
      src = readFileSync(abs, "utf8");
    } catch {
      continue;
    }
    for (const m of src.matchAll(/^\s*import\s+(\S+)/gm)) {
      if (/^CausalSmith\.Mathlib\./.test(m[1])) {
        queue.push(path.join(repoRoot, m[1].split(".").join("/") + ".lean"));
      }
    }
  }
  return all;
}

/** Scan the artifact + its reachable closure for cheat tokens (axiom/opaque/native_decide/unsafe/admit/sorry). */
async function scanCheatTokens(
  researchFiles: string[],
  repoRoot: string,
): Promise<Array<{ file: string; line: number; token: string }>> {
  const all = reachableFileClosure(researchFiles, repoRoot);
  // Reject admitted proof tokens here too, so closure banking cannot launder them as non-cheats.
  const TOKEN = /\b(axiom|opaque|native_decide|unsafe|admit|sorry)\b/;
  const found: Array<{ file: string; line: number; token: string }> = [];
  for (const abs of all) {
    let text: string;
    try {
      text = readFileSync(abs, "utf8");
    } catch {
      continue;
    }
    // stripLeanComments preserves newlines, so line numbers stay accurate; unlike the old
    // line-granular scan it also sees code AFTER a mid-line block-comment close.
    const lines = stripLeanComments(text).split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const m = TOKEN.exec(lines[i]);
      if (m) found.push({ file: relOf(abs, repoRoot), line: i + 1, token: m[1] });
    }
  }
  return found;
}

/**
 * F5 bank-soundness gate: scan the artifact subdir plus its reachable
 * CausalSmith/Mathlib closure for real `sorry` tokens and cheat tokens. Returns
 * human-readable issue strings; empty = bankable.
 */
export async function bankSoundnessIssues(leanDir: string, repoRoot: string): Promise<string[]> {
  const research = await listLeanFiles(leanDir);
  const issues: string[] = [];
  for (const abs of reachableFileClosure(research, repoRoot)) {
    try {
      if (textHasRealSorry(readFileSync(abs, "utf8"))) {
        issues.push(`sorry in ${relOf(abs, repoRoot)}`);
      }
    } catch {
      issues.push(`unreadable file ${relOf(abs, repoRoot)}`);
    }
  }
  for (const c of await scanCheatTokens(research, repoRoot)) {
    issues.push(`${c.token} in ${c.file}:${c.line}`);
  }
  return issues;
}
