// C1 — banked-crosswalk anchor integrity. The bank crosswalks
// (`<qid>_crosswalk_full.json`) are a per-result tex↔Lean map: each row carries a
// structured Lean anchor `{file, decl, line}` and a verdict. Unlike the library
// explorer's review badges, these anchors are FROZEN at bank time and never
// re-validated, so a decl that is later renamed / moved / deleted leaves the
// crosswalk asserting `verdict: equivalent` against a Lean object that no longer
// exists — silent rot. This lint resolves every anchored row against the live
// Lean source and reports the broken ones. It does NOT re-adjudicate the math
// (that is C2, the statement-hash + codex re-review): it only checks that the
// prose still POINTS AT a live decl. Companion to crosswalk.ts's self-consistency
// checks (`crosswalkVerifiedWithoutAnchor`, `anchorDriftFindings`), which compare
// a crosswalk to itself / to a fresh rescan; this one compares it to live source.

import { existsSync } from "node:fs";
import type { CrosswalkEntry, CrosswalkVerdict } from "../types.js";
import { parseAllDecls } from "./crosswalk.js";

/** missing-decl: anchor's decl name absent from live source (renamed/removed) —
 *  the anchor is broken. moved-file: decl still exists but in a different file
 *  basename than recorded — anchor file stale. line-drift: same file, line moved
 *  beyond tolerance — informational (lines shift on every edit). */
export type AnchorIntegritySeverity = "missing-decl" | "moved-file" | "line-drift";

export interface AnchorIntegrityFinding {
  obj_id: string;
  decl: string;
  verdict: CrosswalkVerdict;
  recordedFile: string;
  recordedLine: number;
  severity: AnchorIntegritySeverity;
  liveFile?: string; // where the decl actually lives now (moved-file / line-drift)
  liveLine?: number;
  note: string;
}

/** Where a decl name occurs in live source: file path relative to the Lean dir,
 *  plus the 1-indexed header line. */
export interface LiveDeclOccurrence {
  file: string;
  line: number;
}

/** decl name → occurrences in the live Lean directory. */
export type LiveDeclIndex = Map<string, LiveDeclOccurrence[]>;

const basename = (f: string): string => f.split(/[\\/]/).pop() ?? f;

/**
 * Pure integrity check: every crosswalk row with a structured Lean anchor must
 * still resolve to a live decl of that name, in the recorded file basename,
 * within the line tolerance. Rows with `lean: null` are skipped — they are
 * intentionally unanchored (the lean:null + verified-verdict contradiction is a
 * separate self-consistency check, `crosswalkVerifiedWithoutAnchor`). A passing
 * anchor produces no finding. `lineTolerance` defaults to 50: large because line
 * numbers churn on every edit, so we treat them as a soft hint, not a gate — the
 * load-bearing checks are decl existence (missing-decl) and file (moved-file).
 */
export function crosswalkAnchorIntegrity(
  entries: CrosswalkEntry[],
  live: LiveDeclIndex,
  opts: { lineTolerance?: number } = {},
): AnchorIntegrityFinding[] {
  const tol = opts.lineTolerance ?? 50;
  const out: AnchorIntegrityFinding[] = [];
  for (const e of entries) {
    if (!e.lean) continue;
    const { file, decl, line } = e.lean;
    const base = {
      obj_id: e.obj_id,
      decl,
      verdict: e.verdict,
      recordedFile: file,
      recordedLine: line,
    };
    const cands = live.get(decl) ?? [];
    if (cands.length === 0) {
      out.push({
        ...base,
        severity: "missing-decl",
        note: `decl \`${decl}\` no longer exists in live Lean source (renamed or removed)`,
      });
      continue;
    }
    const sameFile = cands.find((c) => basename(c.file) === basename(file));
    if (!sameFile) {
      const c = cands[0];
      out.push({
        ...base,
        severity: "moved-file",
        liveFile: c.file,
        liveLine: c.line,
        note: `decl \`${decl}\` moved from ${basename(file)} to ${c.file}`,
      });
      continue;
    }
    if (Math.abs(sameFile.line - line) > tol) {
      out.push({
        ...base,
        severity: "line-drift",
        liveFile: sameFile.file,
        liveLine: sameFile.line,
        note: `line drifted ${line} → ${sameFile.line} (anchor file unchanged)`,
      });
    }
  }
  return out;
}

/** Scan a live Lean directory into a decl-name → occurrences index for the
 *  integrity check. Indexes EVERY top-level decl (not just obj_id-bearing ones)
 *  so anchors pointing at helper defs (e.g. AUX- rows) also resolve. */
export async function buildLiveDeclIndex(leanDir: string): Promise<LiveDeclIndex> {
  const idx: LiveDeclIndex = new Map();
  if (!existsSync(leanDir)) return idx;
  for (const d of await parseAllDecls(leanDir)) {
    if (!d.name) continue;
    const arr = idx.get(d.name);
    if (arr) arr.push({ file: d.file, line: d.line });
    else idx.set(d.name, [{ file: d.file, line: d.line }]);
  }
  return idx;
}
