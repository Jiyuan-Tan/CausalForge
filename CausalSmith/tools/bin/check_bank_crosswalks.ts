#!/usr/bin/env node
/**
 * C1 — banked-crosswalk anchor integrity lint.
 *
 * For every banked entry under `_bank/{accepted,downgraded}/` that
 * carries a tex↔Lean crosswalk (`*_crosswalk_full.json`, else `*_crosswalk.json`),
 * resolve each structured Lean anchor `{file, decl, line}` against the entry's
 * LIVE Lean source (`state.json.lean_subdir`) and report anchors that no longer
 * resolve: a renamed/removed decl (missing-decl), a decl that moved files
 * (moved-file), or a large line drift (line-drift, informational). `failed` /
 * `legacy` tiers are skipped (no derivation / pre-reviewer, no calibrated
 * crosswalk). This does NOT re-judge the math — only that prose still points at
 * a live decl.
 *
 * Usage:
 *   npx tsx tools/bin/check_bank_crosswalks.ts            # human-readable report
 *   npx tsx tools/bin/check_bank_crosswalks.ts --json     # machine-readable JSON
 *   npx tsx tools/bin/check_bank_crosswalks.ts --strict   # exit 1 on any broken anchor
 *
 * Exit code: 0 (report-only) unless `--strict`, where any missing-decl /
 * moved-file / unresolvable-lean-dir yields exit 1 (line-drift never fails).
 */
import { existsSync, readFileSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import type { CrosswalkEntry } from "../src/types.js";
import {
  buildLiveDeclIndex,
  crosswalkAnchorIntegrity,
  type AnchorIntegrityFinding,
} from "../src/formalization/bank_crosswalk_lint.js";

const TIERS = ["accepted", "downgraded"] as const;

function findCausalSmithRoot(start: string): string {
  let cur = path.resolve(start);
  for (;;) {
    const lakefile = path.join(cur, "lakefile.toml");
    if (existsSync(lakefile)) {
      try {
        if (/^\s*name\s*=\s*"CausalSmith"/m.test(readFileSync(lakefile, "utf8"))) return cur;
      } catch {
        /* fall through */
      }
    }
    const parent = path.dirname(cur);
    if (parent === cur) throw new Error(`Could not locate CausalSmith package root from ${start}`);
    cur = parent;
  }
}

interface EntryReport {
  tier: string;
  entry: string; // <qid>_<spec> dir name
  leanSubdir: string | null;
  leanDirResolved: boolean;
  crosswalkFile: string; // basename of the linted crosswalk
  findings: AnchorIntegrityFinding[];
  error?: string; // why the entry could not be linted (no state / no lean_subdir / no dir)
}

async function firstFileEndingWith(dir: string, suffixes: string[]): Promise<string | null> {
  const names = await readdir(dir).catch(() => [] as string[]);
  for (const suffix of suffixes) {
    const hit = names.find((n) => n.endsWith(suffix));
    if (hit) return path.join(dir, hit);
  }
  return null;
}

async function lintEntry(csRoot: string, tier: string, entryDir: string): Promise<EntryReport | null> {
  const cwFile = await firstFileEndingWith(entryDir, ["_crosswalk_full.json", "_crosswalk.json"]);
  if (!cwFile) return null; // no crosswalk → nothing to lint for this entry
  const base: EntryReport = {
    tier,
    entry: path.basename(entryDir),
    leanSubdir: null,
    leanDirResolved: false,
    crosswalkFile: path.basename(cwFile),
    findings: [],
  };
  const stateFile = await firstFileEndingWith(entryDir, ["_state.json"]);
  if (!stateFile) return { ...base, error: "no state.json (cannot locate live Lean dir)" };
  let leanSubdir: string | null = null;
  try {
    leanSubdir = JSON.parse(await readFile(stateFile, "utf8")).lean_subdir ?? null;
  } catch {
    return { ...base, error: "state.json unreadable" };
  }
  if (!leanSubdir) return { ...base, leanSubdir: null, error: "state.json has no lean_subdir" };
  const leanDir = path.join(csRoot, leanSubdir);
  if (!existsSync(leanDir))
    return { ...base, leanSubdir, error: `live Lean dir missing: ${leanSubdir}` };
  let entries: CrosswalkEntry[];
  try {
    entries = JSON.parse(await readFile(cwFile, "utf8"));
  } catch {
    return { ...base, leanSubdir, leanDirResolved: true, error: "crosswalk JSON unreadable" };
  }
  const live = await buildLiveDeclIndex(leanDir);
  return {
    ...base,
    leanSubdir,
    leanDirResolved: true,
    findings: crosswalkAnchorIntegrity(entries, live),
  };
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  const asJson = argv.includes("--json");
  const strict = argv.includes("--strict");
  const verbose = argv.includes("--verbose");
  const csRoot = findCausalSmithRoot(process.cwd());
  const bankRoot = path.join(csRoot, "doc/research/_bank");

  const reports: EntryReport[] = [];
  for (const tier of TIERS) {
    const tierDir = path.join(bankRoot, tier);
    const dirs = await readdir(tierDir, { withFileTypes: true }).catch(() => []);
    for (const d of dirs) {
      if (!d.isDirectory()) continue;
      const r = await lintEntry(csRoot, tier, path.join(tierDir, d.name));
      if (r) reports.push(r);
    }
  }

  const broken = (f: AnchorIntegrityFinding) =>
    f.severity === "missing-decl" || f.severity === "moved-file";
  const hardFailures = reports.filter(
    (r) => r.error?.startsWith("live Lean dir missing") || r.findings.some(broken),
  );

  if (asJson) {
    console.log(JSON.stringify(reports, null, 2));
  } else {
    console.log(`Banked-crosswalk anchor integrity — ${reports.length} entr(ies) with a crosswalk\n`);
    for (const r of reports) {
      const head = `[${r.tier}] ${r.entry}  (${r.crosswalkFile})`;
      if (r.error) {
        console.log(`${head}\n  ⚠ ${r.error}`);
        continue;
      }
      // Line-drift is never actionable (line numbers are re-derivable) and never
      // fails — keep the default report scannable by collapsing it to a count.
      const shown = verbose ? r.findings : r.findings.filter((f) => f.severity !== "line-drift");
      const drifts = r.findings.length - shown.length;
      if (shown.length === 0) {
        const tail = drifts > 0 ? ` (${drifts} line-drift — see --json/--verbose)` : "";
        console.log(`${head}\n  ✓ all anchors resolve${tail}`);
        continue;
      }
      console.log(head);
      for (const f of shown) {
        const mark = f.severity === "line-drift" ? "·" : "✗";
        console.log(`  ${mark} ${f.severity} ${f.obj_id} [${f.verdict}] ${f.recordedFile}:${f.decl} — ${f.note}`);
      }
      if (drifts > 0) console.log(`  · (${drifts} line-drift collapsed — see --json/--verbose)`);
    }
    const counts = { "missing-decl": 0, "moved-file": 0, "line-drift": 0 };
    for (const r of reports) for (const f of r.findings) counts[f.severity]++;
    console.log(
      `\nTotals: ${counts["missing-decl"]} missing-decl, ${counts["moved-file"]} moved-file, ${counts["line-drift"]} line-drift.`,
    );
  }

  if (strict && hardFailures.length > 0) process.exit(1);
}

main().catch((err) => {
  console.error(err);
  process.exit(2);
});
