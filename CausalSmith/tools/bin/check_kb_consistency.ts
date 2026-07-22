#!/usr/bin/env node
/**
 * C3 — knowledge-base consistency lint (mechanical, no LLM).
 *
 *   C3  API.md ↔ source: every `## N. \`path\`` section header in `doc/API.md`
 *       (Causalean) and `CausalSmith/doc/API.md` must reference a file/dir that
 *       still exists on disk (brace groups expanded; only the section's first
 *       backtick path is checked).
 *
 * Usage:
 *   npx tsx tools/bin/check_kb_consistency.ts            # human-readable report
 *   npx tsx tools/bin/check_kb_consistency.ts --json     # machine-readable JSON
 *   npx tsx tools/bin/check_kb_consistency.ts --strict   # exit 1 on any finding
 *
 * Exit code: 0 (report-only) unless `--strict`, where any C3 finding yields exit 1.
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import {
  extractApiMdPathRefs,
  apiMdMissingPaths,
  type ApiMdFinding,
} from "../src/formalization/api_md_lint.js";

/** The workspace root holds both `Causalean/` and `CausalSmith/` subdirs. */
function findWorkspaceRoot(start: string): string {
  let cur = path.resolve(start);
  for (;;) {
    if (existsSync(path.join(cur, "Causalean")) && existsSync(path.join(cur, "CausalSmith"))) return cur;
    const parent = path.dirname(cur);
    if (parent === cur) throw new Error(`Could not locate workspace root (Causalean+CausalSmith) from ${start}`);
    cur = parent;
  }
}

async function runC3(repoRoot: string): Promise<{ label: string; findings: ApiMdFinding[] }[]> {
  const csRoot = path.join(repoRoot, "CausalSmith");
  const targets = [
    { label: "Causalean doc/API.md", api: path.join(repoRoot, "doc/API.md"), root: path.join(repoRoot, "Causalean") },
    { label: "CausalSmith doc/API.md", api: path.join(csRoot, "doc/API.md"), root: csRoot },
  ];
  const out: { label: string; findings: ApiMdFinding[] }[] = [];
  for (const t of targets) {
    if (!existsSync(t.api)) {
      out.push({ label: t.label, findings: [] });
      continue;
    }
    const refs = extractApiMdPathRefs(await readFile(t.api, "utf8"));
    // Tokens are normally relative to the file's source root, but a few headers
    // write a path workspace-relative (e.g. `Causalean/Panel/Weighted/`,
    // `archive/Theorems/…`). Accept either rooting so a path that genuinely
    // exists is never flagged on a convention slip; only a path absent under
    // BOTH is rot.
    const findings = apiMdMissingPaths(
      refs,
      (target) => existsSync(path.join(t.root, target)) || existsSync(path.join(repoRoot, target)),
    );
    out.push({ label: t.label, findings });
  }
  return out;
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  const asJson = argv.includes("--json");
  const strict = argv.includes("--strict");
  const repoRoot = findWorkspaceRoot(process.cwd());

  const c3 = await runC3(repoRoot);
  const total = c3.reduce((n, t) => n + t.findings.length, 0);

  if (asJson) {
    console.log(JSON.stringify({ c3 }, null, 2));
  } else {
    console.log("=== C3 — API.md ↔ source file paths ===");
    for (const t of c3) {
      if (t.findings.length === 0) {
        console.log(`  ✓ ${t.label}: all documented paths exist`);
        continue;
      }
      console.log(`  ${t.label}:`);
      for (const f of t.findings) console.log(`    ✗ L${f.line} ${f.token} — ${f.note}`);
    }
    console.log(`\nTotal findings: ${total}.`);
  }

  if (strict && total > 0) process.exit(1);
}

main().catch((err) => {
  console.error(err);
  process.exit(2);
});
