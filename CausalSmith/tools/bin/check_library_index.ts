import { writeFileSync, existsSync, mkdirSync } from "node:fs";
import { join, resolve } from "node:path";
import { execSync } from "node:child_process";
import { loadLibrary, declArea, isTier1, reviewStatus } from "../src/library/schema.js";

/**
 * Standalone integrity + coverage check for the library explorer index.
 * Usage: npx tsx bin/check_library_index.ts [--root <causaleanRoot>] [--seed]
 *   --seed creates empty sidecar files for areas that lack one.
 * Exit 1 on integrity errors (loadLibrary throws); coverage gaps are warnings
 * (printed table, exit 0).
 */

const args = process.argv.slice(2);
const rootIdx = args.indexOf("--root");
const root =
  rootIdx >= 0 ? resolve(args[rootIdx + 1]) : resolve(import.meta.dirname, "..", "..", "..");
const seed = args.includes("--seed");

const lib = loadLibrary(root); // throws (exit 1) on integrity problems

const STALE_MODULES = new Set([
  "Causalean.Estimation.ATT.AIPWScoreL2",
  "Causalean.Estimation.ATT.ATTInstance",
  "Causalean.Estimation.ATT.DML",
  "Causalean.Estimation.ATT.Remainder",
  "Causalean.Estimation.ATT.RemainderBound",
  "Causalean.SCM.Do.Rule2Kernel.Structural.StructCrossSCM",
  "Causalean.SCM.Do.Rule2Kernel.Structural.StructPointwise",
]);

// Orphan check: every Causalean/*.lean file must be reachable from the root
// import graph (= present in the index's modules map), or the explorer
// silently misses its declarations (the PolyTail incident, 2026-06-11).
// Deliberately archived modules are exempt.
{
  const { readdirSync } = await import("node:fs");
  const walk = (dir: string): string[] =>
    readdirSync(join(root, dir), { withFileTypes: true }).flatMap((d) =>
      d.isDirectory() ? walk(`${dir}/${d.name}`) : d.name.endsWith(".lean") ? [`${dir}/${d.name}`] : [],
    );
  const onDisk = walk("Causalean").map((f) => f.slice(0, -5).replace(/\//g, "."));
  const indexed = new Set(Object.keys(lib.modules));
  const orphans = onDisk.filter(
    (m) =>
      !indexed.has(m) &&
      !m.includes(".Archived.") &&
      // stale work-in-progress modules that no longer compile against the
      // Mathlib pin (tracked in SUBSTRATE_DEBT.md; fix or archive to clear)
      !STALE_MODULES.has(m),
  );
  if (orphans.length > 0) {
    console.error(
      `ORPHANED MODULES (${orphans.length}) — on disk but unreachable from the Causalean root import graph; add imports to Causalean.lean and regenerate:\n  ` +
        orphans.join("\n  "),
    );
    process.exit(1);
  }
}

// Alias-lexicon liveness: every module prefix in the causal alias lexicon
// (src/formalization/causal_aliases.ts, the scaffold-retrieval synonym bridge) must
// point at a real area of the index, or the retrieval module-fallback sends agents to
// a directory that no longer exists. Catches alias-path rot at the same cadence as
// index drift (this check runs on every Causalean change).
{
  const { CAUSAL_ALIASES } = await import("../src/formalization/causal_aliases.js");
  const files = lib.entries.map((e) => e.file);
  const prefixes = new Set<string>();
  for (const e of CAUSAL_ALIASES) for (const m of e.modules) prefixes.add(m);
  const dead = [...prefixes].filter((p) => {
    const rr = p.replace(/\/+$/, "");
    return !files.some((f) => f === rr || f === rr + ".lean" || f.startsWith(rr + "/"));
  });
  if (dead.length > 0) {
    console.error(
      `DEAD ALIAS MODULE PREFIXES (${dead.length}) — listed in causal_aliases.ts but matching no indexed file; fix the path or remove it:\n  ` +
        dead.sort().join("\n  "),
    );
    process.exit(1);
  }
}

const areas = new Map<
  string,
  { tier1: number; documented: number; reviewed: number; stale: number; sorried: number }
>();
for (const e of lib.entries) {
  const a = declArea(e);
  const s = areas.get(a) ?? { tier1: 0, documented: 0, reviewed: 0, stale: 0, sorried: 0 };
  if (isTier1(e, lib.sidecars)) {
    s.tier1++;
    if (e.doc && e.doc.trim().length > 0) s.documented++;
    const st = reviewStatus(e, lib.sidecars);
    if (st === "reviewed") s.reviewed++;
    if (st === "stale") s.stale++;
  }
  if (e.usesSorry) s.sorried++;
  areas.set(a, s);
}

if (seed) {
  const dir = join(root, "doc", "library_review");
  mkdirSync(dir, { recursive: true });
  for (const a of areas.keys()) {
    const f = join(dir, `${a}.json`);
    if (!existsSync(f)) {
      writeFileSync(
        f,
        JSON.stringify({ headline_theorems: [], reviews: [], flags: [] }, null, 2) + "\n",
      );
      console.log(`seeded ${f}`);
    }
  }
}

const head = execSync("git rev-parse HEAD", { cwd: root }).toString().trim();
if (head !== lib.commit) {
  console.warn(
    `WARN index commit ${lib.commit.slice(0, 7)} != HEAD ${head.slice(0, 7)} — rerun \`lake exe library_index\``,
  );
}
console.log("area               tier1  documented  reviewed  stale  sorried");
for (const [a, s] of [...areas.entries()].sort()) {
  console.log(
    `${a.padEnd(18)} ${String(s.tier1).padStart(5)}  ${String(s.documented).padStart(10)}  ${String(s.reviewed).padStart(8)}  ${String(s.stale).padStart(5)}  ${String(s.sorried).padStart(7)}`,
  );
}
