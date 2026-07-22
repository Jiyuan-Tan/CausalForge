// One-off migration: rename causalsmith research per-run artifacts from the legacy
// `<qid>_<spec>_<rest>` / `<qid>_<rest>` prefixed names to the bare
// papersmith-style names (`state.json`, `pipeline.jsonl`, `writeup.tex`, …),
// and stamp `qid`/`specialization` into each renamed `state.json` so the bare
// filename stays resumable. Recurses into live structural subfolders
// (discovery/, formalization/, logs/) but SKIPS frozen backup/snapshot dirs
// (names starting with `_` or containing `backup`/`bak`).
//
//   node scripts/migrate_qid_filenames.mjs          # preview (dry-run)
//   node scripts/migrate_qid_filenames.mjs --apply  # execute
import { readdirSync, renameSync, statSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";

const APPLY = process.argv.includes("--apply");
const REPO = path.resolve(import.meta.dirname, "..", "..");
const research = (p) => path.join(REPO, "doc", "research", p);
const study = (p) => path.join(REPO, "doc", "study", "runs", p);

// Each run folder with its (qid, spec). qid drives the prefix; spec the longer prefix.
const RUNS = [
  { dir: research("active/pid_cascade_escalation_rd"), qid: "pid_cascade_escalation_rd", spec: "postselect_honest" },
  { dir: research("active/pid_manski1990test"), qid: "pid_manski1990test", spec: "default" },
  { dir: research("active/pid_poc_tau_band"), qid: "pid_poc_tau_band", spec: "concordance_sharp_dr" },
  { dir: research("active/stat_ate_overlap_decay"), qid: "stat_ate_overlap_decay", spec: "v1" },
  { dir: study("smoke_dry_codex_check"), qid: "smoke_dry_codex_check", spec: "v1" },
  { dir: research("_bank/accepted/stat_policy_regret_margin_overlap_v1"), qid: "stat_policy_regret_margin_overlap", spec: "v1" },
];

const skipDir = (name) => name.startsWith("_") || /backup|bak/i.test(name);

/** Map a legacy basename to its bare form, or null to leave it unchanged. */
function bareName(b, qid, spec) {
  if (b === `${qid}_${spec}.tex`) return "writeup.tex";
  if (b === `${qid}_${spec}.md`) return "formalization.md";
  if (b.startsWith(`${qid}_${spec}_`)) return b.slice(`${qid}_${spec}_`.length);
  if (b.startsWith(`${qid}_`)) return b.slice(`${qid}_`.length);
  return null;
}

let renamed = 0, stamped = 0, skipped = 0;

function walk(dir, qid, spec) {
  let entries;
  try { entries = readdirSync(dir, { withFileTypes: true }); } catch { return; }
  for (const e of entries) {
    const full = path.join(dir, e.name);
    if (e.isDirectory()) {
      if (skipDir(e.name)) continue;
      walk(full, qid, spec);
      continue;
    }
    if (!e.isFile()) continue;
    const bare = bareName(e.name, qid, spec);
    if (!bare || bare === e.name) continue;
    const target = path.join(dir, bare);
    try { statSync(target); console.log(`  SKIP (target exists): ${e.name} -> ${bare}`); skipped++; continue; } catch { /* ok */ }
    console.log(`  ${e.name} -> ${bare}`);
    if (APPLY) renameSync(full, target);
    renamed++;
    // Stamp coordinates into the renamed canonical state file.
    if (bare === "state.json" || bare === "state.archived.json") {
      if (APPLY) {
        try {
          const j = JSON.parse(readFileSync(target, "utf8"));
          j.qid = qid; j.specialization = spec;
          writeFileSync(target, JSON.stringify(j, null, 2) + "\n", "utf8");
          stamped++;
        } catch (err) { console.log(`    (stamp failed: ${err.message})`); }
      } else stamped++;
    }
  }
}

for (const r of RUNS) {
  console.log(`\n=== ${path.relative(REPO, r.dir)}  (qid=${r.qid} spec=${r.spec}) ===`);
  walk(r.dir, r.qid, r.spec);
}
console.log(`\n${APPLY ? "APPLIED" : "DRY-RUN"}: ${renamed} rename(s), ${stamped} state file(s) stamped, ${skipped} skipped.`);
