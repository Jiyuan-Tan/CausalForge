#!/usr/bin/env node
/**
 * D0.R prototype — directed coordinated whole-note re-derivation (single agent,
 * ledger memory). Tests the architecture we converged on: ONE agent holds the
 * whole note + a structured ledger (summarized memory, not full history), and
 * produces a COORDINATED revision executing a reviewer directive — no per-conjecture
 * fan-out, no stitch.
 *
 * Standalone (does NOT mutate run state). One codex call (gpt-5.5/xhigh, no Lean).
 * Reads the current note + setup + a seed/round ledger, writes the revised note +
 * updated ledger + raw output to <outDir>.
 *
 * Usage:
 *   npx tsx bin/d0r_directed_solve.ts <qid> <spec> \
 *       [--ledger <path>] [--directive <path|->] [--out <dir>] [--round <n>]
 *   (--directive - reads the directive from stdin; default = the baked-in round-1
 *    upper+lower directive for the stat_policy pilot)
 */
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { artifactPaths, baseBrief, readPrompt } from "../src/pipeline_support.js";
import { runCodex } from "../src/workers/codex.js";
import { loadState } from "../src/state.js";
import { MODEL_PLAN } from "../src/constants.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

const DEFAULT_DIRECTIVE = [
  "DIRECTIVE (round 1): Close the gap between the full-class upper bound (currently",
  "r_up = 9/16 at alpha=gamma=2, from GLOBAL uniform clipping + an ASSUMED drift) and a",
  "full-class converse. Concretely:",
  "(a) UPPER, sharpen: replace the global uniform clip with a LOCAL/ADAPTIVE or STRATIFIED",
  "    truncation that integrates the overlap-decay tail (clip harder where overlap is thin),",
  "    and recompute the empirical-process exponent for the FULL class P_{alpha,gamma}, aiming",
  "    to lift r_emp from 9/16 toward r = (1+alpha)/(2+alpha+delta). Account for EVERY region's",
  "    variance contribution; do not drop the moderate-overlap term.",
  "(b) UPPER, derive the crux: DERIVE the clipped-score drift Delta_n = o(n^{-r_up}) from the",
  "    primitive L2 nuisance product-remainder rate (ass:nuisance) + cross-fitting + the",
  "    overlap-decay geometry, and REMOVE it from the hypotheses. Do not re-assume it.",
  "(c) MATCH: if the upper bound improves, build a matching FULL-class lower bound (weak-overlap",
  "    witness FAMILY over a non-degenerate region of P_{alpha,gamma}, free weak-arm height beta",
  "    optimized subject to the overlap-decay membership constraint) — NOT the calibrated subclass.",
  "    If a residual exact-rate gap remains, state it as an OEQ at the SAME (field) ambition.",
  "Keep BOTH bounds present and coordinated. Derive, do not assume. Flag any genuine OPEN gap",
  "explicitly in the note and ledger rather than laundering it.",
].join("\n");


function argVal(flag: string): string | undefined {
  const i = process.argv.indexOf(flag);
  return i >= 0 ? process.argv[i + 1] : undefined;
}

function extractBlock(stdout: string, name: string): string | null {
  const re = new RegExp(`<<<${name}\\s*([\\s\\S]*?)\\s*${name}>>>`);
  const m = stdout.match(re);
  return m ? m[1].trim() : null;
}

async function main() {
  const [qid, spec] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
  if (!qid || !spec) {
    console.error("Usage: d0r_directed_solve.ts <qid> <spec> [--ledger p] [--directive p|-] [--out d] [--round n]");
    process.exit(1);
  }
  const round = Number.parseInt(argVal("--round") ?? "1", 10) || 1;
  const outDir = argVal("--out") ?? "/tmp/d0r_pilot";
  await mkdir(outDir, { recursive: true });

  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const ctx = {
    repoRoot,
    qid,
    specialization: spec,
    dryRun: false,
    resume: true,
    noveltyTarget: "field" as const,
  };
  const paths = artifactPaths(ctx, state);
  const runDir = path.dirname(paths.tex);

  // --note overrides the input note (default: the run's canonical .tex). Each round
  // reads the PRIOR round's note, so the loop carries forward the coordinated note.
  const note = await readFile(argVal("--note") ?? paths.tex, "utf8");
  const setupPath = path.join(runDir, `${qid}_setup.json`);
  const setup = existsSync(setupPath) ? await readFile(setupPath, "utf8") : "(no setup.json found)";

  const ledgerPath = argVal("--ledger") ?? path.join(outDir, "seed_ledger.json");
  const ledger = await readFile(ledgerPath, "utf8");

  const directiveArg = argVal("--directive");
  let directive = DEFAULT_DIRECTIVE;
  if (directiveArg) {
    const raw = directiveArg === "-" ? readFileSync(0, "utf8") : await readFile(directiveArg, "utf8");
    // why: an operator-supplied directive may carry consult-capture artifacts; the
    // built-in DEFAULT_DIRECTIVE is authored text and needs no check.
    const cleaned = sanitizeDirectiveForCli(raw, process.argv.includes("--allow-dirty-capture"));
    if (cleaned === null) {
      process.exitCode = 1;
      return;
    }
    directive = cleaned;
  }

  const prompt = [
    await readPrompt(ctx, "stage0_common.txt"),
    "",
    await readPrompt(ctx, "stage0_setup_stat.txt"),
    "",
    await readPrompt(ctx, "stage0_R_directed.txt"),
    "",
    baseBrief(ctx, state),
    "",
    `=== SETUP (setup.json) ===\n${setup}`,
    "",
    `=== LEDGER (your memory across rounds) ===\n${ledger}`,
    "",
    `=== THE DIRECTIVE (round ${round}) ===\n${directive}`,
    "",
    `=== THE WHOLE NOTE (current; rewrite coherently) ===\n${note}`,
    "",
    "RETURN exactly the two fenced blocks <<<NOTE ... NOTE>>> and <<<LEDGER ... LEDGER>>>, nothing else.",
  ].join("\n");

  const plan = MODEL_PLAN.stage0_solve; // kernel/xhigh tier (was the redundant stage0_k alias)
  console.error(`[D0.R round ${round}] ${qid} ${spec} · ${plan.model}/${plan.effort} · dispatching directed solve…`);
  const t0 = process.hrtime.bigint();
  const out = await runCodex({
    prompt,
    cwd: repoRoot,
    model: plan.model,
    reasoningEffort: plan.effort,
    leanLsp: false,
    inactivityTimeoutMs: 50 * 60 * 1000,
  });
  const mins = Number(process.hrtime.bigint() - t0) / 1e9 / 60;

  const rawFile = path.join(outDir, `round${round}_raw.txt`);
  await writeFile(rawFile, out.stdout, "utf8");

  const newNote = extractBlock(out.stdout, "NOTE");
  const newLedger = extractBlock(out.stdout, "LEDGER");
  if (newNote) await writeFile(path.join(outDir, `round${round}_note.tex`), newNote + "\n", "utf8");
  if (newLedger) await writeFile(path.join(outDir, `round${round}_ledger.json`), newLedger + "\n", "utf8");

  console.log(`\n===== D0.R round ${round} done (${mins.toFixed(1)} min) =====`);
  console.log(`raw:    ${rawFile}`);
  console.log(`note:   ${newNote ? path.join(outDir, `round${round}_note.tex`) + ` (${newNote.length} chars)` : "MISSING — check raw"}`);
  console.log(`ledger: ${newLedger ? path.join(outDir, `round${round}_ledger.json`) : "MISSING — check raw"}`);
  if (newLedger) {
    try {
      const l = JSON.parse(newLedger);
      console.log(`\nround_summary: ${l.round_summary ?? "(none)"}`);
      for (const c of l.conjectures ?? []) console.log(`  [${c.status}] ${c.label}: ${c.key_gap ?? c.current_result ?? ""}`.slice(0, 200));
      for (const a of l.assumptions_live ?? []) console.log(`  assumption ${a.name}: ${a.status}`);
    } catch {
      console.log("(ledger did not parse as JSON — inspect the file)");
    }
  }
}

main().catch((err) => {
  console.error(err instanceof Error ? err.stack ?? err.message : String(err));
  process.exit(1);
});
