#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: disclose an assumption you added during a MANUAL de-laundering /
 * hand-intervention into `state.added_assumptions` (and optionally a `design_decisions`
 * note) — WITHOUT hand-editing `state.json`. Hand-editing this array is the classic
 * footgun: a shape mismatch fails the next `--resume` at Zod validation. This CLI loads,
 * appends a schema-valid entry, and saves, so F4 scrutinizes the disclosure and the state
 * stays valid.
 *
 * Each entry needs a `label` + `statement`; `--classification` marks it
 * faithful-refinement / regularity-bookkeeping / substrate-gate (F4 reads this). Appending
 * with an existing `label` REPLACES that entry (idempotent re-disclosure).
 *
 * Usage:
 *   npx tsx tools/bin/add_assumption.ts <qid> <spec> \
 *     --label "<short id>" --statement "<the assumption, as stated in the Lean>" \
 *     [--classification faithful-refinement|regularity-bookkeeping] \
 *     [--source "<where it comes from>"] [--decision "<key>=<design decision note>"]
 *   npx tsx tools/bin/add_assumption.ts <qid> <spec> --label L --statement -   # stdin
 *   npx tsx tools/bin/add_assumption.ts <qid> <spec> --show                    # list current
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { loadState, saveState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";

/** Values this CLI will WRITE. `substrate-gate` is deliberately absent — see the refusal in `main`. */
const ACCEPTED_CLASSIFICATIONS = ["faithful-refinement", "regularity-bookkeeping"] as const;
/** Values recognized on input. `substrate-gate` is recognized only so it earns the routing error
 *  below rather than a generic "must be one of" — never so it can be written. */
const CLASSIFICATIONS = ["faithful-refinement", "regularity-bookkeeping", "substrate-gate"] as const;
type Classification = (typeof CLASSIFICATIONS)[number];



async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  const show = args.includes("--show");
  const label = cli.value("--label");
  let statement = cli.value("--statement");
  const classification = cli.value("--classification");
  const source = cli.value("--source");
  const decision = cli.value("--decision");
  const positional = args.filter((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  const [qid, spec] = positional;

  if (!qid || !spec || (!show && (!label || statement === undefined))) {
    console.error(
      'Usage: add_assumption.ts <qid> <spec> --label "<id>" --statement "<stmt>" ' +
        `[--classification ${ACCEPTED_CLASSIFICATIONS.join("|")}] [--source "<x>"] [--decision "<key>=<note>"] | --show`,
    );
    process.exitCode = 1;
    return;
  }
  if (classification && !CLASSIFICATIONS.includes(classification as Classification)) {
    console.error(`--classification must be one of: ${CLASSIFICATIONS.join(", ")}`);
    process.exitCode = 1;
    return;
  }
  // ONE WRITER PER CONCEPT. This CLI only DISCLOSES (it writes `state.added_assumptions`). A
  // substrate-gate additionally needs REGISTRATION in plan.json + graph.json, or the hypothesis is
  // dropped by the next F2 re-scaffold and `bankEntry` refuses tier `accepted`. `gate.ts` writes
  // all three stores atomically, disclosure included — so route the caller there rather than
  // letting them create a disclosure with no gate behind it.
  if (classification === "substrate-gate") {
    console.error(
      `add_assumption.ts DISCLOSES only — it cannot register a substrate-gate.\n` +
        `A disclosed-but-unregistered gate is dropped by the next F2 re-scaffold (silent sorry), ` +
        `and bankEntry refuses tier 'accepted' while one exists.\n\n` +
        `Use gate.ts instead — it writes plan.json + graph.json + state.added_assumptions + ` +
        `SUBSTRATE_DEBT.md atomically:\n` +
        `  npx tsx tools/bin/gate.ts ${qid} ${spec} <node_id> --consumers <id1,id2> ` +
        `[--class gated|cited] [--reason "<why it is genuine debt>"]\n\n` +
        `(<node_id> is the graph node for the assumed fact; run with --show to inspect.)`,
    );
    process.exitCode = 1;
    return;
  }

  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);

  if (show) {
    console.log(JSON.stringify(state.added_assumptions ?? [], null, 2));
    return;
  }

  if (statement === "-") statement = readFileSync(0, "utf8").trim();
  const stmt = (statement ?? "").trim();
  if (stmt.length === 0) {
    console.error("Refusing to add an assumption with an empty statement.");
    process.exitCode = 1;
    return;
  }

  const entry = {
    label: label!,
    statement: stmt,
    ...(classification ? { classification: classification as Classification } : {}),
    ...(source ? { source } : {}),
  };
  const existing = state.added_assumptions ?? [];
  const idx = existing.findIndex((a) => a.label === label);
  if (idx !== -1) existing[idx] = { ...existing[idx], ...entry };
  else existing.push(entry);
  state.added_assumptions = existing;

  if (decision) {
    const eq = decision.indexOf("=");
    if (eq <= 0) {
      console.error('--decision expects "<key>=<note>".');
      process.exitCode = 1;
      return;
    }
    state.design_decisions = { ...(state.design_decisions ?? {}), [decision.slice(0, eq).trim()]: decision.slice(eq + 1).trim() };
  }

  await saveState(repoRoot, qid, spec, state);
  console.log(
    `${idx !== -1 ? "Updated" : "Added"} assumption '${label}' for ${qid} / ${spec} ` +
      `(${state.added_assumptions.length} total). F4 will scrutinize it on the next --stop-after F4.`,
  );
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
