#!/usr/bin/env -S npx tsx
/**
 * Manual backfill for paper-scoped study-mode BankedTheorem minting.
 *
 * Usage:
 *   npx tsx tools/bin/mint_paper_bts.ts <qid> <spec>
 *
 * Reads retired study-run `doc/study/runs/<qid>/<qid>_<spec>_state.json`, uses its
 * `theorems[]` + `context.from_insight_id`, and calls
 * `mintPaperScopedBankedTheoremsNoOq` to write one BankedTheorem per completed
 * entry under `doc/study/nodes/banked_theorem/<qid>_<local>_<spec>.json`.
 *
 * Idempotent: pre-existing BT files are reused. Use this only to backfill runs
 * that completed Stage 5 BEFORE the no-OQ close hook landed; for new runs the
 * in-pipeline hook handles minting automatically.
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { readFile, writeFile, rename } from "node:fs/promises";
import { mintPaperScopedBankedTheoremsNoOq } from "../src/shared/close_open_question.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


async function main(): Promise<void> {
  const [qid, spec] = process.argv.slice(2);
  if (!qid || !spec) {
    console.error("Usage: mint_paper_bts.ts <qid> <spec>");
    process.exit(2);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const statePath = path.join(
    repoRoot,
    "doc",
    "study",
    "runs",
    qid,
    `${qid}_${spec}_state.json`,
  );
  if (!existsSync(statePath)) {
    console.error(`State file not found: ${statePath}`);
    process.exit(2);
  }
  const state = JSON.parse(await readFile(statePath, "utf8")) as {
    context?: { from_insight_id?: unknown };
    theorems?: Array<{
      theorem_local_id: string;
      lean_decl_name?: string;
      statement: string;
      status: "pending" | "in_progress" | "completed" | "stuck" | "failed";
    }>;
    method_id?: string | null;
  };
  const insightId = state.context?.from_insight_id;
  if (typeof insightId !== "string") {
    console.error(
      `state.context.from_insight_id is not a string in ${statePath}; cannot infer parent Insight.`,
    );
    process.exit(2);
  }
  const paperTheorems = (state.theorems ?? []).map((t) => ({
    local_id: t.theorem_local_id,
    lean_decl_name: t.lean_decl_name,
    statement: t.statement,
    status: t.status,
  }));
  const graphRoot = path.join(repoRoot, "doc", "study");
  const r = await mintPaperScopedBankedTheoremsNoOq(
    {
      qid,
      spec,
      derived_from_insight_id: insightId,
      bankMetadata: {
        instantiates: state.method_id ? [state.method_id] : [],
        uses: [],
      },
      theorems: paperTheorems,
    },
    { graphRoot },
  );
  console.log(`minted ${r.bt_ids.length} BankedTheorem(s):`);
  for (const id of r.bt_ids) console.log(`  ${id}`);

  // Stamp bt_id back into state.theorems[k] for each completed entry so that
  // study-pipeline S5 can locate the BankedTheorem via the DispatchRecord shape.
  let stamped = 0;
  for (const t of state.theorems ?? []) {
    if (t.status === "completed") {
      const derivedBtId = `${qid}_${t.theorem_local_id}_${spec}`;
      if (r.bt_ids.includes(derivedBtId)) {
        (t as { bt_id?: string }).bt_id = derivedBtId;
        stamped++;
      }
    }
  }
  if (stamped > 0) {
    const tmp = `${statePath}.new`;
    await writeFile(tmp, JSON.stringify(state, null, 2) + "\n", "utf8");
    await rename(tmp, statePath);
    console.log(`stamped bt_id on ${stamped} state.theorems entry/entries (${statePath})`);
  }
}

main().catch((err: unknown) => {
  const msg = err instanceof Error ? err.message : String(err);
  console.error(`mint_paper_bts failed: ${msg}`);
  process.exit(1);
});
