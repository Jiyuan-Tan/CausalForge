// Throwaway: build a post-D-1.1 state for the D-stage dual-producer test.
// Rewinds the banked overlap-ate run to the moment right after D-1.1 (gaps mined,
// proposed_from seeded with topic+novelty, current_mode=cold-start v0) so a
// `--resume --stop-after D-0.5` exercises the new D-1.2 dual author + D-0.5 core
// reviewer from scratch. Writes via the real saveState so the state schema is
// validated. Run with cwd = CausalSmith package root.
import { readFile } from "node:fs/promises";
import path from "node:path";
import { createInitialState, saveState } from "../src/state.js";
import { gapsJsonPath } from "../src/paths.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";
const repoRoot = path.resolve(process.cwd()); // CausalSmith package root

// Pull topic / novelty / literature_map from the banked downgraded run so the
// rewound proposed_from carries the same anchor (literature_map = cold-start
// gaps fallback; load-bearing context).
const downgraded = JSON.parse(
  await readFile(
    path.join(
      repoRoot,
      "doc/research/_bank/downgraded/stat_ate_overlap_decay_v1/stat_ate_overlap_decay_v1_state.json",
    ),
    "utf8",
  ),
) as Record<string, any>;
const pf = downgraded.proposed_from ?? {};

const gapsPath = gapsJsonPath(repoRoot, QID, SPEC);
const gapsJson = JSON.parse(await readFile(gapsPath, "utf8")) as Record<string, any>;
const nOpen =
  typeof gapsJson.n_open_problems === "number"
    ? gapsJson.n_open_problems
    : Array.isArray(gapsJson.open_problems)
      ? gapsJson.open_problems.length
      : 0;

const state = createInitialState(QID);
state.stage_completed = "-1.1";
state.gaps = { gaps_path: gapsPath, n_open_problems: nOpen, status: "completed" };
state.proposed_from = {
  topic: pf.topic,
  novelty_target: pf.novelty_target ?? "subfield",
  pivot_budget_used: 0,
  final_verdict: "pending",
  proposal_path: "",
  novelty_justification: "",
  chosen_qid: QID,
  chosen_specialization: SPEC,
  seed_list: [],
  current_angle_index: 0,
  current_version: 0,
  current_mode: "cold-start",
  exhausted_angles: [],
  iterations: [],
  archived_proposals: [],
  ...(typeof pf.literature_map === "string" ? { literature_map: pf.literature_map } : {}),
  ...(pf.cluster ? { cluster: pf.cluster } : {}),
};

await saveState(repoRoot, QID, SPEC, state);
console.log(`wrote post-D-1.1 state: stage_completed=${state.stage_completed}`);
console.log(`  gaps_path=${gapsPath} (n_open_problems=${nOpen})`);
console.log(`  topic=${String(pf.topic).slice(0, 80)}...`);
console.log(`  novelty_target=${state.proposed_from.novelty_target} mode=cold-start v0`);
