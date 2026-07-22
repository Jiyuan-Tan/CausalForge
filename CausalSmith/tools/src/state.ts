import { mkdir, readdir, readFile, rename, writeFile } from "node:fs/promises";
import { randomUUID } from "node:crypto";
import path from "node:path";
import { z } from "zod";
import { STAGE_ORDER } from "./constants.js";
import {
  allowedLeanSubdirs,
  canonicalLeanSubdir,
  formalizationKindRoot,
  statePath,
} from "./paths.js";
import type { StateJson } from "./types.js";
import { UPGRADE_AXES, UPGRADE_PARENT_TIERS } from "./types.js";
import { normalizeNoveltyTarget } from "./novelty.js";

const stageSchema = z.enum(STAGE_ORDER);

/**
 * Legacy stage labels accepted on read for backward compatibility. The Stage -1
 * → -1.2 rename (with a new Stage -1.1 inserted before it) made any state file
 * written by an older pipeline carry `stage_completed: "-1"`; the retired F3.7
 * slot made some carry `"3.7"`. Normalize on load so in-flight runs can resume
 * after upgrade without manual editing. New states always use the new labels.
 */
const LEGACY_STAGE_REMAP: Record<string, (typeof STAGE_ORDER)[number]> = {
  "-1": "-1.2",
  // An old F3.7 completion was immediately followed by F4. Map it to its
  // predecessor so `nextStage` resumes at F4 after the retired slot disappears.
  "3.7": "3.5",
};

/**
 * Legacy-aware stage schema: remaps old stage strings to new ones, then parses
 * the result as a valid stage. Used in both top-level and per-theorem entries.
 */
const legacyAwareStageSchema = z
  .union([stageSchema, z.string()])
  .transform((value) => {
    if (typeof value === "string" && value in LEGACY_STAGE_REMAP) {
      return LEGACY_STAGE_REMAP[value as keyof typeof LEGACY_STAGE_REMAP];
    }
    return stageSchema.parse(value);
  });

const gapsSchema = z
  .object({
    gaps_path: z.string(),
    n_open_problems: z.number().int().nonnegative(),
    status: z.enum(["completed", "needs-pivot"]),
  })
  .passthrough();

const pendingSorrySchema = z.object({
  file: z.string(),
  line: z.number().int().nonnegative(),
  label: z.string().optional(),
  goal: z.string().optional(),
  suggestions: z.array(z.string()).optional(),
  // Per-sorry convergence memory (Stage 3); all optional + backward compatible.
  track: z.union([z.enum(["1", "2", "3", "4", "5"]), z.null()]).optional(),
  attempts: z.number().int().nonnegative().optional(),
  last_goal_hash: z.union([z.string(), z.null()]).optional(),
  escalations: z.number().int().nonnegative().optional(),
  bursted: z.boolean().optional(),
}).passthrough();

/** One cited node's F2.5/F4 source-match verdict, persisted so `bankEntry` can enforce it. */
const citedCheckSchema = z.object({
  name: z.string(),
  check_status: z.string(),
  cite_id: z.string().optional(),
  locator: z.string().optional(),
  reviewer: z.enum(["codex", "claude"]).optional(),
});

const citedReviewReceiptSchema = z.object({
  node_id: z.string().min(1),
  reviewer: z.enum(["codex", "claude"]),
  check_status: z.string().min(1),
  cite_id: z.string().min(1),
  locator: z.string().min(1),
  evidence_hash: z.string().min(1),
});

const deliveryReviewReceiptSchema = z.object({
  node_id: z.string().min(1),
  reviewer: z.enum(["codex", "claude"]),
  verdict: z.enum(["matched", "drift"]),
  evidence_hash: z.string().min(1),
  note: z.string().optional(),
});

const addedAssumptionSchema = z.object({
  label: z.string(),
  statement: z.string(),
  user_approved: z.boolean().optional(),
  source: z.string().optional(),
  anchor: z.string().optional(),
  classification: z
    .enum(["faithful-refinement", "regularity-bookkeeping", "substrate-gate"])
    .optional(),
  reviewed: z.boolean().optional(),
}).passthrough();

const missingItemSchema = z.object({
  kind: z.string(),
  name_suggestion: z.string(),
  purpose: z.string(),
  why_substantial: z.string(),
  nl_artifact_reference: z.string().optional(),
  suggested_location: z.string().optional(),
}).passthrough();

const loopSchema = z.enum(["research", "study"]);
const lineageSchema = z
  .object({
    parent_run_id: z.string().optional(),
    parent_kind: loopSchema.optional(),
  })
  .passthrough();

const theoremEntrySchema = z.object({
  theorem_local_id: z.string(),
  origin_theorem_id: z.string(),
  statement: z.string(),
  proof_sketch: z.string().nullable(),
  status: z.enum(["pending", "in_progress", "completed", "stuck", "failed"]),
  stage_completed: legacyAwareStageSchema.nullable(),
  lean_file_relpath: z.string().nullable(),
  failure_reason: z.string().optional(),
  lean_decl_name: z.string().optional(),
  bt_id: z.string().optional(),
  /**
   * Set by `mintFailedTheoremOpenQuestion` at bank time on `status: "failed"`
   * entries. Points to the OpenQuestion node minted at
   * `doc/study/nodes/open_question/<minted_oq_id>.json`.
   */
  minted_oq_id: z.string().optional(),
}).passthrough();

export const stateSchema = z
  .object({
    stage_completed: legacyAwareStageSchema,
    lean_subdir: z.string(),
    // Self-identifying run coordinates. Historically the qid/spec lived ONLY in
    // the path (folder = qid, filename = `<qid>_<spec>_state.json`). After the
    // causalsmith-style rename the state file is the bare `state.json`, so the
    // spec is no longer recoverable from the filename; it is stamped here on
    // every save and read back by `findActiveStates`. Optional for back-compat
    // with pre-rename state files (whose spec is still in their filename).
    qid: z.string().optional(),
    specialization: z.string().optional(),
    pending_sorries: z.array(pendingSorrySchema).default([]),
    design_decisions: z.record(z.string()).default({}),
    added_assumptions: z.array(addedAssumptionSchema).default([]),
    /**
     * Durable record of the F4 reviewer's CITED source-match verdicts, one per cited node.
     *
     * The `cited-mismatch` / `cited-underspecified` verdicts HARD-BLOCK banking, but the verdict
     * used to live only in the reviewer's in-memory return value: the block was enforced solely
     * inside the proof–review loop, so `bank_entry.ts --tier accepted` (and any resume re-entering
     * at F5) banked a mismatched cited def silently. Persisting it lets `bankEntry` enforce the
     * documented guarantee at the actual irreversible moment.
     */
    cited_checks: z.array(citedCheckSchema).default([]),
    cited_review_receipts: z.array(citedReviewReceiptSchema).default([]),
    delivery_review_receipts: z.array(deliveryReviewReceiptSchema).default([]),
    // Phase 2 additions; all optional + backward compatible.
    loop: loopSchema.default("research"),
    // `--auto`: persisted autonomy flag (see SharedState.auto_mode).
    auto_mode: z.boolean().default(false),
    next_action: z.union([z.string(), z.null()]).default(null),
    lineage: z.union([lineageSchema, z.null()]).default(null),
    // Phase 3 additions; all optional + backward compatible.
    from_question_oq_id: z.union([z.string(), z.null()]).default(null),
    method_id: z.union([z.string(), z.null()]).default(null),
    closed_oq: z
      .union([
        z
          .object({ oq_id: z.string(), bt_id: z.string() })
          .passthrough(),
        z.null(),
      ])
      .default(null),
    gaps: gapsSchema.optional(),
    flags: z.object({
      rewound_from_stage0: z.string().nullable().optional(),
      rewound_from_stage4d: z.string().nullable().optional(),
      rewound_from_stage0_5_pivot: z.string().nullable().optional(),
      stage_neg1_fallback: z.string().nullable().optional(),
      local_fix_from_4d: z.boolean().default(false),
      missing_architecture: z.boolean().default(false),
      missing_architecture_items: z.array(missingItemSchema).optional(),
      theorem_splits: z.number().int().nonnegative().optional(),
      scaffold_redirect: z.string().nullable().optional(),
      scaffold_redirect_count: z.number().int().nonnegative().optional(),
      scaffold_redirect_cap_hit: z.string().optional(),
      // Proof-review loop iteration budgets — persisted so a `--resume` cannot silently
      // hand the loop a fresh budget (see types.ts).
      proof_loop_counters: z
        .object({
          iters: z.number().int().nonnegative().default(0),
          scaffold_rounds: z.number().int().nonnegative().default(0),
          stale: z.number().int().nonnegative().default(0),
          tag_reroutes: z.number().int().nonnegative().default(0),
          node_strikes: z.record(z.string(), z.number().int().nonnegative()).default({}),
          review_error_strikes: z.record(z.string(), z.number().int().nonnegative()).default({}),
          // Hash of the last red `lake build` diagnostic. Persisted so the identically-red
          // no-progress cap survives a `--resume` — an in-process comparand reset `stale` to 0
          // on every re-entry, refunding the circuit breaker a fresh budget each time.
          last_build_error_sig: z.string().default(""),
        })
        .optional(),
      proof_loop_cap_hit: z.string().optional(),
      // D-phase loop budgets. These were in-process `for`-loop bounds, so every plain
      // `--resume` silently granted a FRESH 15 solve rounds / 3 D0.5 rounds — the same
      // unbounded re-sampling this file's proof_loop_counters were introduced to stop
      // for the F stages. `consistency_heals` moves here from `design_decisions` so a
      // cap gate can reset it (a CapGate's `clear` only receives `flags`); a legacy run
      // wedged on the old design_decisions value is unwedged by that migration, which is
      // the desired outcome.
      d0_loop_counters: z
        .object({
          solve_rounds: z.number().int().nonnegative().default(0),
          revise_rounds: z.number().int().nonnegative().default(0),
          consistency_heals: z.number().int().nonnegative().default(0),
        })
        .optional(),
      d0_loop_cap_hit: z.string().optional(),
      neg1_env_failure_retries: z.number().int().nonnegative().optional(),
      proof_review_escalation_pending: z
        .object({
          route: z.string(),
          reason: z.string(),
        })
        .nullable()
        .default(null),
      // D0.5.G cold-referee below-floor-not-salvageable halt reason.
      general_review_halt: z.string().nullable().optional(),
      // Build-first substrate seam (F1.5→F2): set by F1 on needs-new-infrastructure;
      // blocks --resume until the orchestrator builds the crux substrate + reruns F1.
      substrate_build_required: z.string().nullable().optional(),
      // Substrate-built channel (build→F1): orchestrator records the freshly-built
      // 0-sorry Causalean decl(s) here; F1 reads it as a discharge directive for the
      // matching gate node(s) and the gate is cleared once consumed.
      substrate_built: z
        .array(
          z.object({
            gate_id: z.string(),
            decl_name: z.string(),
            module: z.string(),
            nl_statement: z.string(),
          }),
        )
        .nullable()
        .optional(),
      // D0.5.G directed-reroute counter (below-floor but bounded-fix salvageable →
      // re-run D0 with the directive); capped so a stuck topic still halts.
      general_reroute_count: z.number().int().nonnegative().optional(),
      // D0.R loop: operator injection (cleared after use), flagship-upside counter,
      // and best-note-by-tier tracking (deliverable = best, not last).
      d0r_human_directive: z.string().nullable().optional(),
      d0r_flagship_rounds: z.number().int().nonnegative().optional(),
      d0r_best_tier: z.string().nullable().optional(),
      d0r_best_note_path: z.string().nullable().optional(),
      // F3 phase-B proof-fill directive (build→resume): a load-bearing PROOF hint the
      // orchestrator injects for the filler (lemma names / tactic strategy / Mathlib API)
      // when the fill loop is stuck. Loop-wide + persistent — injected into every filler
      // call for the rest of phase B until the orchestrator clears it. Mirrors the D0
      // escalation-log directive channel; NOT a license to change statements/hypotheses
      // (the per-iteration anti-laundering + assumption/def gates still apply).
      f3_filler_directive: z.string().nullable().optional(),
      // Persistent orchestrator SCAFFOLD directive for F2 (analogue of `f3_filler_directive`):
      // read by `runStage2` on every scaffold/revise pass and injected verbatim as a
      // top-priority faithfulness constraint. Unlike `scaffold_redirect` (one-shot, capped,
      // self-clearing, review-loop-driven) this PERSISTS across resumes until the orchestrator
      // clears it (via `bin/f2_directive.ts`). A faithfulness/statement-shape steer only — the
      // F2.5 review + anti-laundering gates still apply.
      f2_scaffold_directive: z.string().nullable().optional(),
      // Statement-correction rewind (over-precise headline → standard true form).
      statement_correction_directive: z.string().nullable().optional(),
      source_rewind: z
        .object({
          status: z.string(),
          command_ts: z.string().optional(),
          target: z.string().optional(),
          subtype: z.string().optional(),
          reentry_stage: z.string().optional(),
          reentry_mode: z.string().optional(),
          dirty_nodes: z.array(z.string()).default([]),
          review_scope: z.string().optional(),
          f2_revised_at: z.string().optional(),
        })
        .optional(),
      stage0_too_many_conjectures: z.string().optional(),
      stage0_stitch_invariant_violated: z.string().optional(),
    }).passthrough(),
    proposed_from: z
      .object({
        topic: z.string(),
        // Canonical vocabulary is the tier ladder (incremental|subfield|field|flagship).
        // The two legacy spellings are still accepted on load and normalized to the
        // tier names, so pre-unification banked runs remain resumable.
        novelty_target: z
          .enum([
            "incremental",
            "subfield",
            "field",
            "flagship",
            "relative-to-repo",
            "relative-to-literature",
          ])
          .transform((v) => normalizeNoveltyTarget(v)!),
        pivot_budget_used: z.number().int().nonnegative(),
        // Nullable so manual state edits can clear the verdict between
        // resume attempts (e.g. operator wants to re-run D0 without
        // re-running D-0.5 on the same proposal). Live writers only emit
        // "pending" / "ACCEPT" / "NO-PASS".
        final_verdict: z.string().nullable(),
        proposal_path: z.string(),
        novelty_justification: z.string(),
        chosen_qid: z.string(),
        chosen_specialization: z.string(),
        // Without this the proposer-emitted cluster was silently STRIPPED on
        // every state reload (zod objects drop unknown keys).
        cluster: z.enum(["panel", "exactid", "partialid", "stat", "experimentation", "scm"]).optional(),
        seed_list: z.array(z.string()).optional(),
        current_angle_index: z.number().int().nonnegative().optional(),
        current_version: z.number().int().nonnegative().optional(),
        current_mode: z
          .enum(["cold-start", "revise", "pivot", "kernel-replace", "draft-rebuild"])
          .optional(),
        revision_cap_by_angle: z.record(z.string(), z.number().int().positive()).optional(),
        angle_checkpoint: z
          .object({
            kind: z.enum(["revise", "angle-boundary"]),
            angle: z.number().int().nonnegative(),
            version: z.number().int().nonnegative(),
            verdict: z.string(),
            reason: z.string(),
            revise_cap: z.number().int().positive(),
            next_angle: z.number().int().nonnegative().optional(),
          })
          .optional(),
        last_draft_handoff: z.string().optional(),
        last_draft_status: z
          .enum(["completed", "needs-pivot", "invalid-draft", "env-failure"])
          .optional(),
        exhausted_angles: z.array(z.number().int().nonnegative()).optional(),
        last_reviewer_verdict: z.string().optional(),
        iterations: z
          .array(
            z.object({
              angle: z.number().int().nonnegative(),
              // Nonnegative (not positive) so a `version: 0` pre-draft pivot
              // marker — emitted historically when pivoting to a new angle
              // before the first draft existed — loads on resume. Live writers
              // emit version >= 1 for real drafts; the v0 marker is harmless.
              version: z.number().int().nonnegative(),
              mode: z.string(),
              verdict: z.string(),
              tier: z.string().optional(),
              clean_substance: z.boolean().optional(),
            }),
          )
          .optional(),
        archived_proposals: z.array(z.string()).optional(),
        upgrade_from: z
          .object({
            parent_qid: z.string(),
            parent_spec: z.string(),
            parent_tier: z.enum(UPGRADE_PARENT_TIERS),
            upgrade_axis: z.enum(UPGRADE_AXES),
          })
          .optional(),
      })
      .passthrough()
      .optional(),
    theorems: z.array(theoremEntrySchema).optional(),
    current_theorem_index: z.number().int().min(0).optional(),
  })
  .passthrough()
  .transform((raw) => {
    const copy = { ...raw } as Record<string, unknown>;
    delete copy.ckpt_pending;
    if (copy.flags && typeof copy.flags === "object") {
      delete (copy.flags as Record<string, unknown>).bucket_a_blocked;
    }
    return copy as unknown as StateJson;
  });

export function createInitialState(qid: string): StateJson {
  return {
    stage_completed: "-1.2",
    lean_subdir: canonicalLeanSubdir(qid),
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    cited_checks: [],
    delivery_review_receipts: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: {
      rewound_from_stage0: null,
      rewound_from_stage4d: null,
      local_fix_from_4d: false,
      missing_architecture: false,
      scaffold_redirect: null,
      f2_scaffold_directive: null,
      scaffold_redirect_count: 0,
      d0_loop_counters: { solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 },
      proof_review_escalation_pending: null,
    },
  };
}

export function assertLeanSubdirInvariant(qid: string, state: StateJson): void {
  const allowed = allowedLeanSubdirs(qid);
  const normalized = state.lean_subdir.split(path.sep).join(path.posix.sep);
  if (!allowed.includes(normalized)) {
    const expectedDesc = allowed.length === 1 ? allowed[0] : `one of {${allowed.join(", ")}}`;
    throw new Error(
      `qid/lean_subdir invariant failed: expected ${expectedDesc}, found ${state.lean_subdir}`,
    );
  }
}

export async function loadState(
  repoRoot: string,
  qid: string,
  specialization: string,
): Promise<StateJson> {
  const file = statePath(repoRoot, qid, specialization);
  const parsed = stateSchema.parse(JSON.parse(await readFile(file, "utf8")));
  assertLeanSubdirInvariant(qid, parsed);
  return parsed;
}

export async function saveState(
  repoRoot: string,
  qid: string,
  specialization: string,
  state: StateJson,
): Promise<void> {
  assertLeanSubdirInvariant(qid, state);
  // Stamp self-identifying coordinates so the bare `state.json` filename (which
  // no longer encodes the spec) stays resumable — `findActiveStates` reads them.
  state.qid = qid;
  state.specialization = specialization;
  const file = statePath(repoRoot, qid, specialization);
  await mkdir(path.dirname(file), { recursive: true });
  // Atomic write (temp + rename, same pattern as the graph writers): state is
  // saved many times mid-stage, and a crash during a bare writeFile truncates
  // the state file and makes the run unresumable without hand surgery.
  // Unique temp name (pid + uuid, like saveGraph): a pipeline save racing a
  // concurrent bin-tool save on one FIXED `.tmp` could rename a half-written
  // interleaving into place.
  const tmp = `${file}.${process.pid}.${randomUUID()}.tmp`;
  await writeFile(tmp, `${JSON.stringify(state, null, 2)}\n`, "utf8");
  await rename(tmp, file);
}

export interface ActiveState {
  qid: string;
  specialization: string;
  path: string;
  state: StateJson;
}

export async function findActiveStates(repoRoot: string): Promise<ActiveState[]> {
  const active: ActiveState[] = [];

  for (const kind of ["research", "study"] as const) {
    const kindRoot = formalizationKindRoot(repoRoot, kind);
    const entries = await readdir(kindRoot, { withFileTypes: true }).catch(() => []);
    for (const entry of entries) {
      if (!entry.isDirectory()) continue;
      const qid = entry.name;
      const dir = path.join(kindRoot, qid); // why: scan each kind root directly; qid heuristics can map study-looking runs to research/.
      const files = await readdir(dir, { withFileTypes: true }).catch(() => []);
      for (const file of files) {
        if (!file.isFile()) continue;
        // Bare `state.json` (causalsmith-style) or legacy `<qid>_<spec>_state.json`.
        const isBare = file.name === "state.json";
        const isLegacy = file.name.endsWith("_state.json") && file.name.startsWith(`${qid}_`);
        if (!isBare && !isLegacy) continue;
        const fullPath = path.join(dir, file.name);
        // One corrupt/legacy state file must not brick the scan for the whole
        // kind — skip it loudly and keep enumerating.
        try {
          const parsed = stateSchema.parse(JSON.parse(await readFile(fullPath, "utf8")));
          assertLeanSubdirInvariant(qid, parsed);
          // Spec: prefer the stamped field; fall back to the legacy filename.
          const specialization =
            parsed.specialization ??
            (isLegacy ? file.name.slice(qid.length + 1, -"_state.json".length) : "");
          if (!specialization) continue;
          if (parsed.stage_completed !== "5") {
            active.push({ qid, specialization, path: fullPath, state: parsed });
          }
        } catch (err) {
          console.warn(
            `[state] skipping unparseable state file ${fullPath}: ${err instanceof Error ? err.message : String(err)}`,
          );
        }
      }
    }
  }

  return active;
}
