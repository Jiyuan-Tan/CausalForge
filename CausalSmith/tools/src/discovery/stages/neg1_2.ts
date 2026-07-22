// Discovery Stage -1.2 (proposal producer) + Stage -1 helpers.
// Extracted from pipeline_stages.ts in Step 2.2 of the three-submodules refactor.

import path from "node:path";
import { mkdir, readFile, rename, writeFile, copyFile, access } from "node:fs/promises";
import { formalizationDir, resolveInDir, templatePath } from "../../paths.js";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import { appendReviewLog, type ReviewLogEntry } from "../../log.js";
import {
  artifactPaths,
  ensureSkeleton,
  readPrompt,
  type StageDeps,
} from "../../pipeline_support.js";
import { buildGapsContextBlock } from "./neg1_1.js";
import { buildStage0_5RejectionContext } from "./neg0_5.js";
import { runStageNeg1_2ProtoCore } from "./neg1_2_author.js";
import { formatNeg1EscalationContext, readNeg1EscalationLog } from "../stageNeg1_directive.js";
import { laterStageEverRan } from "../../shared/resume_mode.js";

export const NEG1_PIVOT_BUDGET = (() => {
  const v = parseInt(process.env.CAUSALSMITH_NEG1_PIVOT_BUDGET ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 5;
})();
export const NEG1_REVISE_CAP = (() => {
  const v = parseInt(process.env.CAUSALSMITH_NEG1_REVISE_CAP ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 5;
})();
// Tier-gated early-stop: if an angle has not reached `tier=flagship` by this
// version (counting any iteration in the angle's history), the orchestrator
// kills the angle instead of polishing it up to NEG1_REVISE_CAP. Designed to
// stop spending polish budget on structurally below-flagship angles while
// preserving the full revise budget for angles that already demonstrated
// flagship potential and just need substance fixes.
export const NEG1_NONFLAGSHIP_KILL_VERSION = (() => {
  const v = parseInt(process.env.CAUSALSMITH_NEG1_NONFLAGSHIP_KILL_VERSION ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 3;
})();
// How many times the orchestrator re-attempts the SAME draft after an
// environment failure (codex sandbox could not start) before aborting the run.
// An env failure is not a judgment about the angle, so it must NOT pivot; we
// retry a couple of times to ride out a transient hiccup, then abort WITHOUT
// pivot so the angle is preserved for `--resume` once the sandbox is repaired.
export const NEG1_ENV_FAILURE_RETRY_BUDGET = (() => {
  const v = parseInt(process.env.CAUSALSMITH_NEG1_ENV_FAILURE_RETRY_BUDGET ?? "", 10);
  return Number.isFinite(v) && v >= 0 ? v : 2;
})();

// Signatures of a producer/reviewer that failed to START its local execution
// (sandbox / FS) — as opposed to a genuine mathematical `needs-pivot`. When the
// codex write sandbox cannot spawn, the agent still emits a well-formed JSON
// with `status: "needs-pivot"` and a `blocking_reason` naming the environment
// failure. Pivoting on that spuriously burns a healthy angle, so we detect it
// and route to a retry/abort path instead. Kept deliberately specific to
// sandbox/process-startup failures so a real pivot is never misclassified.
const ENV_FAILURE_SIGNATURES: RegExp[] = [
  /spawn setup refresh/i,
  /windows sandbox/i,
  /sandbox:\s*spawn/i,
  /(local )?(file[- ]access |execution )(tools?|backends?)\b[^.]*\b(failed|returned|could not (start|spawn))/i,
  /failed before process start/i,
  /could not (start|spawn) (the )?(sandbox|local|child )?process/i,
];

/**
 * True iff the text carries a sandbox/process-startup failure signature.
 */
function textSignalsEnvFailure(text: string): boolean {
  if (!text) return false;
  return ENV_FAILURE_SIGNATURES.some((re) => re.test(text));
}

/**
 * True iff a parsed producer handoff reports an ENVIRONMENT failure (the
 * sandbox / local execution backend could not start) rather than a genuine
 * mathematical `needs-pivot`. Scans the fields a producer uses to report a
 * pre-flight failure: `blocking_reason`, `error`, and the SC self-review lines.
 */
export function handoffSignalsEnvFailure(json: Record<string, unknown>): boolean {
  const texts: string[] = [];
  for (const key of ["blocking_reason", "error", "failure_reason"] as const) {
    if (typeof json[key] === "string") texts.push(json[key] as string);
  }
  if (Array.isArray(json.soundness_self_review)) {
    for (const s of json.soundness_self_review) if (typeof s === "string") texts.push(s);
  }
  return textSignalsEnvFailure(texts.join("\n"));
}

/**
 * Stage -1.2 producer: produce ONE proposal version, reading `current_mode` /
 * `current_angle_index` / `current_version` from `state.proposed_from`. The
 * orchestrator (Stage -0.5) decides what mode to ask for next; this handler
 * only drafts. State is mutated in place; on cold start `proposed_from` is
 * initialized here.
 */
export async function runStageNeg1_2(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // Cold-start requires --propose. Resumes after a programmatic rewind
  // (e.g. Stage 0.5 boundary routing back to "-1.2") use the topic stored on
  // state.proposed_from. Without this fallback, --resume short-circuits the
  // producer and the rewound proposal is never redrafted.
  const effectiveTopic = args.ctx.proposeTopic ?? args.state.proposed_from?.topic;
  if (!effectiveTopic) {
    return { stage: "-1.2", status: "skipped", message: "proposal stage skipped" };
  }
  const paths = artifactPaths(args.ctx, args.state);

  const continuingExistingProposal = !!args.state.proposed_from;
  let pf = args.state.proposed_from;
  if (!pf) {
    pf = {
      topic: effectiveTopic,
      novelty_target: args.ctx.noveltyTarget ?? "field",
      pivot_budget_used: 0,
      final_verdict: "pending",
      proposal_path: paths.proposalTex,
      novelty_justification: "",
      chosen_qid: args.ctx.qid,
      chosen_specialization: args.ctx.specialization,
      seed_list: [],
      current_angle_index: 0,
      current_version: 0,
      current_mode: "cold-start",
      exhausted_angles: [],
      iterations: [],
      archived_proposals: [],
      upgrade_from: args.ctx.upgradeFrom,
    };
    args.state.proposed_from = pf;
  }

  // Mode union widened May 2026 to admit the Stage -0.5 REJECT-escape
  // dispatcher's two new modes (kernel-replace, draft-rebuild). The proto-core
  // author (`runStageNeg1_2ProtoCore`) maps each mode to
  // `stage_neg1_2_proto_head_<mode>.txt`; behavior diverges across modes only
  // via that mode-specific head prompt.
  const requestedMode: "cold-start" | "revise" | "pivot" | "kernel-replace" | "draft-rebuild" =
    pf.current_mode ?? "cold-start";
  // An explicit rewind/resume must not cold-regenerate an accepted proposal
  // after its reviewer (or any later stage) already ran. Preserve deliberate
  // pivot/rebuild modes; only stale `cold-start` is promoted to `revise`.
  const mode = requestedMode === "cold-start" && continuingExistingProposal &&
      (pf.current_version ?? 0) > 0 &&
      await laterStageEverRan(args.ctx, args.state, "-1.2")
    ? "revise"
    : requestedMode;
  pf.current_mode = mode;
  const angleIndex = pf.current_angle_index ?? 0;
  const nextVersion = (pf.current_version ?? 0) + 1;

  if (mode === "cold-start" || mode === "pivot") {
    await ensureSkeleton({
      ctx: args.ctx,
      templateName: "stage_neg1_skeleton.tex",
      target: paths.proposalTex,
    });
  }

  // Refresh the per-qid output JSON template (mode/version/qid pre-filled,
  // mode-inapplicable fields stripped). Re-rendered every invocation so revise
  // / pivot iterations see the correct mode + version without manual edits.
  await renderProposalOutputTemplate({
    ctx: args.ctx,
    targetPath: paths.proposalOutputJson,
    mode,
    version: nextVersion,
    proposalTexPath: paths.proposalTex,
  });

  // Cold-start only: load the (tier-general) motif library + anti-pattern
  // reservoir. On revise/pivot the chosen seed inherits its `motif` +
  // `target_tier` labels from cold-start `seed_details` via
  // `state.proposed_from`, so the library does not need to be re-read.
  // Trims ~5K tokens off every revise/pivot call.
  const flagshipMotifsBlock =
    mode === "cold-start"
      ? await readPrompt(args.ctx, "stage_neg1_2_motif_library.txt")
      : "";

  let parentBlock = "";
  if (pf.upgrade_from) {
    const { loadParentEntry, renderUpgradeContextBlock } = await import("../../upgrade.js");
    const parent = await loadParentEntry(args.ctx.repoRoot, {
      parent_qid: pf.upgrade_from.parent_qid,
      parent_spec: pf.upgrade_from.parent_spec,
    });
    // Snap parent_tier to the resolved tier (CLI defaulted to "accepted").
    pf.upgrade_from = { ...pf.upgrade_from, parent_tier: parent.tier };
    if (parent.cluster) pf.cluster = parent.cluster;
    const directiveText = await readPrompt(args.ctx, "stage_neg1_2_draft_upgrade_directive.txt");
    parentBlock = renderUpgradeContextBlock({
      upgradeFrom: pf.upgrade_from,
      parent,
      directiveText,
      targetTier: args.ctx.noveltyTarget,
    });
  }

  // Stage 0.5 rejection context: load-bearing on resume after a rewound_from_stage0.
  // Surfaces the verbatim rewind reason, auto-granted Bucket A assumptions, and the
  // most recent Stage 0.5 reviewer JSON so the producer can revise/pivot the kernel
  // instead of patching only the local proof step.
  const stage0_5RejectionBlock = await buildStage0_5RejectionContext({
    ctx: args.ctx,
    state: args.state,
  });

  // Stage -1.1 gaps payload: read the open-problem substrate produced upstream
  // and inject it as a load-bearing prompt block. Seeds in the proposer's F1
  // step must anchor to one of these open problems (paper bibkey OR prior
  // proposal ref). The block is empty on revise/pivot resumes that lost the
  // gaps.json file but still carry state.gaps in JSON — the proposer falls
  // back to the literature_map cached on proposed_from.
  const gapsBlock = await buildGapsContextBlock({
    ctx: args.ctx,
    state: args.state,
    gapsPath: paths.gapsJson,
  });

  // Orchestrator directive channel (mirrors D0's escalation-log directive): a
  // standalone, cumulative steer injected via `bin/dneg1_directive.ts`. Read on
  // every mode (cold-start included, matching D0 applying on every round) so an
  // injected direction is never silently dropped.
  const directiveBlock = formatNeg1EscalationContext(await readNeg1EscalationLog(args.ctx));

  // Required-precondition guard (cold-start only). The proposer must never run
  // cold-start ideation without a literature substrate: the Stage -1.1 GAPS
  // CONTEXT block is the only source (the legacy inline Step 0a / Step 1a
  // fallbacks were removed). An empty block on cold-start means gaps.json was
  // written + advanced but is now missing/unreadable AND no cached
  // literature_map survives on proposed_from (e.g. a resume after the file was
  // lost). Halt loudly rather than let the proposer improvise a worse scan:
  // silent degradation masks the lost substrate and burns a proposer +
  // reviewer call on a thin draft. The operator re-runs Stage -1.1 or restores
  // gaps.json, then --resume. Revise / pivot are exempt — they patch / re-seed
  // from artifacts inherited via proposed_from and do not consume the block.
  if (mode === "cold-start" && gapsBlock.length === 0) {
    return {
      stage: "-1.2",
      status: "checkpoint",
      advance: false,
      message:
        "Stage -1.2 cold-start halted: STAGE -1.1 GAPS CONTEXT is empty " +
        `(gaps.json missing/unreadable at ${paths.gapsJson} and no cached literature_map). ` +
        "Re-run Stage -1.1 or restore gaps.json, then --resume.",
    };
  }

  // Single-artifact producer: ONE author emits the typed proposal core. Thread the
  // SHARED context into the author so it is
  // NOT context-starved: the D-1.1 gaps/literature substrate (load-bearing — the
  // kernel must anchor to a named open problem), the cold-start motif library, the
  // Stage-0.5 rejection context, and the upgrade-parent block. MODE-SPECIFIC inputs
  // (prior core to edit, seed list, prior reviewer verdict) are assembled inside
  // runStageNeg1_2ProtoCore from `mode` + state.
  const contextBlocks = [gapsBlock, flagshipMotifsBlock, stage0_5RejectionBlock, parentBlock, directiveBlock]
    .filter((b) => b && b.length > 0)
    .join("\n\n");
  return runStageNeg1_2Dual({
    ctx: args.ctx,
    state: args.state,
    deps: args.deps,
    mode,
    nextVersion,
    angleIndex,
    contextBlocks,
  });
}

/**
 * Single-artifact producer (rollout step 5): ONE author emits the typed proposal
 * core (formal + prose fields), and the proposal gate (G1–G7 + GP1/GP2/GP3) runs inside
 * the author. The author's
 * stdout handoff is harvested into `proposed_from` so the -0.5 reviewer handoff
 * (literature_checklist) and the pivot/revise reuse keep working. A gate failure
 * throws with the violation list — loud by design while the flag is being validated.
 * The -0.5 retarget (step 4) lights up automatically: it inlines the proposal core
 * once the file exists. `contextBlocks` carries the D-1.1 gaps / motif / flagship /
 * prior-review context the caller assembled, so the author is not context-starved.
 */
export async function runStageNeg1_2Dual(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  mode: "cold-start" | "revise" | "pivot" | "kernel-replace" | "draft-rebuild";
  nextVersion: number;
  angleIndex: number;
  contextBlocks?: string;
}): Promise<StageResult> {
  const pf = args.state.proposed_from;
  if (!pf) throw new Error("runStageNeg1_2Dual called without state.proposed_from");

  // ONE author: head(mode)+body → typed core → proposal gate → schema-validate.
  const authored = await runStageNeg1_2ProtoCore({
    ctx: args.ctx,
    state: args.state,
    deps: args.deps,
    mode: args.mode,
    contextBlocks: args.contextBlocks,
  });
  const handoff = authored.handoff;

  // Harvest ideation metadata even when the author returns needs-pivot. A
  // cold-start author can legitimately reject the initially requested kernel
  // while still writing the ranked seed slate that the pivot modes require.
  // Persisting those seeds before the early return prevents artificial
  // empty-seed pivot exhaustion.
  const ideationStateMissing = !Array.isArray(pf.seed_list) || pf.seed_list.length === 0;
  if (args.mode === "cold-start" || ideationStateMissing) {
    if (Array.isArray(handoff.seeds)) {
      pf.seed_list = (handoff.seeds as unknown[]).filter((s): s is string => typeof s === "string");
    }
    if (Array.isArray(handoff.seed_details)) {
      pf.seed_details = (handoff.seed_details as unknown[]).filter(
        (d): d is Record<string, unknown> => typeof d === "object" && d !== null,
      );
    }
    if (typeof handoff.literature_map === "string") {
      pf.literature_map = handoff.literature_map;
    } else if (handoff.literature_map && typeof handoff.literature_map === "object") {
      pf.literature_map = JSON.stringify(handoff.literature_map);
    }
  }
  if (typeof handoff.cluster === "string") {
    const c = handoff.cluster.toLowerCase();
    if (c === "panel" || c === "exactid" || c === "partialid" || c === "stat" || c === "experimentation" || c === "scm") pf.cluster = c;
  }
  if (typeof handoff.novelty_justification === "string") {
    pf.novelty_justification = handoff.novelty_justification;
  } else if (handoff.novelty_justification && typeof handoff.novelty_justification === "object") {
    pf.novelty_justification = JSON.stringify(handoff.novelty_justification);
  }

  // needs-pivot: the author declined this mode (revise can't fix / no surviving
  // seed). Record it so Stage -0.5 drives the pivot (mirrors the monolith's
  // last_draft_status="needs-pivot" path). Ideation fields above remain available
  // to the pivot even when no advancing core was authored this round.
  if (authored.status === "needs-pivot") {
    pf.current_version = args.nextVersion;
    pf.last_draft_handoff = JSON.stringify(handoff);
    // A sandbox/process-startup failure arrives as a well-formed needs-pivot receipt
    // (blocking_reason names the environment fault). Classifying it here is what feeds
    // the D-0.5 retry branch (`neg1_env_failure_retries`); the monolith made this call
    // and the carve lost it, so a spawn failure burned a healthy angle as "dead".
    const envFailure = handoffSignalsEnvFailure(handoff);
    pf.last_draft_status = envFailure ? "env-failure" : "needs-pivot";
    return {
      stage: "-1.2",
      status: "completed",
      message: envFailure
        ? `Stage -1.2 (single-artifact) mode=${args.mode} hit an ENVIRONMENT failure (sandbox/process startup) — angle ${args.angleIndex} is NOT dead; D-0.5 retries the same draft`
        : `Stage -1.2 (single-artifact) mode=${args.mode} returned needs-pivot — angle ${args.angleIndex} not authorable as posed`,
      artifacts: [],
    };
  }

  // Harvest into proposed_from (mirror the monolith's harvest). Cold-start
  // normally owns the ideation outputs (seeds / literature_map). A later mode
  // also rehydrates them from the authoritative core when persisted state is
  // empty, so an interrupted/legacy run cannot turn real seeds into fake
  // `needs-pivot` rounds. Every mode may refresh cluster + novelty justification.
  // The full handoff JSON feeds the -0.5 reviewer (including its checklist).
  pf.current_version = args.nextVersion;
  pf.last_draft_handoff = JSON.stringify(handoff);
  pf.last_draft_status = "completed";
  // The proto_core JSON is the sole artifact (no proposal .tex). Point
  // proposal_path at it so pipeline.ts's resume-safety guard (re-enter -1.2 when
  // the recorded draft is missing on disk) sees a real file.
  pf.proposal_path = authored.protoCoreJsonPath;

  return {
    stage: "-1.2",
    status: "completed",
    message: `Stage -1.2 (single-artifact) authored angle=${args.angleIndex} v${args.nextVersion} mode=${args.mode} → proto_core.json`,
    artifacts: [authored.protoCoreJsonPath],
  };
}

/**
 * Render the stdout JSON template into the qid folder, pre-filling values the
 * orchestrator already knows (chosen_qid, chosen_specialization, version,
 * mode, proposal_path) and stripping mode-inapplicable fields. The proposer
 * agent reads THIS file (right next to the .tex), not the static template
 * under tools/src/templates/. Refreshed on every invocation so mode / version
 * stay current across revise / pivot iterations.
 */
async function renderProposalOutputTemplate(args: {
  ctx: PipelineContext;
  targetPath: string;
  mode: "cold-start" | "revise" | "pivot" | "kernel-replace" | "draft-rebuild";
  version: number;
  proposalTexPath: string;
}): Promise<void> {
  const src = await readFile(
    templatePath(args.ctx.repoRoot, "stage_neg1_2_output_template.json"),
    "utf8",
  );
  const tmpl = JSON.parse(src) as Record<string, unknown>;

  tmpl.chosen_qid = args.ctx.qid;
  tmpl.chosen_specialization = args.ctx.specialization;
  tmpl.version = args.version;
  tmpl.mode = args.mode;
  tmpl.proposal_path = args.proposalTexPath;

  // Mode-conditional field stripping. Mirrors the rules in _emit_rules but
  // enforces them HERE so the agent never sees a field it should not emit
  // (eliminates the most common drift mode). revise / draft-rebuild /
  // kernel-replace all inherit the cold-start literature_map + seeds payload
  // from the angle's prior version, so they MUST NOT re-emit those fields;
  // only cold-start and pivot are allowed to author fresh seeds.
  const inheritsFromColdStart =
    args.mode === "revise" || args.mode === "draft-rebuild" || args.mode === "kernel-replace";
  if (inheritsFromColdStart) {
    delete tmpl.literature_map;
    delete tmpl.seeds;
    delete tmpl.seed_details;
    delete tmpl.prior_work_summary;
  } else {
    delete tmpl.addressed_flags;
  }

  await mkdir(path.dirname(args.targetPath), { recursive: true });
  await writeFile(args.targetPath, `${JSON.stringify(tmpl, null, 2)}\n`, "utf8");
}

/** Move an existing archive aside under the first free `.prevN` name, so archiving is
 *  never destructive. Returns the path it was parked at, or null if nothing was there. */
export async function preserveExistingArchive(target: string): Promise<string | null> {
  try {
    await access(target);
  } catch {
    return null;
  }
  for (let n = 1; n < 1000; n++) {
    const parked = `${target}.prev${n}`;
    try {
      await access(parked);
    } catch {
      await rename(target, parked);
      return parked;
    }
  }
  throw new Error(`[archive] refusing to overwrite ${target}: 999 prior archives already parked alongside it.`);
}

export async function archiveProposalForPivot(
  proposalPath: string,
  angleIndex: number,
): Promise<string | null> {
  const dir = path.dirname(proposalPath);
  const base = path.basename(proposalPath, ".tex");
  // Archive names are keyed by angle only, so a SECOND pivot off the same angle used to
  // overwrite the first — and `reset_proposal_cursor` would then re-seat the cursor at
  // version V while restoring whichever draft happened to survive. Never destroy an
  // archive: on collision, park the incumbent under a numbered suffix first.
  const archived = path.join(dir, `${base}_angle${angleIndex}_rejected.tex`);
  await preserveExistingArchive(archived);
  // Single-artifact mode (stage -1.2): the substance is in proto_core.json, not
  // the .tex. Snapshot it alongside the .tex so a later cursor-reset can restore
  // the converged core (see bin/reset_proposal_cursor.ts). Best-effort: absent in
  // .tex-only mode. Snapshot (copy) rather than move so the live file is intact
  // for the next angle's producer to overwrite.
  const protoCore = path.join(dir, "proto_core.json");
  try {
    await access(protoCore);
    const protoArchive = path.join(dir, `proto_core_angle${angleIndex}_rejected.json`);
    await preserveExistingArchive(protoArchive);
    await copyFile(protoCore, protoArchive);
  } catch {
    /* no proto_core to snapshot — .tex-only mode */
  }
  try {
    await rename(proposalPath, archived);
    return archived;
  } catch {
    return null;
  }
}

async function persistReviewJson(
  ctx: PipelineContext,
  angle: number,
  version: number,
  json: Record<string, unknown>,
): Promise<void> {
  const dir = resolveInDir(formalizationDir(ctx.repoRoot, ctx.qid), "reviews", [
    `${ctx.qid}_${ctx.specialization}_reviews`,
  ]);
  await mkdir(dir, { recursive: true });
  const file = path.join(dir, `angle${angle}_v${version}.json`);
  await writeFile(file, `${JSON.stringify(json, null, 2)}\n`, "utf8");
}

export async function logNeg1Review(args: {
  ctx: PipelineContext;
  angle: number;
  version: number;
  verdict: string;
  json: Record<string, unknown>;
}): Promise<void> {
  const status: "accept" | "revise" | "reject" =
    args.verdict === "ACCEPT" ? "accept" : args.verdict === "REJECT" ? "reject" : "revise";
  const flagCounts = {
    S: countFlags(args.json.structure_flags),
    N: countFlags(args.json.novelty_flags),
    C: countFlags(args.json.soundness_flags),
  };
  const tier =
    typeof args.json.publishability_tier === "string" ? args.json.publishability_tier : "unknown";
  const entry: Omit<Extract<ReviewLogEntry, { kind: "review" }>, "timestamp"> = {
    kind: "review",
    stage: "stage_neg1",
    attempt: args.angle * NEG1_REVISE_CAP + args.version,
    status,
    report_summary: `angle=${args.angle} v${args.version} verdict=${args.verdict} tier=${tier} S=${flagCounts.S} N=${flagCounts.N} C=${flagCounts.C}`,
  };
  await appendReviewLog(args.ctx, entry);
  await persistReviewJson(args.ctx, args.angle, args.version, args.json);
}
export function buildDrafterHandoff(json: Record<string, unknown>): string {
  const lines: string[] = [];
  const stringField = (key: string) =>
    typeof json[key] === "string" ? (json[key] as string) : null;
  const obj = (key: string) =>
    json[key] && typeof json[key] === "object" ? (json[key] as Record<string, unknown>) : null;

  for (const key of ["chosen_qid", "chosen_specialization", "version", "mode"] as const) {
    const v = json[key];
    if (v !== undefined) lines.push(`${key}: ${JSON.stringify(v)}`);
  }

  if (json.upgrade_mode === true) {
    lines.push(
      "",
      `upgrade_mode: true`,
      `parent_qid: ${JSON.stringify(json.parent_qid ?? "")}`,
      `parent_spec: ${JSON.stringify(json.parent_spec ?? "")}`,
      `upgrade_axis: ${JSON.stringify(json.upgrade_axis ?? "")}`,
    );
    if (typeof json.delta_summary === "string") {
      lines.push(`delta_summary: ${json.delta_summary}`);
    }
    if (Array.isArray(json.reused_bibkeys)) {
      lines.push(`reused_bibkeys: ${JSON.stringify(json.reused_bibkeys)}`);
    }
    if (Array.isArray(json.new_bibkeys)) {
      lines.push(`new_bibkeys: ${JSON.stringify(json.new_bibkeys)}`);
    }
  }

  // Honor the exact key `literature_checklist`, but fall back to the paraphrase
  // keys the producer model empirically drifts to (e.g. `named_literature_checklist`)
  // so a renamed-but-present checklist is not silently treated as MISSING and
  // does not spuriously trigger N-thin-survey.
  const checklist =
    json.literature_checklist ??
    json.named_literature_checklist ??
    json.literature_check_list;
  if (Array.isArray(checklist) && checklist.length > 0) {
    lines.push("", "literature_checklist (drafter-emitted; the reviewer must verify each entry):");
    for (const item of checklist) {
      lines.push(`- ${JSON.stringify(item)}`);
    }
  } else {
    lines.push(
      "",
      "literature_checklist: <MISSING — drafter did not emit a checklist; reviewer must reconstruct from §5 and treat thin/absent coverage as N-thin-survey>",
    );
  }

  const labels = json.statement_labels;
  if (Array.isArray(labels) && labels.length > 0) {
    lines.push("", "statement_labels (Theorem vs Conjecture per result):");
    for (const item of labels) {
      lines.push(`- ${JSON.stringify(item)}`);
    }
  }

  const justification = obj("novelty_justification");
  if (justification) {
    lines.push("", "novelty_justification:");
    if (typeof justification.repo_axis === "string") {
      lines.push(`  repo_axis: ${justification.repo_axis}`);
    }
    if (typeof justification.published_axis === "string") {
      lines.push(`  published_axis: ${justification.published_axis}`);
    }
  } else {
    const flat = stringField("novelty_justification");
    if (flat) lines.push("", `novelty_justification: ${flat}`);
  }

  const message = stringField("message");
  if (message) lines.push("", `drafter_message: ${message}`);

  // The typed-core (proto) producer emits the SC6 comparator table under
  // `comparator_promises`; the legacy template uses `comparator_promise_table`.
  // Accept either so the reviewer sees the table on the proto path (otherwise
  // N-comparator-drift fires unfixably every revise round on a present table).
  const promiseTable =
    json.comparator_promise_table ?? json.comparator_promises;
  if (Array.isArray(promiseTable) && promiseTable.length > 0) {
    lines.push(
      "",
      "comparator_promise_table (drafter SC6 output — every published comparator named in §1/§3 abstract must map to a §8 conjecture, or be downgraded / dropped):",
    );
    for (const item of promiseTable) {
      lines.push(`- ${JSON.stringify(item)}`);
    }
  } else {
    lines.push(
      "",
      "comparator_promise_table: <MISSING — drafter did not emit the SC6 table; reviewer MUST emit N-comparator-drift unless §1/§3 abstract names NO published comparator at all>",
    );
  }

  return lines.length > 0 ? lines.join("\n") : "<empty handoff>";
}

export function countFlags(value: unknown): number {
  return Array.isArray(value) ? value.length : 0;
}
