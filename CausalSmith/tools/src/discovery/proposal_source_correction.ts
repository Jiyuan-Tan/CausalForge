/**
 * Administrative correction for reviewer-induced citation/source metadata drift.
 *
 * Only literature-facing string fields are mutable. Formal definitions,
 * assumptions, statements, witnesses, and statuses are structurally unreachable
 * from this helper, so a source correction cannot become a hidden math revision.
 */
import { readFile, readdir, rename, stat, writeFile } from "node:fs/promises";
import path from "node:path";
import { appendPipelineLog } from "../log.js";
import { formalizationDir } from "../paths.js";
import { loadState, saveState } from "../state.js";
import { CoreSchema } from "./core/schema.js";
import { runProposalGate } from "./core/proposal_gate.js";
import { protoCoreJsonPath } from "./stages/neg1_2_author.js";
import { parseRepairedModelJson } from "./core/core_io.js";

export interface ProposalSourceCorrectionResult {
  coreReplacements: number;
  handoffReplacements: number;
  corePath: string;
}

const CORE_START = "=== PROPOSAL CORE (the artifact under review — typed source of truth) ===";
const CORE_END = "=== END PROPOSAL CORE ===";

function replaceCount(source: string, from: string, to: string): { value: string; count: number } {
  const pieces = source.split(from);
  return { value: pieces.join(to), count: pieces.length - 1 };
}

function replaceField(
  owner: Record<string, unknown>,
  key: string,
  from: string,
  to: string,
): number {
  if (typeof owner[key] !== "string") return 0;
  const replaced = replaceCount(owner[key] as string, from, to);
  owner[key] = replaced.value;
  return replaced.count;
}

function correctLiteratureFields(
  object: Record<string, unknown>,
  from: string,
  to: string,
): number {
  let count = replaceField(object, "related_work", from, to);
  for (const tableKey of ["comparator_promises", "comparator_promise_table"] as const) {
    for (const row of Array.isArray(object[tableKey]) ? object[tableKey] : []) {
      if (row && typeof row === "object") {
        count += replaceField(row as Record<string, unknown>, "comparator_claim", from, to);
      }
    }
  }
  for (const row of Array.isArray(object.literature_checklist) ? object.literature_checklist : []) {
    if (row && typeof row === "object") {
      count += replaceField(row as Record<string, unknown>, "one_line", from, to);
    }
  }
  return count;
}

export async function applyProposalSourceCorrection(
  repoRoot: string,
  qid: string,
  specialization: string,
  from: string,
  to: string,
): Promise<ProposalSourceCorrectionResult> {
  if (!from || !to || from === to) {
    throw new Error("proposal-source-correction requires distinct non-empty --from and --to strings");
  }
  const state = await loadState(repoRoot, qid, specialization);
  const pf = state.proposed_from;
  const currentAngle = pf?.current_angle_index ?? 0;
  const currentVersion = pf?.current_version ?? 0;
  const currentReviewStillActive = (pf?.iterations ?? []).some(
    (it) => it.angle === currentAngle && it.version === currentVersion,
  );
  const parkedOrReviewerOnlyReopened =
    pf?.angle_checkpoint !== undefined ||
    (pf?.final_verdict === "pending" && !currentReviewStillActive);
  if (!pf || !parkedOrReviewerOnlyReopened || pf.last_draft_status !== "completed" || !pf.last_draft_handoff) {
    throw new Error(
      "proposal-source-correction requires a completed proposal either parked at D-0.5 or reopened by reviewer invalidation",
    );
  }
  if (state.stage_completed !== "-1.2") {
    throw new Error(`proposal-source-correction requires stage_completed=-1.2; found ${state.stage_completed}`);
  }

  const corePath = protoCoreJsonPath({
    repoRoot,
    qid,
    specialization,
    dryRun: false,
    resume: true,
  });
  const originalCoreRaw = await readFile(corePath, "utf8");
  // Three-layer defense: the core and handoff are model-authored TeX carriers;
  // the corrected artifacts persisted below then also leave in canonical form.
  const core = parseRepairedModelJson(originalCoreRaw, corePath) as Record<string, unknown>;
  const coreReplacements = correctLiteratureFields(core, from, to);

  const handoff = parseRepairedModelJson(
    pf.last_draft_handoff,
    "proposal-source-correction: last_draft_handoff",
  ) as Record<string, unknown>;
  const handoffReplacements = correctLiteratureFields(handoff, from, to);
  if (coreReplacements + handoffReplacements === 0) {
    throw new Error(`proposal-source-correction found no exact occurrence of ${JSON.stringify(from)}; nothing changed`);
  }

  // Validate, but persist the ORIGINAL object. CoreSchema intentionally strips
  // producer metadata it does not consume (seeds, literature_map, comparator
  // promises). Persisting CoreSchema.parse(core) here would silently delete
  // those authoritative fields during an otherwise literature-only correction.
  CoreSchema.parse(core);
  const gate = runProposalGate(core);
  if (!gate.ok) {
    throw new Error(
      `proposal-source-correction unexpectedly failed the proposal gate: ` +
        gate.violations.map((v) => `${v.code}@${v.where}`).join(", "),
    );
  }
  const correctedCoreRaw = `${JSON.stringify(core, null, 2)}\n`;
  pf.last_draft_handoff = JSON.stringify(handoff);

  await writeFile(corePath, correctedCoreRaw, "utf8");
  try {
    await saveState(repoRoot, qid, specialization, state);
  } catch (err) {
    await writeFile(corePath, originalCoreRaw, "utf8");
    throw err;
  }
  await appendPipelineLog(
    { repoRoot, qid, specialization },
    {
      stage: "-0.5",
      status: "source-corrected",
      duration_ms: 0,
      message:
        `Administrative literature-only correction at angle ${pf.current_angle_index ?? 0} ` +
        `v${pf.current_version ?? 0}: ${JSON.stringify(from)} -> ${JSON.stringify(to)}; ` +
        `${coreReplacements} core and ${handoffReplacements} handoff replacement(s).`,
    },
  );
  return { coreReplacements, handoffReplacements, corePath };
}

/** Recover the exact latest proto core inlined into a D-0.5 reviewer transcript.
 * Used only when a main-owned administrative writer itself damaged persistence. */
export async function recoverProposalCoreFromLatestReviewPrompt(
  repoRoot: string,
  qid: string,
  specialization: string,
): Promise<{ corePath: string; backupPath: string; sourceLog: string }> {
  const stageLogDir = path.join(formalizationDir(repoRoot, qid), "logs", "stages");
  const candidates: Array<{ file: string; mtimeMs: number; coreText: string }> = [];
  for (const name of await readdir(stageLogDir)) {
    if (!name.endsWith(".log")) continue;
    const file = path.join(stageLogDir, name);
    const src = await readFile(file, "utf8");
    const start = src.lastIndexOf(CORE_START);
    if (start < 0) continue;
    const bodyStart = start + CORE_START.length;
    const end = src.indexOf(CORE_END, bodyStart);
    if (end < 0) continue;
    candidates.push({
      file,
      mtimeMs: (await stat(file)).mtimeMs,
      coreText: src.slice(bodyStart, end).trim(),
    });
  }
  candidates.sort((a, b) => b.mtimeMs - a.mtimeMs);
  const latest = candidates[0];
  if (!latest) throw new Error(`no complete D-0.5 PROPOSAL CORE block found under ${stageLogDir}`);
  const core = parseRepairedModelJson(
    latest.coreText,
    `review transcript core block in ${latest.file}`,
  ) as Record<string, unknown>;
  if (core.qid !== qid || core.specialization !== specialization) {
    throw new Error(
      `review transcript core identity mismatch: expected ${qid}/${specialization}, ` +
        `found ${String(core.qid)}/${String(core.specialization)}`,
    );
  }
  CoreSchema.parse(core);
  const gate = runProposalGate(core);
  if (!gate.ok) throw new Error("review transcript core fails the proposal gate; refusing recovery");

  const corePath = protoCoreJsonPath({ repoRoot, qid, specialization, dryRun: false, resume: true });
  let backupPath = `${corePath}.pre-recovery`;
  for (let n = 1; ; n++) {
    try {
      await stat(backupPath);
      backupPath = `${corePath}.pre-recovery.${n}`;
    } catch {
      break;
    }
  }
  await rename(corePath, backupPath);
  try {
    await writeFile(corePath, `${latest.coreText}\n`, "utf8");
  } catch (err) {
    await rename(backupPath, corePath);
    throw err;
  }
  await appendPipelineLog(
    { repoRoot, qid, specialization },
    {
      stage: "-0.5",
      status: "core-recovered",
      duration_ms: 0,
      message: `Recovered proto core from latest complete D-0.5 transcript ${latest.file}; parked damaged copy at ${backupPath}.`,
    },
  );
  return { corePath, backupPath, sourceLog: latest.file };
}
