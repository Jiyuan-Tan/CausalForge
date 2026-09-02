// D0-SOLVE step 2/5 — dispatchAgents (spec §Stage kernel).
//
// WCC partitioning of the open frontier, per-round prose/emission ownership
// selection, per-unit prompt assembly, the solveUnit agent dispatch (with the
// id parse/heal at the unit output boundary), moved verbatim from
// stage0_solve.ts in the T1 carve. Capability projection and conflict
// resolution over the raw outputs happen in solve/merge.ts.
import { existsSync } from "node:fs";
import { mkdir, open, readFile, readdir, rename, rm, writeFile } from "node:fs/promises";
import { createHash, randomUUID } from "node:crypto";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import { artifactPath, formalizationDir } from "../../paths.js";
import { discoveryBrief, parseStageOutput, readPrompt, type StageDeps } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import type { Core, CoreStatement } from "../core/schema.js";
import { healStatementId } from "../core/node_ids.js";
import {
  assertNoDecodedControlChars,
  assertSealableLatexPayload,
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../core/latex_serialization.js";
import { archiveProofs, proofBytesInRoundFile } from "../proof_archive.js";
import { hotProofBytes, loadWorkingState } from "../stages/d0_working.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import type { SolveUnitOutput } from "./schemas.js";
import { SolveUnitOutputSchema } from "./schemas.js";
import {
  type SolveDispatchUnit,
  selectDirectiveEmissionOwnerLabel,
  selectSemanticTargetOwners,
} from "./ownership.js";
import { openSolveTarget, type SolveRoundContext } from "./context.js";
import { stampRevision } from "../core/revision.js";
import { companionPathFor, sliceTexCompanion, resolveTexRefs } from "./tex_companion.js";
import { coreEditTarget, type RawCoreEdit } from "../stages/d0_apply.js";
import {
  projectFrozenCore,
  serializeFrozenCoreSnapshot,
} from "./context_projection.js";

/** A worker's explicit "the target is not provable" refusal — a mathematical
 * signal that must surface unchanged, never a mechanical-retry candidate. */
class SolveUnitMathFailure extends Error {}

/** The completed worker's OUTPUT failed the mechanical reader (garbled stdout
 * receipt, missing/invalid/unsealable output file). Deterministic normalization
 * has already run before this is raised. A missing or damaged carrier permits
 * one model-call recovery; semantic/schema failures surface unchanged. */
class SolveUnitMechanicalReadError extends Error {}

/** The persisted artifact is not a readable carrier (damaged JSON / TeX bytes)
 * even after readSolveUnitOutput's deterministic repairs: the model call itself
 * failed and may be repeated once. A schema/semantic contradiction in a readable
 * carrier is deliberately NOT this class — no mechanical rewrite may guess intent. */
export class SolveUnitCarrierError extends Error {}

/** Classify the reader's raw failure ONCE at the reader boundary. JSON.parse
 * failures are typed (SyntaxError); the TeX-side helpers live in sibling modules
 * and identify their defects by message, which is matched here and nowhere else. */
function isCarrierDefect(err: unknown): boolean {
  if (err instanceof SyntaxError) return true;
  const message = err instanceof Error ? err.message : String(err);
  return /(?:Bad control character|LaTeX payload cannot be sealed|decoded JSON control character|under-escaped TeX|TeX companion|tex_ref|no tex_ref cites)/i.test(message);
}

async function syncDirectory(dir: string): Promise<void> {
  const handle = await open(dir, "r");
  try {
    try {
      await handle.sync();
    } catch (err) {
      const code = (err as NodeJS.ErrnoException).code;
      if (code !== "EINVAL" && code !== "ENOTSUP" && code !== "EISDIR") throw err;
    }
  } finally {
    await handle.close();
  }
}

/** Per-unit output JSON path ('thm:x' → 'thm_x', 'props' → 'props'). */
function unitOutPath(ctx: PipelineContext, label: string): string {
  const slug = label.replace(/[^a-z0-9]+/gi, "_");
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", `solve_${slug}.json`, [`${ctx.qid}_solve_${slug}.json`]);
}

const sha256Hex = (bytes: string): string => createHash("sha256").update(bytes).digest("hex");

/** Round-scoped reuse receipts for solveUnit's persisted-output reuse lane.
 *
 * A merge/gate failure lands AFTER every unit has been paid for, and a resume used
 * to clear the outputs and re-pay every model call even when nothing about a
 * unit's inputs had changed (observed back-to-back identical re-fails:
 * exp_mixed 2026-08-09 19:26→19:32, stat_transport 2026-08-30 15:51→16:00; one
 * exp_two_wave unit was re-dispatched 15x through such cycles). A receipt binds a
 * validated output file to the exact prompt that produced it; a later dispatch
 * with a byte-identical prompt reuses the output instead of calling the model.
 * Receipts exist only between a unit's validated write and the round's successful
 * commit (commitRound deletes the directory), so a committed round can never leak
 * a stale answer into the next round. */
export function solveReuseReceiptsDir(ctx: PipelineContext): string {
  return path.join(path.dirname(unitOutPath(ctx, "snapshot")), "solve_receipts");
}

/** Canonicalize every model-authored string before solve-unit schema validation and
 * proposal persistence. The repair itself is deliberately narrow, so traversing the
 * full payload catches `current`, `proposed`, nested core edits, proofs, and prose
 * without changing ordinary tabs or non-LaTeX text. */
export function repairSolveUnitLatexSerialization(value: unknown): void {
  repairLatexStringsDeep(value);
}

/** Treat a model-serialized empty optional mutation channel as omission.
 *
 * `prose_updates: {}` has no writable field and therefore cannot mutate prose,
 * but retaining the key makes the ownership gate classify it as an attempted
 * prose write. Normalize only the literally empty object; any populated prose
 * payload remains subject to the ordinary ownership checks.
 */
export function normalizeEmptySolveUnitContainers(value: unknown): void {
  if (value === null || typeof value !== "object" || Array.isArray(value)) return;
  const body = value as Record<string, unknown>;
  const prose = body.prose_updates;
  if (
    prose !== null &&
    typeof prose === "object" &&
    !Array.isArray(prose) &&
    Object.keys(prose as Record<string, unknown>).length === 0
  ) {
    delete body.prose_updates;
  }
}

/** Fail closed when a worker puts new claim bytes only in the metadata channel.
 *
 * The standalone JSON schema can verify that every declared claim correction has
 * a matching `statement-replace`, but it cannot detect the reverse omission
 * without the frozen statement catalog.  If this check is deferred to merge, the
 * orphan edit is filtered as unpublishable after its same-round proof has already
 * been accepted, silently pairing a proof of the proposed claim with the old one.
 * Run this inside the mechanical-reader retry boundary instead.
 */
export function assertClaimChangingStatementReplacementsArePaired(
  output: SolveUnitOutput,
  statements: CoreStatement[],
): void {
  const statementById = new Map(statements.map((statement) => [statement.id, statement] as const));
  for (const edit of output.proposed_core_edits) {
    if (edit.kind !== "statement-replace") continue;
    const current = statementById.get(edit.id);
    if (current === undefined || edit.proposed.statement === current.statement) continue;
    const pairs = output.proposed_statement_changes.filter(
      (change) => change.id === edit.id && change.proposed === edit.proposed.statement,
    );
    if (pairs.length !== 1) {
      throw new Error(
        `claim-changing statement-replace ${edit.id} requires exactly one paired ` +
          `proposed_statement_changes item; found ${pairs.length}`,
      );
    }
  }
  for (const proof of output.proofs) {
    if (proof.argues_proposed !== true) continue;
    const current = statementById.get(proof.id);
    const changes = output.proposed_statement_changes.filter(
      (change) => change.id === proof.id && change.proposed !== current?.statement,
    );
    const completePairs = changes.filter((change) =>
      output.proposed_core_edits.some(
        (edit) => edit.kind === "statement-replace" && edit.id === proof.id &&
          edit.proposed.statement === change.proposed,
      )
    );
    if (completePairs.length !== 1) {
      throw new Error(
        `proof ${proof.id} sets argues_proposed=true but has ${completePairs.length} complete ` +
          `claim-change transaction(s); exactly one changed statement and post-image are required`,
      );
    }
  }
}

async function publishFrozenCoreSnapshot(
  ctx: PipelineContext,
  core: Core,
): Promise<{ path: string; bytes: string; sha256: string }> {
  const serialized = serializeFrozenCoreSnapshot(core);
  const dir = path.join(path.dirname(unitOutPath(ctx, "snapshot")), "solve_context");
  const snapshotPath = path.join(dir, `core-${serialized.sha256}.json`);
  await mkdir(dir, { recursive: true });
  if (existsSync(snapshotPath)) {
    const existing = await readFile(snapshotPath, "utf8");
    if (existing !== serialized.bytes) {
      throw new Error(`D0 frozen-core snapshot hash collision/corruption at ${snapshotPath}`);
    }
  } else {
    const staged = `${snapshotPath}.tmp-${process.pid}-${Date.now()}`;
    try {
      await writeFile(staged, serialized.bytes, "utf8");
      await rename(staged, snapshotPath);
    } finally {
      await rm(staged, { force: true });
    }
  }
  return { path: snapshotPath, ...serialized };
}

/** When F3 bounced a node back to D0 with a refuting witness (`flags.redo_math_witness`), surface it
 *  so the re-solve CONSUMES it: re-derive only the refuted node + its dependents (never from scratch),
 *  treating the obstruction as a hard constraint — so the solver cannot regenerate the same false claim.
 *  Empty string when there is no parked witness. */
function redoMathWitnessBlock(state: StateJson): string {
  const w = state.flags.redo_math_witness;
  if (!w) return "";
  return [
    "=== F3 REFUTATION — RE-DERIVE THIS NODE (do NOT re-emit the refuted claim) ===",
    `Node \`${w.obj_id}\` was PROVEN-FALSE downstream by a concrete witness; your prior derivation of it`,
    `is WRONG. Re-derive ONLY this node and its dependents [${w.dependents.join(", ") || "none"}]; leave`,
    "every other established proof intact (incremental re-solve, not from scratch). The refuting witness",
    `(type: ${w.type}) is a HARD CONSTRAINT your new statement/proof MUST respect:`,
    w.detail,
    "If the node cannot be salvaged as stated, weaken/correct it (proposed_statement_changes) so the",
    "witness no longer refutes it — never restate the same claim.",
  ].join("\n");
}

export async function acquireSolvePathLease(outPath: string): Promise<{
  release: () => Promise<void>;
  assertOwned: () => Promise<void>;
}> {
  const lockDirectory = `${outPath}.lease.lock`;
  const ownerPath = path.join(lockDirectory, "owner-token");
  const ownerToken = randomUUID();
  try {
    await mkdir(lockDirectory);
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "EEXIST") {
      throw Object.assign(new Error(`solve output path is already locked: ${outPath}`), { code: "ELOCKED" });
    }
    throw err;
  }
  await writeFile(ownerPath, `${ownerToken}\n`, { encoding: "utf8", flag: "wx" });
  const assertOwned = async (): Promise<void> => {
    try {
      if ((await readFile(ownerPath, "utf8")).trim() !== ownerToken) {
        throw new Error("owner token changed");
      }
    } catch (err) {
      throw new Error(`solve output lease ownership changed for ${outPath}: ${err instanceof Error ? err.message : String(err)}`);
    }
  };
  return {
    assertOwned,
    release: async () => {
      try {
        await assertOwned();
      } catch {
        return;
      }
      // The directory itself excludes a successor until this owner removes it;
      // token verification therefore fences the entire two-step release.
      await rm(ownerPath, { force: true });
      await rm(lockDirectory, { recursive: true, force: true });
    },
  };
}

/** Called only from inside the acquired per-qid run heartbeat. Hard crashes may
 * strand a path lock; the qid mutex proves that no normal pipeline owner remains.
 * The explicit parallel bypass skips reclamation and still gets fail-closed path
 * exclusion rather than unsafe stale stealing. */
export async function clearOrphanSolvePathLeases(ctx: PipelineContext): Promise<void> {
  if (process.env.CAUSALSMITH_ALLOW_PARALLEL === "1") return;
  const runDir = formalizationDir(ctx.repoRoot, ctx.qid);
  // artifactPath may resolve canonical or qid-prefixed outputs in either the
  // nested discovery directory or the legacy flat run directory.
  for (const dir of [path.join(runDir, "discovery"), runDir]) {
    let names: string[];
    try {
      names = await readdir(dir);
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code === "ENOENT") continue;
      throw err;
    }
    for (const name of names) {
      if (/(^|_)solve_.*\.json\.lease\.lock$/.test(name)) {
        await rm(path.join(dir, name), { recursive: true, force: true });
      }
    }
  }
}

/** Dispatch one solver agent for a set of target statements (a headline, or all props). */
async function solveUnit(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  core: Core;
  /** Authoritative current statement bytes, including shelved durable nodes that
   * are intentionally absent from the assembled publication view. */
  statementCatalog: CoreStatement[];
  targets: CoreStatement[];
  label: string;
  clusterSetupBlock: string;
  /** Incremental context: the orchestrator escalation log, established-node
   *  receipts, and prior target/partial proofs that prevent mathematical restart. */
  priorContext?: string;
  /** Paper-wide prose has one deterministic owner per directed round. Other
   * units solve mathematics only and must omit `prose_updates`. */
  proseRole: "owner" | "omit" | "none";
  /** A directed round also has one writer for cross-cutting additions/edits.
   * Non-owners may still prove their targets and add genuinely local, non-cited
   * proof helpers. */
  directiveEmissionRole: "owner" | "local" | "none";
  requiredCoreTargets: string[];
  requiredCoreEdits: RawCoreEdit[];
  ownedSemanticTargets: string[];
  siblingSemanticTargets: Array<{ id: string; owner: string }>;
  coreSnapshotPath: string;
  /** Explicit ids whose cross-unit emission belongs to the one staged owner. */
  sharedTargetIds: string[];
}): Promise<SolveUnitOutput> {
  const { ctx, targets, label } = args;
  const outPath = unitOutPath(ctx, label);
  await mkdir(path.dirname(outPath), { recursive: true });
  const pathLease = await acquireSolvePathLease(outPath);
  try {
  // The companion dir (discovery/solve_tex/) must exist before the worker
  // tries to write its raw-TeX file into it.
  await mkdir(path.dirname(companionPathFor(outPath)), { recursive: true });
  // Output paths are stable across D0 rounds. Remove the prior invocation's
  // artifact before dispatch so a worker that reports completion but fails to
  // write cannot be credited with stale proofs/proposals from an earlier round.
  // Archive its proof bytes first: if the prior round died before commit, this file is
  // the ONLY copy of what that dispatch paid for. Bytes that DID reach the working
  // cursor are filtered out — they are hot, not displaced, and a false archive row
  // would later suppress the record of a real displacement (dedup is (bytes, node)).
  // A no-artifact model-call recovery below runs the same sweep so an orphaned
  // companion is archived before the mathematical call repeats. Existing damaged
  // JSON/TeX artifacts stay in place until the deterministic reader has tried its
  // normalizers; only an unrecoverable generation is archived before one re-call.
  // `.receipt` (never `.json`): replay's solve-output sweep ingests every
  // `solve_*.json` basename in the tree, and a receipt must not be mistaken for
  // a solve output there.
  const receiptPath = path.join(solveReuseReceiptsDir(ctx), `${path.basename(outPath)}.receipt`);
  const archiveAndClearRoundFiles = async (reason: string): Promise<void> => {
    await pathLease.assertOwned();
    await rm(receiptPath, { force: true });
    const companionPath = companionPathFor(outPath);
    const companionText = existsSync(companionPath) ? await readFile(companionPath, "utf8") : undefined;
    if (existsSync(outPath)) {
      const hot = hotProofBytes(await loadWorkingState(ctx));
      const stale = proofBytesInRoundFile(
        path.basename(outPath),
        await readFile(outPath, "utf8"),
        reason,
        companionText,
      ).filter((p) => !hot.get(p.nodeId)?.has(p.proofTex));
      if (stale.length > 0) await archiveProofs(path.dirname(outPath), stale);
    } else if (companionText !== undefined && companionText.trim().length > 0) {
      // ORPHANED companion (audit P23F5): the worker wrote its TeX and crashed
      // before the JSON. These bytes exist nowhere else — archive them as a
      // blob before the sweep deletes the file.
      await archiveProofs(path.dirname(outPath), [{
        nodeId: `file:${path.basename(companionPath)}`,
        proofTex: companionText,
        reason: `${reason}-orphan`,
      }]);
    }
    await pathLease.assertOwned();
    await rm(outPath, { force: true });
    await syncDirectory(path.dirname(outPath));
    // A stale companion from a prior round must never resolve into this round's
    // fresh output (Phase 3) — its bytes were archived above.
    await pathLease.assertOwned();
    await rm(companionPath, { force: true });
    await syncDirectory(path.dirname(companionPath));
    // A hard crash can strand a private canonical staging file.  This unit is
    // the sole owner of its stable output path, and dispatches are drained
    // before the qid lease is released, so exact-prefix cleanup is safe here.
    const stagedPrefix = `${path.basename(outPath)}.canonical-`;
    for (const name of await readdir(path.dirname(outPath))) {
      if (name.startsWith(stagedPrefix)) {
        await pathLease.assertOwned();
        await rm(path.join(path.dirname(outPath), name), { force: true });
      }
    }
  };
  // The stale-file sweep moved BELOW prompt assembly: a persisted output whose
  // receipt matches this round's exact prompt is reused instead of cleared.

  const projectedCore = projectFrozenCore(
    args.core,
    new Set(args.targets.map((target) => target.id)),
  );
  const targetReceipts = targets.map((target) => {
    const stamped = stampRevision(target);
    // The exact claim and dependency list already occur in the inline frozen
    // neighborhood. Keep only non-duplicated target metadata and the proof-route
    // guardrail here. A reopened
    // cited leaf is the exception: byte-faithful revalidation needs its complete
    // source-bearing node in one place.
    if (stamped.status === "cited") return stamped;
    const {
      statement: _statement,
      depends_on: _dependsOn,
      proof_tex: _proofTex,
      ...receipt
    } = stamped;
    return receipt;
  });
  const prompt = [
    await readPrompt(ctx, "stage0_common_discovery.txt"),
    "",
    args.clusterSetupBlock,
    "",
    await readPrompt(ctx, "stage0_solve.txt"),
    "",
    discoveryBrief(ctx, args.state),
    ...(redoMathWitnessBlock(args.state) ? ["", redoMathWitnessBlock(args.state)] : []),
    "",
    "=== FROZEN CORE TARGET NEIGHBORHOOD (read-only inline context) ===",
    JSON.stringify(projectedCore.inline, null, 2),
    "",
    "=== FROZEN CORE SNAPSHOT + OMISSION MANIFEST ===",
    `CORE_SNAPSHOT_PATH: ${args.coreSnapshotPath}`,
    JSON.stringify(projectedCore.manifest, null, 2),
    "The inline view contains your targets, their transitive statement dependencies, and referenced catalog/symbol closure. The compact manifest names omitted nodes and affected downstream statements. If an omitted id becomes relevant, inspect that id selectively in CORE_SNAPSHOT_PATH (for example with jq or rg); inspect affected downstream nodes before changing a claim or dependency they consume. Do not scan the snapshot by default and NEVER edit it.",
    ...(args.priorContext && args.priorContext.trim().length > 0 ? ["", args.priorContext] : []),
    ...(args.proseRole === "owner" ? [
      "",
      "=== PAPER-WIDE PROSE OWNERSHIP ===",
      "You are the ONLY solve unit allowed to emit `prose_updates` this round. Synthesize one canonical",
      "paper-wide update that incorporates the orchestrator directive. Your inline context stays local;",
      "inspect only the necessary prose or result records in CORE_SNAPSHOT_PATH before writing the update.",
      "Other units are forbidden to emit prose_updates, so do not expect or require identical prose from them.",
      "Top-level prose fields may summarize the whole paper. In `statement_notes`, name only statements present",
      "in this round's FROZEN CORE or a replacement theorem/helper that YOUR unit emits; omit prior-round or",
      "sibling-only ids that are visible only in escalation/reuse context.",
    ] : args.proseRole === "omit" ? [
      "",
      "=== PAPER-WIDE PROSE OWNERSHIP ===",
      "Another solve unit owns the single canonical paper-wide prose update. OMIT `prose_updates` entirely",
      "from your output, even though the orchestrator directive requests narrative synchronization. Solve only",
      "your mathematical targets; the designated prose owner will synchronize the paper-wide narrative.",
    ] : []),
    ...(args.directiveEmissionRole === "owner" ? [
      "",
      "=== GLOBAL SHARED-UPSTREAM OWNERSHIP ===",
      "You are the ONLY solve unit allowed to emit directive-wide shared payloads this round: the one global upstream owner.",
      `Explicit shared target ids: ${args.sharedTargetIds.join(", ") || "(none listed)"}.`,
      "Emit every explicitly shared or cross-cutting payload exactly once. Emit each",
      "new exact required node, proposed assumption,",
      "definition correction, or non-local `proposed_core_edits` symbol/definition/bibliography/comparator/metadata edit",
      "exactly once in YOUR output. Other units may cite or depend on those ids but are forbidden to emit them.",
      "A citation or helper used by only one sibling proof remains local to that sibling; do not preempt it.",
      `Exact required target ids for this round: ${args.requiredCoreTargets.join(", ") || "(none listed)"}.`,
      `Statement target ids semantically owned by YOUR unit: ${args.ownedSemanticTargets.join(", ") || "(none)"}.`,
      "IMPORTANT: being the cross-cutting owner does NOT authorize you to prove, replace, edit, or re-emit a",
      "statement target owned by a sibling unit. You may only depend on those sibling-owned ids:",
      ...(args.siblingSemanticTargets.length > 0
        ? args.siblingSemanticTargets.map(({ id, owner }) => `- ${id} -> semantic owner ${owner}`)
        : ["- (no sibling-owned statement targets)"]),
    ] : args.directiveEmissionRole === "local" ? [
      "",
      "=== GLOBAL SHARED-UPSTREAM OWNERSHIP ===",
      "The designated global unit is the canonical writer for explicit shared payloads. You are FORBIDDEN to",
      `emit any of these shared target ids: ${args.sharedTargetIds.join(", ") || "(none listed)"}.`,
      "You are also forbidden to emit an added node named by the exact required-target list, proposed assumptions,",
      "definition changes, or any `proposed_core_edits` whose target is not one of YOUR target statement ids.",
      `Exact required target ids for this round: ${args.requiredCoreTargets.join(", ") || "(none listed)"}.`,
      "If your proof uses an explicitly shared comparator/symbol/definition, add that exact id to `depends_on` and",
      "let the canonical owner emit it. You may still emit genuinely local cited comparators, proof helpers, and a",
      "statement change/edit for one of YOUR exact target ids. Do not duplicate the shared payload.",
      "Do not rely on new or changed owner mathematics before round merge; solve against the frozen core and",
      "explicit shared ids only. A purely shared staged bundle defers downstream to a later accepted-basis pass.",
      `Statement target ids semantically owned by YOUR unit: ${args.ownedSemanticTargets.join(", ") || "(none)"}.`,
      "Every proof, replacement, `proposed_statement_changes` item, or statement-target core edit for a",
      "sibling-owned id is forbidden. You may only depend on these sibling-owned ids:",
      ...(args.siblingSemanticTargets.length > 0
        ? args.siblingSemanticTargets.map(({ id, owner }) => `- ${id} -> semantic owner ${owner}`)
        : ["- (no sibling-owned statement targets)"]),
    ] : []),
    ...(args.requiredCoreEdits.length > 0 ? [
      "",
      "=== ORCHESTRATOR-SUPPLIED EXACT CORE EDITS (already in the atomic bundle) ===",
      JSON.stringify(args.requiredCoreEdits, null, 2),
      "These typed operations are already supplied by the orchestrator. Do NOT re-emit them.",
      "Do NOT prove, replace, reopen, or add a node named by a supplied statement-delete.",
      "Solve only the surviving targets and any dependency cleanup requested by the directive.",
    ] : []),
    "",
    `=== TARGET STATEMENT(S) TO SOLVE (unit: ${label}) ===`,
    "Exact claim text and dependencies are in the frozen neighborhood above; these receipts add target-only metadata.",
    JSON.stringify(targetReceipts, null, 2),
    "",
    `SOLVE_OUTPUT_PATH: ${outPath}`,
    `SOLVE_COMPANION_PATH: ${companionPathFor(outPath)}`,
    "D-orchestration validates and mechanically normalizes the artifact after this call; spend this call on the mathematics.",
    'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<solve.json>"]}.',
  ].join("\n");

  const attemptUnit = async (retryNote?: string): Promise<{
    output: SolveUnitOutput;
    companionBlocks: Map<string, string>;
  }> => {
    const attemptPrompt = retryNote === undefined
      ? prompt
      : [
          prompt,
          "",
          "=== MODEL-CALL RECOVERY — NO TRUSTWORTHY ARTIFACT WAS WRITTEN ===",
          retryNote,
          "Repeat the same mathematical answer and write the required artifact; do not change the solution.",
        ].join("\n");
    const out = await dispatchAgent({
      ctx,
      deps: args.deps,
      stage: "0",
      label: `D0-SOLVE unit ${label}${retryNote === undefined ? "" : " (model-call recovery)"}`,
      prompt: attemptPrompt,
      promptSources: ["prompts/D0/stage0_solve.txt", `unit:${label}`],
      model: MODEL_PLAN.stage0_solve.model,
      reasoningEffort: MODEL_PLAN.stage0_solve.effort,
      inactivityTimeoutMs: 30 * 60 * 1000,
    });
    const parsed = parseStageOutput(out.stdout);
    if (parsed.status === "parse_failed") {
      // Stdout is only a completion receipt; the persisted, strictly validated
      // artifact is the mathematical authority. Do not repay Sol merely because
      // the receipt was garbled when the file itself is complete and valid.
      try {
        const accepted = await readValidatedOutput();
        console.warn(
          `[D0-SOLVE] unit ${label}: stdout receipt was unparseable, but the persisted solve artifact ` +
            "passed the full mechanical reader; accepting it without a model retry.",
        );
        return accepted;
      } catch (artifactError) {
        throw new SolveUnitMechanicalReadError(
          `Stage 0-SOLVE unit ${label} returned unparseable stdout and its artifact was unusable: ` +
            `${artifactError instanceof Error ? artifactError.message : String(artifactError)}`,
          { cause: artifactError },
        );
      }
    }
    if (parsed.status === "failed") {
      throw new SolveUnitMathFailure(
        `Stage 0-SOLVE failed on unit ${label}: ${parsed.message ?? "(no message)"} — ` +
          `the target is not provable from its declared dependencies; fix the core, do not launder.`,
      );
    }
    try {
      return await readValidatedOutput();
    } catch (err) {
      throw new SolveUnitMechanicalReadError(err instanceof Error ? err.message : String(err), { cause: err });
    }
  };
  // Persisted-output reuse lane (see solveReuseReceiptsDir). Reuse requires the
  // receipt's prompt hash to match THIS dispatch's exact prompt bytes — the prompt
  // embeds the projected core, snapshot path (content-addressed), directive, roles,
  // and targets, so any operator adjustment that could change the unit's answer
  // also changes the prompt and forces an honest fresh solve. The reused bytes
  // still pass the full mechanical reader + validation below, exactly as a fresh
  // worker's output would; any mismatch or read failure falls back to a fresh
  // solve. Kill switch: CAUSALSMITH_D0_REUSE=0 (or delete the unit's solve_*.json).
  const promptSha = sha256Hex(prompt);
  const readValidatedOutput = async (): Promise<{
    output: SolveUnitOutput;
    companionBlocks: Map<string, string>;
  }> => {
    let companionBlocks = new Map<string, string>();
    const output = await readSolveUnitOutput(outPath, label, {
      postValidate: (parsed) =>
        assertClaimChangingStatementReplacementsArePaired(parsed, args.statementCatalog),
      persistCanonical: true,
      assertPersistenceLease: pathLease.assertOwned,
      onValidatedSnapshot: (snapshot) => {
        companionBlocks = snapshot.companionBlocks;
      },
    });
    return { output, companionBlocks };
  };
  const tryReusePersistedOutput = async (): Promise<{
    output: SolveUnitOutput;
    companionBlocks: Map<string, string>;
  } | null> => {
    if (process.env.CAUSALSMITH_D0_REUSE === "0") return null;
    let receipt: {
      format?: unknown;
      model?: unknown;
      effort?: unknown;
      prompt_sha256?: unknown;
      output_sha256?: unknown;
      companion_sha256?: unknown;
    };
    try {
      receipt = JSON.parse(await readFile(receiptPath, "utf8")) as typeof receipt;
    } catch {
      return null;
    }
    // The model/effort that produced the answer are dispatch inputs the prompt
    // bytes do not carry: an operator upgrading MODEL_PLAN between resumes wants
    // the new model's answer, not a silent replay of the old one. The format tag
    // invalidates every receipt across a receipt-semantics change.
    if (receipt.format !== "v1") return null;
    if (receipt.model !== MODEL_PLAN.stage0_solve.model) return null;
    if (receipt.effort !== MODEL_PLAN.stage0_solve.effort) return null;
    if (receipt.prompt_sha256 !== promptSha) return null;
    if (!existsSync(outPath)) return null;
    if (sha256Hex(await readFile(outPath, "utf8")) !== receipt.output_sha256) return null;
    const companionPath = companionPathFor(outPath);
    const companionSha = existsSync(companionPath)
      ? sha256Hex(await readFile(companionPath, "utf8"))
      : undefined;
    if ((receipt.companion_sha256 ?? undefined) !== companionSha) return null;
    try {
      const reused = await readValidatedOutput();
      console.warn(
        `[D0-SOLVE] unit ${label}: reusing the persisted validated output from the last uncommitted ` +
          `dispatch (prompt unchanged) — no model call. Change the directive or delete ` +
          `${path.basename(outPath)} to force a fresh solve.`,
      );
      return reused;
    } catch (err) {
      console.warn(
        `[D0-SOLVE] unit ${label}: persisted output matched its reuse receipt but failed ` +
          `re-validation (${err instanceof Error ? err.message : String(err)}); solving fresh.`,
      );
      return null;
    }
  };
  const writeReuseReceipt = async (): Promise<void> => {
    await pathLease.assertOwned();
    const companionPath = companionPathFor(outPath);
    const companionSha = existsSync(companionPath)
      ? sha256Hex(await readFile(companionPath, "utf8"))
      : undefined;
    await mkdir(path.dirname(receiptPath), { recursive: true });
    await writeFile(receiptPath, `${JSON.stringify({
      format: "v1",
      unit: label,
      created: new Date().toISOString(),
      model: MODEL_PLAN.stage0_solve.model,
      effort: MODEL_PLAN.stage0_solve.effort,
      prompt_sha256: promptSha,
      output_sha256: sha256Hex(await readFile(outPath, "utf8")),
      ...(companionSha !== undefined ? { companion_sha256: companionSha } : {}),
    }, null, 2)}\n`, "utf8");
  };
  const reusedAccepted = await tryReusePersistedOutput();
  if (reusedAccepted !== null) {
    // The canonical persist inside the reader may have re-normalized the file
    // bytes; refresh the receipt so the NEXT resume's hashes still match. The
    // companion bytes were archived by the original fresh acceptance.
    await writeReuseReceipt();
    return reusedAccepted.output;
  }
  await archiveAndClearRoundFiles("stale-dispatch-cleared");
  let accepted: { output: SolveUnitOutput; companionBlocks: Map<string, string> };
  try {
    accepted = await attemptUnit();
  } catch (err) {
    // Only a completed worker's unusable result is retried, and only once.
    // Mathematical refusals and infrastructure failures (timeout, spawn)
    // propagate unchanged. The reader has already applied every deterministic
    // JSON/TeX repair. A residual missing/damaged carrier means the model call
    // itself failed and permits one repeat; semantic/schema failures do not.
    if (!(err instanceof SolveUnitMechanicalReadError)) throw err;
    if (existsSync(outPath) && !(err.cause instanceof SolveUnitCarrierError)) {
      // The file exists but the failure is semantic/schema-level, not a damaged
      // JSON/TeX carrier. A mechanical rewrite would have to guess intent.
      throw err;
    }
    console.warn(
      `[D0-SOLVE] unit ${label} wrote no trustworthy solve artifact after deterministic ` +
        `JSON/TeX normalization; repeating this unit once because the model call itself failed: ${err.message}`,
    );
    // Preserve the failed generation, then clear it before the one permitted
    // mathematical recovery call. No accepted artifact enters a clerical LLM.
    await archiveAndClearRoundFiles("failed-carrier-model-recovery");
    accepted = await attemptUnit(err.message);
  }
  // Phase 3 ingest: content-address every companion block into the proof archive
  // at the moment it enters the pipeline — the companion is a raw round file the
  // next dispatch overwrites, so this is the earliest durable copy. (Read paths
  // like replay never archive; only the live dispatch does.)
  {
    if (accepted.companionBlocks.size > 0) {
      await archiveProofs(
        path.dirname(outPath),
        [...accepted.companionBlocks.entries()].map(([ref, tex]) => ({
          nodeId: `companion:${ref}`,
          proofTex: tex,
          reason: `solve-companion/${label}`,
        })),
      );
    }
  }
  // Bind the validated output to this exact prompt so an uncommitted resume can
  // reuse it without re-paying the model. commitRound deletes all receipts.
  await writeReuseReceipt();
  return accepted.output;
  } finally {
    await pathLease.release();
  }
}

/** Rewrite every statement id a solve unit emitted into the schema's lowercase-kebab
 *  grammar, in place, including the dependency edges and proof ids that reference them.
 *  Mutates `body` before validation; ids already canonical are untouched. */
/** `direction` on a core edit is a function of `kind` (delete kinds are
 *  `delete-obsolete`, every other kind `correct`), so a worker that omits it has
 *  made no decision the orchestrator needs. Fill it deterministically instead of
 *  spending the round on a strict-schema failure. A present value is left alone
 *  so a contradictory one still fails loudly. */
export function healCoreEditDirections(body: unknown): void {
  if (body === null || typeof body !== "object") return;
  const edits = (body as { proposed_core_edits?: unknown }).proposed_core_edits;
  if (!Array.isArray(edits)) return;
  for (const e of edits) {
    if (!e || typeof e !== "object") continue;
    const edit = e as { kind?: unknown; direction?: unknown };
    if (edit.direction !== undefined || typeof edit.kind !== "string") continue;
    edit.direction = edit.kind.endsWith("-delete") ? "delete-obsolete" : "correct";
  }
}

function healSolveUnitIds(body: unknown): void {
  if (body === null || typeof body !== "object") return;
  const b = body as Record<string, unknown>;
  const rename = new Map<string, string>();
  const note = (id: unknown): void => {
    if (typeof id !== "string") return;
    const healed = healStatementId(id);
    if (healed !== null && healed !== id) rename.set(id, healed);
  };
  const stmts = [
    ...(Array.isArray(b.added_lemmas) ? b.added_lemmas : []),
    ...(Array.isArray(b.resolved_oeqs) ? b.resolved_oeqs.map((r) => (r as { theorem?: unknown }).theorem) : []),
  ];
  for (const st of stmts) if (st && typeof st === "object") note((st as { id?: unknown }).id);
  if (rename.size === 0) return;
  const swap = (id: unknown): unknown => (typeof id === "string" ? rename.get(id) ?? id : id);
  for (const st of stmts) {
    if (!st || typeof st !== "object") continue;
    const node = st as { id?: unknown; depends_on?: unknown };
    node.id = swap(node.id);
    if (Array.isArray(node.depends_on)) node.depends_on = node.depends_on.map(swap);
  }
  if (Array.isArray(b.proofs)) {
    for (const pr of b.proofs) if (pr && typeof pr === "object") {
      (pr as { id?: unknown }).id = swap((pr as { id?: unknown }).id);
    }
  }
  // Obligations and prose notes are keyed by statement id too. Renaming the node but not
  // these left an obligation recorded under an id that no longer exists (so the round
  // halts asking for guidance on a ghost node) and a prose note attached to nothing.
  if (Array.isArray(b.open_obligations)) {
    for (const o of b.open_obligations) if (o && typeof o === "object") {
      (o as { node_id?: unknown }).node_id = swap((o as { node_id?: unknown }).node_id);
    }
  }
  const notes = (b.prose_updates as { statement_notes?: unknown } | undefined)?.statement_notes;
  if (Array.isArray(notes)) {
    for (const n of notes) if (n && typeof n === "object") {
      (n as { id?: unknown }).id = swap((n as { id?: unknown }).id);
    }
  }
  if (Array.isArray(b.proposed_core_edits)) {
    for (const e of b.proposed_core_edits) if (e && typeof e === "object") {
      const edit = e as {
        id?: unknown; replacement_id?: unknown;
        proposed?: { id?: unknown; depends_on?: unknown; ref?: unknown; by_member_properties?: unknown };
      };
      edit.id = swap(edit.id);
      // A statement-delete names its successor, and a symbol/definition payload can point
      // at a statement through `ref`/`refs`/`by_member_properties`. Renaming the node but
      // not these left a reference to an id that no longer exists, which the strict solve
      // schema or the apply's closure check then rejects.
      edit.replacement_id = swap(edit.replacement_id);
      if (edit.proposed && typeof edit.proposed === "object") {
        edit.proposed.id = swap(edit.proposed.id);
        if (Array.isArray(edit.proposed.depends_on)) edit.proposed.depends_on = edit.proposed.depends_on.map(swap);
        edit.proposed.ref = swap(edit.proposed.ref);
        // NOT `refs`: on a symbol payload that field holds SYMBOL NAMES, not statement ids,
        // so rewriting it renamed an unrelated symbol that happened to share the spelling.
        if (Array.isArray(edit.proposed.by_member_properties)) {
          edit.proposed.by_member_properties = edit.proposed.by_member_properties.map(swap);
        }
        // NOT `inputs` either. It was added on the reasoning that a definition input can
        // name an emitted statement -- but inputs also carry SYMBOL names, so an
        // unconditional swap repeats exactly the collision just removed from `refs`: a
        // symbol spelled like a healed helper gets silently renamed. Distinguishing the two
        // needs the symbol table, which is not available at this boundary.
      }
    }
  }
  console.warn(
    `[D0-SOLVE] normalised ${rename.size} non-kebab emitted id(s) at the unit boundary: ` +
      `${[...rename].map(([a, c]) => `${a}->${c}`).join(", ")}`,
  );
}

export interface ReadSolveUnitOutputOptions {
  /** Catalog- and caller-dependent acceptance checks. */
  postValidate?: (output: SolveUnitOutput) => void;
  /** Commit the canonical unresolved JSON only after every check passes. Pure by
   * default so replay and diagnostic reads cannot mutate evidence. */
  persistCanonical?: boolean;
  /** Fencing check supplied by live dispatch before destructive publication. */
  assertPersistenceLease?: () => Promise<void>;
  /** Exact companion generation accepted with the JSON; live dispatch archives
   * this snapshot instead of reopening a mutable path after validation. */
  onValidatedSnapshot?: (snapshot: {
    companionBlocks: Map<string, string>;
    companionRaw: string | null;
  }) => void;
}

/** Solve-unit ingest: raw-byte normalization → JSON.parse → LaTeX repair →
 * control-char assert → id heal → strict schema.  Parsing is pure unless the live
 * dispatcher explicitly requests a canonical commit after its catalog checks. */
export async function readSolveUnitOutput(
  outPath: string,
  label: string,
  options: ReadSolveUnitOutputOptions = {},
): Promise<SolveUnitOutput> {
  if (!existsSync(outPath)) {
    throw new Error(`Stage 0-SOLVE unit ${label} completed without writing ${outPath}`);
  }
  try {
    // Pre-parse raw-byte normalization: an under-escaped TeX backslash (`\theta`)
    // is only distinguishable from an intended control escape BEFORE JSON.parse
    // destroys the information. The post-parse repair below stays as legacy cover.
    const raw = await readFile(outPath, "utf8");
    const companionPath = companionPathFor(outPath);
    const companionRawAtStart = existsSync(companionPath)
      ? await readFile(companionPath, "utf8")
      : null;
    const normalizedRaw = normalizeRawModelJson(raw);
    const body = JSON.parse(normalizedRaw);
    normalizeEmptySolveUnitContainers(body);
    repairSolveUnitLatexSerialization(body);
    assertNoDecodedControlChars(body, `Stage 0-SOLVE unit ${label} output`);
    // Persist the accepted unresolved representation, so every post-parse
    // normalization is durable while companion-backed TeX remains a tex_ref.
    healSolveUnitIds(body);
    healCoreEditDirections(body);
    const canonicalRaw = `${JSON.stringify(body, null, 2)}\n`;
    const validationBody = structuredClone(body);
    // Phase 3 (TeX-out-of-JSON): resolve `{"tex_ref": ...}` fields from the raw
    // companion file AFTER the JSON-channel defenses above — companion bytes are
    // never JSON-decoded, so the escaping class cannot occur in them and they
    // must not be "repaired". Missing/duplicate refs fail loud here, before any
    // store is touched. Inline strings remain valid indefinitely (no companion,
    // no refs → no-op). Read-only: archiving the blocks is the DISPATCH flow's
    // job (`archiveSolveCompanion`), so replay can call this on real files.
    const companionBlocks = companionRawAtStart !== null
      ? sliceTexCompanion(companionRawAtStart, companionPath)
      : new Map<string, string>();
    {
      const used = resolveTexRefs(validationBody, companionBlocks, companionPath);
      // UNUSED blocks fail loud too (audit P23F2): a header-lookalike line
      // inside a block silently TRUNCATES the field and strands the remainder
      // as an extra block — strictness here converts that silent corruption
      // into a re-dispatchable error.
      const unused = [...companionBlocks.keys()].filter((ref) => !used.has(ref));
      if (unused.length > 0) {
        throw new Error(
          `TeX companion ${companionPath} has block(s) no tex_ref cites: ${unused.join(", ")} — ` +
            "either the JSON forgot a ref or a '%%% FIELD' look-alike line inside a block mis-sliced it",
        );
      }
    }
    // NORMALISE IDS FIRST. The schema's id grammar is lowercase-kebab, and a solver
    // reliably names a helper after a capital-letter symbol (`lem:Ghat-envelope` for an
    // estimator Ĝ). A downstream auto-heal exists for exactly that — but it ran over
    // core.statements, which are already schema-validated, so it could never fire: the
    // strict parse below rejected the payload first and the ENTIRE round was lost as
    // "invalid solve JSON". Heal at the input boundary so the heal is reachable and a
    // capitalised id costs a rename instead of a round.
    healSolveUnitIds(validationBody);
    // Validate solve-unit item shapes and every nested TeX string at the same
    // D-orchestration boundary. Mechanical delimiter/environment defects are
    // repaired without another mathematical model call.
    const parsed = SolveUnitOutputSchema.parse(validationBody);
    assertSealableLatexPayload(parsed, `Stage 0-SOLVE unit ${label} output`);
    options.postValidate?.(parsed);

    // PASS is a persistence contract: leave standards-compliant JSON whose
    // unresolved AST matches the value accepted above. Detect replacement of
    // either the JSON or companion generation while validation is in flight,
    // then fsync a private temp file and atomically rename it so a crash or reader
    // cannot observe an in-place truncation.
    // A canonical JSON generation may reference companion bytes, so make that
    // dependency durable first; publication order is companion -> JSON.
    if (options.persistCanonical === true && companionRawAtStart !== null) {
      await options.assertPersistenceLease?.();
      const companionHandle = await open(companionPath, "r");
      try {
        await companionHandle.sync();
      } finally {
        await companionHandle.close();
      }
      await syncDirectory(path.dirname(companionPath));
    }
    if (options.persistCanonical === true && canonicalRaw !== raw) {
      await options.assertPersistenceLease?.();
      if (await readFile(outPath, "utf8") !== raw) {
        throw new Error(
          `solve output generation changed during validation for ${outPath}; refusing to overwrite newer bytes`,
        );
      }
      const staged = `${outPath}.canonical-${process.pid}-${randomUUID()}`;
      try {
        const handle = await open(staged, "wx");
        try {
          await handle.writeFile(canonicalRaw, "utf8");
          await handle.sync();
        } finally {
          await handle.close();
        }
        const beforeRenameRaw = await readFile(outPath, "utf8");
        const beforeRenameCompanion = existsSync(companionPath)
          ? await readFile(companionPath, "utf8")
          : null;
        if (beforeRenameRaw !== raw || beforeRenameCompanion !== companionRawAtStart) {
          throw new Error(
            `solve output generation changed before canonical commit for ${outPath}; refusing to persist a mixed JSON/companion generation`,
          );
        }
        await options.assertPersistenceLease?.();
        await rename(staged, outPath);
        // rename durability requires the parent directory entry to reach disk.
        // Some platforms/filesystems reject directory fsync; only those explicit
        // unsupported cases are tolerated.
        await syncDirectory(path.dirname(outPath));
      } finally {
        await rm(staged, { force: true });
      }
    }
    if (options.persistCanonical === true && canonicalRaw === raw) {
      await options.assertPersistenceLease?.();
      const acceptedHandle = await open(outPath, "r");
      try {
        await acceptedHandle.sync();
      } finally {
        await acceptedHandle.close();
      }
      // The worker created this pathname after dispatch removed the prior
      // generation, so the directory entry itself must also be durable.
      await syncDirectory(path.dirname(outPath));
    }
    // Even when canonical bytes already match (or this is a pure read), never
    // return a hybrid generation or hand dispatch a stale companion snapshot.
    const finalRaw = await readFile(outPath, "utf8");
    const finalCompanion = existsSync(companionPath)
      ? await readFile(companionPath, "utf8")
      : null;
    const expectedRaw = options.persistCanonical === true && canonicalRaw !== raw
      ? canonicalRaw
      : raw;
    if (finalRaw !== expectedRaw || finalCompanion !== companionRawAtStart) {
      throw new Error(
        `solve output generation changed before validation returned for ${outPath}; refusing a mixed JSON/companion generation`,
      );
    }
    if (options.persistCanonical === true) await options.assertPersistenceLease?.();
    options.onValidatedSnapshot?.({
      companionBlocks: new Map(companionBlocks),
      companionRaw: companionRawAtStart,
    });
    return parsed;
  } catch (err) {
    const message = `Stage 0-SOLVE unit ${label} wrote invalid solve JSON at ${outPath}: ${err instanceof Error ? err.message : String(err)}`;
    throw isCarrierDefect(err) ? new SolveUnitCarrierError(message, { cause: err }) : new Error(message, { cause: err });
  }
}

/** Partition to-prove statements into weakly-connected components of their mutual
 *  dependency graph. Only an edge between two TO-PROVE statements couples them — a
 *  `depends_on` reference to an already-proved statement, an assumption, or a
 *  definition is stable frozen context, not a reconciliation hazard. Each component
 *  becomes one solver unit; its label is the component's lead headline (`theorem`/
 *  `conjecture`), or its first member when the component is props/lemmas only. */
export function groupToProveByComponent(
  toProve: CoreStatement[],
): Array<{ targets: CoreStatement[]; label: string }> {
  const order = new Map(toProve.map((s, i) => [s.id, i]));
  const idSet = new Set(toProve.map((s) => s.id));
  const parent = new Map(toProve.map((s) => [s.id, s.id]));
  const find = (x: string): string => {
    let r = x;
    while (parent.get(r) !== r) r = parent.get(r)!;
    let c = x;
    while (parent.get(c) !== r) {
      const nxt = parent.get(c)!;
      parent.set(c, r);
      c = nxt;
    }
    return r;
  };
  const union = (a: string, b: string): void => {
    parent.set(find(a), find(b));
  };
  for (const s of toProve) {
    for (const d of s.depends_on ?? []) {
      if (idSet.has(d)) union(s.id, d);
    }
  }
  const byRoot = new Map<string, CoreStatement[]>();
  for (const s of toProve) {
    const r = find(s.id);
    const bucket = byRoot.get(r) ?? [];
    bucket.push(s);
    byRoot.set(r, bucket);
  }
  const comps = [...byRoot.values()];
  for (const c of comps) c.sort((a, b) => order.get(a.id)! - order.get(b.id)!);
  comps.sort((a, b) => order.get(a[0].id)! - order.get(b[0].id)!);
  return comps.map((targets) => {
    // Choose the lead by CONTENT, never by array position. `find` returned the first
    // headline in SOURCE order, so two semantically identical cores that happened to list
    // their statements differently elected different unit labels — and the label decides
    // ownership, so a reorder alone could move who is allowed to emit what.
    // `selectDirectiveEmissionOwnerLabel` already holds this discipline; this did not.
    const HEADLINE_RANK: Record<string, number> = {
      theorem: 3, openendedquestion: 2, conjecture: 1,
    };
    const lead =
      [...targets].sort((a, b) => {
        const byKind = (HEADLINE_RANK[b.kind] ?? 0) - (HEADLINE_RANK[a.kind] ?? 0);
        if (byKind !== 0) return byKind;
        return a.id.localeCompare(b.id); // stable tie-break independent of input order
      })[0] ?? targets[0];
    return { targets, label: lead.id };
  });
}

export interface SolveDispatchResult {
  dispatch: SolveDispatchUnit[];
  rawOutputs: SolveUnitOutput[];
  proseOwnerIndex: number | null;
  directiveOwnerLabel: string | null;
  semanticTargetOwners: Map<string, string>;
  /** When present, this was the sole unit dispatched in the staged pass and is
   * the canonical writer for its explicit shared targets. */
  sharedUpstreamLabel?: string | null;
  /** Explicit directive ids for which the staged upstream has strict authority. */
  sharedTargetIds?: string[];
}

export interface StagedSolveDispatchPlan {
  ordered: SolveDispatchUnit[];
  upstream: SolveDispatchUnit | null;
  downstream: SolveDispatchUnit[];
  sharedTargetIds: string[];
}

/** Stage exactly ONE existing unit for a purely shared exact directive bundle.
 * Open/writable overlap was already collapsed by WCC; settled shared reads are
 * immutable context and must not serialize an ordinary cold solve. We deliberately
 * do not create one coordinator per pair: with A/B/C that recreates overlap.
 *
 * The selected unit keeps its ordinary target work and is the entire current
 * dispatch. Downstream units are not called speculatively; they re-enter on a
 * later D0 pass only after this postimage has merged and been accepted. */
export function planStagedSolveDispatch(args: {
  dispatch: SolveDispatchUnit[];
  hasPendingDirective: boolean;
  requiredCoreTargets: ReadonlySet<string>;
}): StagedSolveDispatchPlan {
  const { dispatch } = args;
  if (dispatch.length < 2) {
    return { ordered: dispatch, upstream: null, downstream: dispatch, sharedTargetIds: [] };
  }
  const targetOwners = new Map<string, Set<string>>();
  for (const unit of dispatch) {
    for (const target of unit.targets) {
      const labels = targetOwners.get(target.id) ?? new Set<string>();
      labels.add(unit.label);
      targetOwners.set(target.id, labels);
    }
  }
  // A required statement with exactly one component owner is local, even when
  // several targets appear in the directive. Only new/catalog/contested ids lack
  // one semantic owner and therefore require the global writer.
  const sharedTargetIds = [...args.requiredCoreTargets]
    .filter((id) => (targetOwners.get(id)?.size ?? 0) !== 1)
    .sort();
  const localRequiredIds = [...args.requiredCoreTargets]
    .filter((id) => (targetOwners.get(id)?.size ?? 0) === 1);
  // Stage only a purely shared exact bundle. Broad directives have no stable
  // predeclared shared partition, and a mixed shared+local exact bundle is one
  // atomic obligation under the existing gate; both retain parallel dispatch
  // plus deterministic conflict withholding rather than inventing sliced state.
  const needsStagedOwner = args.hasPendingDirective &&
    sharedTargetIds.length > 0 && localRequiredIds.length === 0;
  if (!needsStagedOwner) {
    return { ordered: dispatch, upstream: null, downstream: dispatch, sharedTargetIds: [] };
  }
  // Prefer a unit actually solving an explicit shared target. A stable fallback
  // covers paper-wide directives whose target is catalog/prose rather than a
  // statement in the open frontier.
  const targetReaders = dispatch.filter((unit) =>
    unit.targets.some((target) => sharedTargetIds.includes(target.id))
  );
  const upstreamLabel = selectDirectiveEmissionOwnerLabel(targetReaders.length > 0 ? targetReaders : dispatch);
  const upstream = dispatch.find((unit) => unit.label === upstreamLabel) ?? null;
  if (upstream === null) {
    return { ordered: dispatch, upstream: null, downstream: dispatch, sharedTargetIds };
  }
  const downstream = dispatch.filter((unit) => unit !== upstream);
  return {
    ordered: [upstream, ...downstream],
    upstream,
    downstream,
    sharedTargetIds,
  };
}

export async function dispatchSolveUnits(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  sctx: SolveRoundContext;
}): Promise<SolveDispatchResult> {
  const { ctx, state, deps, sctx } = args;
  const {
    proto,
    core,
    prev,
    next,
    validIds,
    persistedOeqReplacements,
    staleAgentTargets,
    hasPendingDirective,
    requiredCoreTargets,
    escContext,
    clusterSetupBlock,
  } = sctx;
  // One agent per weakly-connected component of the OPEN spec statements. Coupling
  // edges run only through open (still-changeable) statements, so consumers connected
  // ONLY through a now-valid node split into separate groups and parallelize.
  // Pruned proto orphans are not part of the frontier (audit R2F3): the proto
  // still defines them, but the durable prune record excludes them from the
  // paper, so dispatching one as an ordinary open member would re-pay for a
  // node nothing references and "revive" it. An exact-target directive naming
  // one was already removed from the list by the context carry.
  const prunedOrphans = new Set(sctx.next.pruned_proto_orphans ?? []);
  const sealedOpenOeqs = new Set(Object.keys(sctx.next.sealed_open_oeqs ?? {}));
  const openById = new Map<string, CoreStatement>();
  for (const statement of [
    ...proto.statements.filter(
      (m) => !validIds.has(m.id) && !persistedOeqReplacements.has(m.id) &&
        !prunedOrphans.has(m.id) && !sealedOpenOeqs.has(m.id),
    ),
    ...staleAgentTargets.filter((m) => !sealedOpenOeqs.has(m.id)),
  ]) openById.set(statement.id, statement);
  if (hasPendingDirective) {
    const forcedIds = requiredCoreTargets.size > 0
      ? [...requiredCoreTargets]
      : core.statements.map((statement) => statement.id);
    const statementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
    for (const id of forcedIds) {
      // A broad directive revalidates the paper, but an acknowledged residual OEQ
      // already sealed at its current source is not active theorem work.  An exact
      // target intentionally naming the OEQ removed its seal in context assembly,
      // so this guard does not suppress explicit reopening.
      if (sealedOpenOeqs.has(id) && !requiredCoreTargets.has(id)) continue;
      // A resolved agent-authored OEQ is absent from assembled `core` by design, but
      // its canonical source may be rehydrated in sourceById so a directed repair can
      // assign the answer theorem to the semantic OEQ owner without reopening it.
      const statement = statementById.get(id) ?? sctx.sourceById.get(id);
      if (!statement) continue; // a genuinely new required node must be emitted as an addition.
      if (!statementById.has(id) && persistedOeqReplacements.has(id)) {
        // Merge validates and fingerprints a resolution against the assembled source,
        // then removes it again. Temporarily restore only this explicitly forced,
        // already-resolved source; it never survives the round as an open node.
        const opened = openSolveTarget(statement);
        core.statements.push(opened);
        statementById.set(id, opened);
      }
      openById.set(id, openSolveTarget(statement));
    }
  }
  const openStmts = [...openById.values()];
  let groups = groupToProveByComponent(openStmts);
  // A directed round with exact statement targets pays ONLY for the components
  // the directive names — an open dependency of a named target shares its
  // component by WCC construction, so nothing a directed repair needs is lost.
  // Unrelated open components used to be re-dispatched (and re-paid) on every
  // repair round even though a blind re-solve of a stuck component rarely closes
  // it (the skill routes those through directives; exp_two_wave re-paid one
  // unrelated unit 11x this way). Deferred components stay open and are solved
  // by an undirected round or a directive that names them. A catalog-only
  // directive (def:/sym:/metadata/ass: targets, no statement ids) keeps the full
  // dispatch: its writers are the statement units consuming the catalog object,
  // which the target list does not identify.
  if (hasPendingDirective && requiredCoreTargets.size > 0) {
    const directiveIds = new Set([
      ...requiredCoreTargets,
      ...sctx.requiredCoreEdits.map((edit) => coreEditTarget(edit)),
    ]);
    const scoped = groups.filter((group) => group.targets.some((target) => directiveIds.has(target.id)));
    if (scoped.length > 0 && scoped.length < groups.length) {
      const deferred = groups.filter((group) => !scoped.includes(group)).map((group) => group.label);
      console.warn(
        `[D0-SOLVE] exact-target directive: dispatching ${scoped.length}/${groups.length} open component(s); ` +
          `deferring unrelated open component(s) to an undirected round: ${deferred.join(", ")}.`,
      );
      groups = scoped;
    }
  }
  let dispatch: SolveDispatchUnit[] = [];
  for (const g of groups) {
    // Established nodes are already present with their statements and revisions in
    // the projected upstream closure. A compact receipt is enough to authorize
    // citation; repeating complete proof bodies makes every later turn repay for
    // mathematics this unit is explicitly told not to re-derive.
    const openDeps = new Set(g.targets.flatMap((m) => m.depends_on ?? []));
    const targetIds = new Set(g.targets.map((m) => m.id));
    const established = [...openDeps]
      // A directed repair can force an otherwise-valid dependency back onto the
      // target frontier. Never tell the worker that the same node is both owed and
      // established/do-not-rederive; that contradictory I/O previously caused a
      // requested proof replacement to be copied through unchanged.
      .filter((id) => !targetIds.has(id) && next.solved[id] !== undefined && !next.solved[id].partial)
      .map((id) => `- ${id} (proved; cite the frozen statement above)`);
    const priorTargetProofs = g.targets
      .filter((m) => next.solved[m.id] !== undefined && !next.solved[m.id].partial)
      .map((m) => `- ${m.id}: ${next.solved[m.id].proof_tex}`);
    // Prior PARTIAL progress on this group's open targets (from a previous round): the
    // agent must EXTEND it, not restart — this is what makes the iteration accumulate.
    // A partial whose snapshot records a DIFFERENT statement text than the current
    // target argued a previous form of the claim (its bytes survive a statement change
    // as the repair basis). Say so, and show which text it argued — otherwise the agent
    // extends a stale argument past the change instead of realigning it.
    const partials = g.targets
      .filter((m) => prev?.solved[m.id]?.partial && (prev.solved[m.id].proof_tex ?? "").trim().length > 0)
      .map((m) => {
        const rec = prev!.solved[m.id];
        const staleBasis = rec.snapshot?.stmt !== undefined && rec.snapshot.stmt !== m.statement
          ? ` [this partial argued a PREVIOUS statement of ${m.id} — "${rec.snapshot.stmt}" — which has since ` +
            `changed; REALIGN the argument to the current statement, dropping any step that relied on the old form]`
          : "";
        return `- ${m.id}:${staleBasis} ${rec.proof_tex}`;
      });
    const body = [
      escContext,
      established.length > 0
        ? "=== ALREADY-ESTABLISHED RECEIPTS (still valid — cite for REUSE, do NOT re-derive) ===\n" + established.join("\n")
        : "",
      priorTargetProofs.length > 0
        ? "=== PRIOR PROOF OF A DIRECTED TARGET (revise/replace it; it is NOT established for this round) ===\n" + priorTargetProofs.join("\n\n")
        : "",
      partials.length > 0
        ? "=== PRIOR PARTIAL PROGRESS on your targets (EXTEND this, do NOT restart; prove the residual on top of it) ===\n" + partials.join("\n\n")
        : "",
    ].filter((x) => x.trim().length > 0);
    // The context below is REUSE background; it must not shrink the work. The agent
    // still owes a proof OR a proposed change for EVERY listed target.
    const priorContext =
      body.length > 0
        ? [
            "=== PRIOR-ROUND CONTEXT (reuse only — does NOT reduce your TARGET list below; " +
              "you still owe a proof or a proposed change for EVERY target) ===",
            ...body,
          ].join("\n\n")
        : "";
    dispatch.push({ targets: g.targets, label: g.label, priorContext });
  }

  // A sealed exact edit is already a complete, basis-checked mechanical action.
  // D-orchestration applies it directly; paying a solver to echo it adds no
  // mathematical judgment and used to create same-target noise. Free-text or
  // target-only directives still need one worker to author the missing payload.
  if (hasPendingDirective && dispatch.length === 0 && sctx.requiredCoreEdits.length === 0) {
    dispatch.push({
      targets: [],
      label: "directive:structured-metadata",
      priorContext: escContext,
    });
  } else if (hasPendingDirective && dispatch.length === 0) {
    console.warn(
      `[D0-SOLVE] applying ${sctx.requiredCoreEdits.length} sealed mechanical core edit(s) ` +
        "through D-orchestration; no solver call is needed.",
    );
  }

  const statementCatalog = new Map(core.statements.map((statement) => [statement.id, statement] as const));
  for (const records of [next.solved, prev?.solved ?? {}]) {
    for (const record of Object.values(records)) {
      if (record.node !== undefined && !statementCatalog.has(record.node.id)) {
        statementCatalog.set(record.node.id, record.node);
      }
    }
  }

  // For a purely shared exact directive bundle, stage one existing component —
  // never one owner per pair — as the only unit in this pass. Broad and mixed
  // directives keep ordinary parallel dispatch and deterministic withholding.
  const stagedPlan = planStagedSolveDispatch({
    dispatch,
    hasPendingDirective,
    requiredCoreTargets,
  });
  // A shared producer's schema-valid output is not yet an accepted mathematical
  // basis. Run and commit/checkpoint that one unit alone; the deferred components
  // re-enter on the next D0 pass and see its carried, merge-checked postimage.
  // This avoids both a provisional-merge subsystem and speculative downstream calls.
  if (stagedPlan.upstream !== null) {
    console.warn(
      `[D0-SOLVE] staging shared directive owner '${stagedPlan.upstream.label}' alone; ` +
        `${stagedPlan.downstream.length} downstream component(s) defer until its accepted postimage is carried.`,
    );
    dispatch = [stagedPlan.upstream];
  } else {
    dispatch = stagedPlan.ordered;
  }

  // The staged upstream owns all explicit shared/catalog writes. An ordinary
  // single-unit directed pass keeps its direct owner without creating staging.
  const directiveOwnerLabel = stagedPlan.upstream?.label ?? (hasPendingDirective
    ? selectDirectiveEmissionOwnerLabel(dispatch)
    : null);
  const semanticTargetOwners = hasPendingDirective || stagedPlan.upstream !== null
    ? selectSemanticTargetOwners(dispatch)
    : new Map<string, string>();
  const semanticTargetEntries = [...semanticTargetOwners.entries()]
    .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
  const proseOwnerIndex = !hasPendingDirective || directiveOwnerLabel === null
    ? null
    : dispatch.findIndex((unit) => unit.label === directiveOwnerLabel);

  if (dispatch.length === 0) {
    return {
      dispatch, rawOutputs: [], proseOwnerIndex, directiveOwnerLabel, semanticTargetOwners,
      sharedUpstreamLabel: null,
      sharedTargetIds: stagedPlan.sharedTargetIds,
    };
  }

  // Publish one immutable, content-addressed snapshot before parallel dispatch.
  // Every unit sees the exact same round even if a prior canonical core.json is
  // concurrently replaced later at commit.
  const coreSnapshot = await publishFrozenCoreSnapshot(ctx, core);
  const runUnit = (
    u: SolveDispatchUnit,
    i: number,
  ): Promise<SolveUnitOutput> => solveUnit({
        ctx,
        state,
        deps,
        core,
        statementCatalog: [...statementCatalog.values()],
        targets: u.targets,
        label: u.label,
        clusterSetupBlock,
        priorContext: u.priorContext,
        proseRole: proseOwnerIndex === null ? "none" : i === proseOwnerIndex ? "owner" : "omit",
        directiveEmissionRole: directiveOwnerLabel === null
          ? "none"
          : u.label === directiveOwnerLabel ? "owner" : "local",
        requiredCoreTargets: [...requiredCoreTargets].sort(),
        requiredCoreEdits: sctx.requiredCoreEdits,
        ownedSemanticTargets: semanticTargetEntries
          .filter(([, owner]) => owner === u.label)
          .map(([id]) => id),
        siblingSemanticTargets: semanticTargetEntries
          .filter(([, owner]) => owner !== u.label)
          .map(([id, owner]) => ({ id, owner })),
        coreSnapshotPath: coreSnapshot.path,
        sharedTargetIds: stagedPlan.sharedTargetIds,
      });

  const assertSnapshotUnchanged = async (): Promise<void> => {
    if (await readFile(coreSnapshot.path, "utf8") !== coreSnapshot.bytes) {
      throw new Error(`D0 solver modified immutable frozen-core snapshot ${coreSnapshot.path}`);
    }
  };

  let rawOutputs: SolveUnitOutput[];
  if (stagedPlan.upstream !== null) {
    // Phase 1 commits/checkpoints alone. Downstream is intentionally absent from
    // this dispatch result, so merge cannot mistake uncalled units for omissions.
    const upstreamOutput = await runUnit(dispatch[0], 0);
    await assertSnapshotUnchanged();
    rawOutputs = [upstreamOutput];
  } else {
    // Independent components still fan out together. Drain every worker before
    // returning so stable output paths cannot overlap a resumed round.
    const settledOutputs = await Promise.allSettled(
      dispatch.map((unit, index) => runUnit(unit, index)),
    );
    await assertSnapshotUnchanged();
    const firstRejected = settledOutputs.find(
      (result): result is PromiseRejectedResult => result.status === "rejected",
    );
    if (firstRejected !== undefined) throw firstRejected.reason;
    rawOutputs = settledOutputs.map((result) =>
      (result as PromiseFulfilledResult<SolveUnitOutput>).value
    );
  }
  // The snapshot is a read-only input contract. Detect an accidental worker edit
  // before accepting any output from the round.
  await assertSnapshotUnchanged();
  return {
    dispatch,
    rawOutputs,
    proseOwnerIndex,
    directiveOwnerLabel,
    semanticTargetOwners,
    sharedUpstreamLabel: stagedPlan.upstream?.label ?? null,
    sharedTargetIds: stagedPlan.sharedTargetIds,
  };
}
