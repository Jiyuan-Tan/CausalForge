/**
 * Phase 3 — Post-Stage-5 hook: close an OpenQuestion by minting a
 * BankedTheorem node and the `closes` edge.
 *
 * Wrapped in `withGraphWriteLock` (spec §15.2). Atomic node writes via
 * tempfile + rename so a partial failure leaves the graph consistent:
 *   - BankedTheorem write fails → no edge added, OQ untouched.
 *   - BankedTheorem written but OQ update fails → recovery file describes
 *     the in-flight transaction; index.json is rebuilt from the post-state.
 *
 * Recovery file format (written next to `nodes/` on partial failure):
 *   {
 *     "phase": "after_bt_write" | "after_oq_update",
 *     "bt_id": "...",
 *     "oq_id": "...",
 *     "qid": "...",
 *     "spec": "...",
 *     "timestamp": "ISO-8601"
 *   }
 *
 * Future revisions can ship `close_oq.ts --resume <recovery_file>` to
 * complete an interrupted transaction.
 */
import path from "node:path";
import { existsSync, readFileSync } from "node:fs";
import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import {
  buildIndex,
  loadAllNodes,
  writeIndexAtomic,
} from "./graph.js";
import { withGraphWriteLock } from "./graph_lock.js";
import type { BankedTheorem, OpenQuestion } from "./kb_types.js";

// ---------------------------------------------------------------------------
// Typed errors
// ---------------------------------------------------------------------------

export class OpenQuestionNotInProgress extends Error {
  constructor(public oq_id: string, public observedStatus: string) {
    super(
      `OpenQuestion ${oq_id} has status=${observedStatus}; expected "in_progress" before close.`,
    );
    this.name = "OpenQuestionNotInProgress";
  }
}

export class BankedTheoremAlreadyExists extends Error {
  constructor(public bt_id: string, public path: string) {
    super(
      `BankedTheorem ${bt_id} already exists at ${path}; refusing to overwrite (Phase 3 has no --force).`,
    );
    this.name = "BankedTheoremAlreadyExists";
  }
}

export class BankedTheoremConflict extends Error {
  constructor(public bt_id: string, public path: string) {
    super(
      `BankedTheorem ${bt_id} already exists at ${path} with different close provenance; refusing idempotent reuse.`,
    );
    this.name = "BankedTheoremConflict";
  }
}

export class OpenQuestionMissing extends Error {
  constructor(public oq_id: string, public path: string) {
    super(`OpenQuestion ${oq_id} not found at ${path}`);
    this.name = "OpenQuestionMissing";
  }
}

export class GraphLockTimeout extends Error {
  constructor(public cause?: unknown) {
    super(
      `Could not acquire the graph write lock within the configured retry budget (60s + 10 retries). Wait or stop the other writer.`,
    );
    this.name = "GraphLockTimeout";
  }
}

export class PaperHasNoCompletedTheorems extends Error {
  constructor(public qid: string) {
    super(
      `Paper-scoped closeOpenQuestion for qid=${qid}: all theorems are stuck/failed. ` +
      `No BankedTheorem written; OQ left in_progress for Stage 7 reroute or manual retry.`,
    );
    this.name = "PaperHasNoCompletedTheorems";
  }
}

/**
 * Paper-scoped no-OQ banking: mint one BankedTheorem per completed entry
 * without touching an OpenQuestion node. Used by the post-Stage-5 close hook
 * when the run was launched by the study-pipeline paper_dispatcher (no `--from-question`
 * OQ to close — the dispatch is keyed on the parent Insight directly).
 *
 * The semantic difference from `closeOpenQuestionPaperScoped`:
 *   - Source of derivation is the parent Insight id (`derived_from`), not an OQ.
 *   - No `closes` edge — nothing is being closed.
 *   - No OQ-status flip; therefore no recovery record machinery needed for the
 *     OQ side (BT writes are still individually atomic via tempfile + rename).
 *
 * Idempotent: pre-existing `<bt_id>.json` files are reused, not overwritten.
 * Throws `PaperHasNoCompletedTheorems` when zero entries have status="completed"
 * — the caller logs and leaves the run dir in place (study-pipeline S5 then mints
 * failure-Notes).
 */
export interface MintPaperScopedBTInput {
  qid: string;
  spec: string;
  /** Parent Insight id (study graph node) the theorems were extracted from. */
  derived_from_insight_id: string;
  bankMetadata: {
    instantiates: string[];
    uses: string[];
  };
  theorems: Array<CloseTheoremEntry & {
    status: "pending" | "in_progress" | "completed" | "stuck" | "failed";
  }>;
}

export interface MintPaperScopedBTResult {
  bt_ids: string[];
  banked_theorem_paths: string[];
}

export async function mintPaperScopedBankedTheoremsNoOq(
  input: MintPaperScopedBTInput,
  opts: CloseOpenQuestionOpts = {},
): Promise<MintPaperScopedBTResult> {
  const graphRoot = opts.graphRoot ?? defaultGraphRoot();
  const completed = input.theorems.filter((t) => t.status === "completed");

  try {
    return await withGraphWriteLock(graphRoot, async () => {
      const btDir = path.join(graphRoot, "nodes", "banked_theorem");
      await mkdir(btDir, { recursive: true });

      const writtenBtIds: string[] = [];
      const writtenBtPaths: string[] = [];
      for (const t of completed) {
        const bt_id = `${input.qid}_${t.local_id}_${input.spec}`;
        const btPath = path.join(btDir, `${bt_id}.json`);
        if (existsSync(btPath)) {
          // Idempotent: keep prior write.
          writtenBtIds.push(bt_id);
          writtenBtPaths.push(btPath);
          continue;
        }
        const bt: BankedTheorem = {
          schema_version: 2,
          bt_id,
          qid: input.qid,
          spec: input.spec,
          instantiates: input.bankMetadata.instantiates ?? [],
          uses: input.bankMetadata.uses ?? [],
          derived_from: input.derived_from_insight_id,
        };
        await writeAtomic(btPath, jsonStable(bt));
        writtenBtIds.push(bt_id);
        writtenBtPaths.push(btPath);
      }

      if (writtenBtIds.length === 0) {
        throw new PaperHasNoCompletedTheorems(input.qid);
      }

      // Rebuild index once after all writes.
      const nodes = await loadAllNodes(graphRoot);
      await writeIndexAtomic(graphRoot, buildIndex(nodes));

      return { bt_ids: writtenBtIds, banked_theorem_paths: writtenBtPaths };
    });
  } catch (err: unknown) {
    if (isLockError(err)) throw new GraphLockTimeout(err);
    throw err;
  }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/**
 * Per-theorem entry for paper-scoped close input (Option 2 extension).
 * When `CloseOpenQuestionInput.theorems` is non-empty, `closeOpenQuestion`
 * writes N BankedTheorems (one per completed entry) instead of a single one.
 */
export interface CloseTheoremEntry {
  /** Stable per-paper handle matching TheoremEntry.theorem_local_id, e.g. "t1". */
  local_id: string;
  /** Lean declaration name for this theorem, e.g. "t1_thm". */
  lean_decl_name?: string;
  /** Full NL statement for this theorem. */
  statement: string;
}

export interface CloseOpenQuestionInput {
  qid: string;
  spec: string;
  oq_id: string;
  bankMetadata: {
    instantiates: string[];
    uses: string[];
    title?: string;
  };
  /**
   * Paper-scoped mode: when non-empty, `closeOpenQuestion` writes one
   * BankedTheorem per completed entry (bt_id = `<qid>_<local_id>_<spec>`)
   * instead of a single BankedTheorem (bt_id = `<qid>_<spec>`).
   * All entries are attempted; only `status === "completed"` ones are banked.
   * This field is additive and backward compatible — legacy callers omit it.
   */
  theorems?: Array<CloseTheoremEntry & { status: "pending" | "in_progress" | "completed" | "stuck" | "failed" }>;
}

export interface CloseOpenQuestionResult {
  bt_id: string;
  banked_theorem_path: string;
  open_question_path: string;
  index_rebuilt: boolean;
  /**
   * Paper-scoped mode only: bt_ids for every BankedTheorem successfully
   * written. Empty for legacy single-theorem mode.
   */
  all_bt_ids: string[];
}

export interface CloseOpenQuestionOpts {
  graphRoot?: string;
}

export async function closeOpenQuestion(
  input: CloseOpenQuestionInput,
  opts: CloseOpenQuestionOpts = {},
): Promise<CloseOpenQuestionResult> {
  const graphRoot = opts.graphRoot ?? defaultGraphRoot();

  // Paper-scoped mode: input.theorems is non-empty — write N BankedTheorems.
  const paperTheorems = input.theorems && input.theorems.length > 0 ? input.theorems : null;

  if (paperTheorems) {
    return closeOpenQuestionPaperScoped(input, graphRoot, paperTheorems);
  }

  // -----------------------------------------------------------------------
  // Legacy single-theorem path (unchanged).
  // -----------------------------------------------------------------------
  const bt_id = `${input.qid}_${input.spec}`;
  const btPath = path.join(graphRoot, "nodes", "banked_theorem", `${bt_id}.json`);
  const oqPath = path.join(graphRoot, "nodes", "open_question", `${input.oq_id}.json`);

  try {
    return await withGraphWriteLock(graphRoot, async () => {
      // 1. Validate preconditions.
      if (!existsSync(oqPath)) {
        throw new OpenQuestionMissing(input.oq_id, oqPath);
      }
      if (existsSync(btPath)) {
        throw new BankedTheoremAlreadyExists(bt_id, btPath);
      }
      const oq = JSON.parse(await readFile(oqPath, "utf8")) as OpenQuestion;
      const observedStatus = stringifyStatus(oq.status);
      if (observedStatus !== "in_progress") {
        throw new OpenQuestionNotInProgress(input.oq_id, observedStatus);
      }

      // 2. Build BankedTheorem node.
      const bt: BankedTheorem = {
        schema_version: 2,
        bt_id,
        qid: input.qid,
        spec: input.spec,
        instantiates: input.bankMetadata.instantiates ?? [],
        uses: input.bankMetadata.uses ?? [],
        derived_from: input.oq_id,
        closes: [input.oq_id],
      };

      // 3. Atomic write BankedTheorem.
      await mkdir(path.dirname(btPath), { recursive: true });
      await writeAtomic(btPath, jsonStable(bt));

      // 4. Update OpenQuestion status atomically. Recovery file is left in
      //    `<graphRoot>/_recovery/` on any failure between BT write and OQ
      //    rename so a future `close_oq.ts --resume` can finish.
      const updatedOq = { ...oq, status: { closed_by: bt_id } as const };
      try {
        await writeAtomic(oqPath, jsonStable(updatedOq));
      } catch (err) {
        await writeRecoveryRecord(graphRoot, {
          phase: "after_bt_write",
          bt_id,
          oq_id: input.oq_id,
          qid: input.qid,
          spec: input.spec,
          timestamp: new Date().toISOString(),
        });
        throw err;
      }

      // 5. Rebuild index.
      try {
        const nodes = await loadAllNodes(graphRoot);
        await writeIndexAtomic(graphRoot, buildIndex(nodes));
      } catch (err) {
        await writeRecoveryRecord(graphRoot, {
          phase: "after_oq_update",
          bt_id,
          oq_id: input.oq_id,
          qid: input.qid,
          spec: input.spec,
          timestamp: new Date().toISOString(),
        });
        throw err;
      }

      return {
        bt_id,
        banked_theorem_path: btPath,
        open_question_path: oqPath,
        index_rebuilt: true,
        all_bt_ids: [],
      };
    });
  } catch (err: unknown) {
    if (isLockError(err)) throw new GraphLockTimeout(err);
    throw err;
  }
}

// ---------------------------------------------------------------------------
// Paper-scoped path: write N BankedTheorems (one per completed entry).
//
// NOTE: Writing N BankedTheorems is not strictly atomic — a partial failure
// leaves some BT files written and the OQ still `in_progress`. The recovery
// record machinery handles this: a recovery file is written after each BT
// write failure so `close_oq.ts --resume` can complete the transaction.
//
// Rebuild of index.json happens ONCE after all N writes, not per-theorem.
// ---------------------------------------------------------------------------

async function closeOpenQuestionPaperScoped(
  input: CloseOpenQuestionInput,
  graphRoot: string,
  paperTheorems: NonNullable<CloseOpenQuestionInput["theorems"]>,
): Promise<CloseOpenQuestionResult> {
  const oqPath = path.join(graphRoot, "nodes", "open_question", `${input.oq_id}.json`);

  // Filter to only completed theorems — stuck/failed entries are skipped.
  const completed = paperTheorems.filter((t) => t.status === "completed");

  try {
    return await withGraphWriteLock(graphRoot, async () => {
      // 1. Validate OQ preconditions.
      if (!existsSync(oqPath)) {
        throw new OpenQuestionMissing(input.oq_id, oqPath);
      }
      const oq = JSON.parse(await readFile(oqPath, "utf8")) as OpenQuestion;
      const observedStatus = stringifyStatus(oq.status);
      if (observedStatus !== "in_progress") {
        throw new OpenQuestionNotInProgress(input.oq_id, observedStatus);
      }

      // 2. Write one BankedTheorem per completed theorem.
      // bt_id format: <qid>_<local_id>_<spec>
      const writtenBtIds: string[] = [];
      const btDir = path.join(graphRoot, "nodes", "banked_theorem");
      await mkdir(btDir, { recursive: true });

      for (const t of completed) {
        const bt_id = `${input.qid}_${t.local_id}_${input.spec}`;
        const btPath = path.join(btDir, `${bt_id}.json`);

        const bt: BankedTheorem = {
          schema_version: 2,
          bt_id,
          qid: input.qid,
          spec: input.spec,
          instantiates: input.bankMetadata.instantiates ?? [],
          uses: input.bankMetadata.uses ?? [],
          derived_from: input.oq_id,
          closes: [input.oq_id],
        };

        if (existsSync(btPath)) {
          await assertExistingBankedTheoremMatches(btPath, bt);
          writtenBtIds.push(bt_id);
          continue;
        }

        try {
          await writeAtomic(btPath, jsonStable(bt));
          writtenBtIds.push(bt_id);
        } catch (err) {
          // Leave a recovery record for partial-write scenario.
          await writeRecoveryRecord(graphRoot, {
            phase: "after_bt_write",
            bt_id,
            oq_id: input.oq_id,
            qid: input.qid,
            spec: input.spec,
            timestamp: new Date().toISOString(),
          });
          throw err;
        }
      }

      // 3. Guard: if no theorems completed, leave OQ in_progress and throw.
      // Per design: stuck/failed entries are NOT banked; they surface as
      // failure-Notes via study-pipeline S5. The OQ must stay in_progress so
      // Stage 7 reroute or manual retry can pick it up later.
      if (writtenBtIds.length === 0) {
        throw new PaperHasNoCompletedTheorems(input.qid);
      }

      // 4. Update OpenQuestion status.
      // OpenQuestion.closed_by accepts a single string. Under paper-scoped
      // mode there are N bt_ids; we use the first one as the canonical closer.
      // The full list is available via writtenBtIds / all_bt_ids on the result.
      const primaryBtId = writtenBtIds[0];
      const updatedOq = { ...oq, status: { closed_by: primaryBtId } as const };
      try {
        await writeAtomic(oqPath, jsonStable(updatedOq));
      } catch (err) {
        await writeRecoveryRecord(graphRoot, {
          phase: "after_bt_write",
          bt_id: primaryBtId,
          oq_id: input.oq_id,
          qid: input.qid,
          spec: input.spec,
          timestamp: new Date().toISOString(),
        });
        throw err;
      }

      // 5. Rebuild index ONCE after all N writes.
      try {
        const nodes = await loadAllNodes(graphRoot);
        await writeIndexAtomic(graphRoot, buildIndex(nodes));
      } catch (err) {
        await writeRecoveryRecord(graphRoot, {
          phase: "after_oq_update",
          bt_id: primaryBtId,
          oq_id: input.oq_id,
          qid: input.qid,
          spec: input.spec,
          timestamp: new Date().toISOString(),
        });
        throw err;
      }

      // Return first bt_id as the canonical result; all_bt_ids carries the full list.
      const firstBtPath = path.join(btDir, `${primaryBtId}.json`);
      return {
        bt_id: primaryBtId,
        banked_theorem_path: firstBtPath,
        open_question_path: oqPath,
        index_rebuilt: true,
        all_bt_ids: writtenBtIds,
      };
    });
  } catch (err: unknown) {
    if (isLockError(err)) throw new GraphLockTimeout(err);
    throw err;
  }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function stringifyStatus(status: OpenQuestion["status"]): string {
  if (typeof status === "string") return status;
  if (status && typeof status === "object" && "closed_by" in status) {
    return `closed_by:${(status as { closed_by: string }).closed_by}`;
  }
  return String(status);
}

function sameStringArray(a: unknown, b: string[]): boolean {
  return Array.isArray(a) && a.length === b.length && a.every((v, i) => v === b[i]);
}

async function assertExistingBankedTheoremMatches(
  btPath: string,
  expected: BankedTheorem,
): Promise<void> {
  const existing = JSON.parse(await readFile(btPath, "utf8")) as BankedTheorem;
  if (
    existing.qid !== expected.qid ||
    existing.spec !== expected.spec ||
    existing.derived_from !== expected.derived_from ||
    !sameStringArray(existing.closes, expected.closes ?? []) ||
    !sameStringArray(existing.instantiates, expected.instantiates) ||
    !sameStringArray(existing.uses, expected.uses)
  ) {
    // why: recovery idempotency must not silently close the wrong OQ/source.
    throw new BankedTheoremConflict(expected.bt_id, btPath);
  }
}

function jsonStable(obj: unknown): string {
  // Stable, sorted-key JSON (mirrors graph.ts#serializeIndex pattern) so the
  // emitted node file is byte-deterministic across runs.
  function replacer(_k: string, v: unknown) {
    if (v && typeof v === "object" && !Array.isArray(v)) {
      const o = v as Record<string, unknown>;
      const out: Record<string, unknown> = {};
      for (const k of Object.keys(o).sort()) out[k] = o[k];
      return out;
    }
    return v;
  }
  return JSON.stringify(obj, replacer, 2) + "\n";
}

async function writeAtomic(target: string, content: string): Promise<void> {
  const tmp = `${target}.new`;
  await writeFile(tmp, content, "utf8");
  await rename(tmp, target);
}

interface RecoveryRecord {
  phase: "after_bt_write" | "after_oq_update";
  bt_id: string;
  oq_id: string;
  qid: string;
  spec: string;
  timestamp: string;
}

async function writeRecoveryRecord(
  graphRoot: string,
  rec: RecoveryRecord,
): Promise<void> {
  const dir = path.join(graphRoot, "_recovery");
  await mkdir(dir, { recursive: true });
  const target = path.join(dir, `${rec.bt_id}.recovery.json`);
  await writeFile(target, JSON.stringify(rec, null, 2) + "\n", "utf8");
}

function isLockError(err: unknown): boolean {
  if (!err || typeof err !== "object") return false;
  const code = (err as { code?: string }).code;
  return code === "ELOCKED" || code === "EEXIST";
}

function defaultGraphRoot(): string {
  let cur = path.resolve(process.cwd());
  while (true) {
    const lakefile = path.join(cur, "lakefile.toml");
    if (existsSync(lakefile)) {
      try {
        const content = readFileSync(lakefile, "utf8");
        if (/^\s*name\s*=\s*"CausalSmith"/m.test(content)) {
          return path.join(cur, "doc", "study");
        }
      } catch {
        // unreadable; keep walking
      }
    }
    const parent = path.dirname(cur);
    if (parent === cur) {
      throw new Error(
        `Could not locate CausalSmith package root from ${process.cwd()}. Pass {graphRoot} to closeOpenQuestion explicitly.`,
      );
    }
    cur = parent;
  }
}
