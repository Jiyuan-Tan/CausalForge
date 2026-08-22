// Replay engine over archived REAL D-stage artifacts (2026-07-30 migration plan, Phase 0).
//
// Purpose: every migration phase (store consolidation, revision-hash references,
// TeX-out-of-JSON) is validated against real bytes, not belief-built fixtures. The
// engine walks every run directory under a research root and replays the artifacts
// through the PRODUCTION read/validate paths:
//
//   1. store loads       — `readTypedCore` over proto_core.json / core.json,
//                          `loadWorkingState`, `readEscalationLog` (torn-line strict);
//   2. apply validator   — `applyProposedChanges({checkOnly: true})` over a temp COPY
//                          of the run (originals are never passed to any production
//                          function), asserting the validated-change count equals the
//                          pending-proposal count;
//   3. apply receipts    — every escalation entry that carries `changed[]` is
//                          well-formed (historical receipts cannot be re-validated
//                          end-to-end: the pre-apply working state is consumed by the
//                          apply transaction, whose journal is deleted on commit);
//   4. solve outputs     — every persisted `solve_*.json` through the exact production
//                          ingest (`readSolveUnitOutput`);
//   5. review packets    — every `proposal_review_packet.json` parses, and its payload
//                          is replayed through the apply validator against the sibling
//                          proto (the packet embeds the working state it was built from);
//   6. assemble-equivalence — once Phase 1 lands the pure `assemble(proto, working)`,
//                          each archived (proto, working) pair is assembled and diffed
//                          against the committed core.json (report-only on
//                          pre-migration runs; hard-fail on post-migration runs).
//                          Until then this section reports SKIPPED.
//
// Mutation guard: each run replays inside a temp copy which is hashed before and after;
// any byte difference is a hard failure regardless of tier.
//
// Severity policy (explicit): failures gate; warnings are reported only.
//   - ACTIVE runs (research-root/active/...) must load/validate with current code —
//     any error there is a failure.
//   - _bank runs and `rejected_rounds/` snapshots are frozen history spanning older
//     format generations; read-compat is best-effort, so load errors there are
//     classified warnings (each is listed for review), EXCEPT mutation and
//     count-invariant breaks, which indicate current-code bugs and fail on any tier.

import { existsSync } from "node:fs";
import { cp, copyFile, mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import os from "node:os";
import path from "node:path";

import type { PipelineContext } from "../types.js";
import { CoreSchema, type Core } from "./core/schema.js";
import { assembleCore } from "./core/assemble.js";
import { readTypedCore } from "./core/core_io.js";
import { protoCoreJsonPath } from "./stages/neg1_2_author.js";
import { coreJsonPath } from "./stages/d0_core.js";
import {
  loadWorkingState,
  readEscalationLog,
  type WorkingState,
} from "./stages/d0_working.js";

import { applyProposedChanges, validatePendingApplyTransaction } from "./stages/d0_apply.js";
import { readRoundProposals, type RoundProposals } from "./solve/proposals.js";
import { readSolveUnitOutput } from "./solve/dispatch.js";

/** Directory names never descended into: snapshot/backup trees whose bytes predate the
 *  store layouts under test, plus content-addressed blobs with nothing to replay. */
const SKIP_DIR_NAMES = new Set([".premigration", "_backups", "objects"]);

export interface ReplayTargetResult {
  /** Path relative to the research root. */
  rel: string;
  tier: "active" | "bank";
  qid: string | null;
  notes: string[];
  warnings: string[];
  failures: string[];
}

export function relToRoot(researchRoot: string, p: string): string {
  return path.relative(researchRoot, p);
}

export function tierOf(researchRoot: string, p: string): "active" | "bank" {
  const segs = relToRoot(researchRoot, p).split(path.sep);
  // `rejected_rounds/` subtrees are frozen snapshots of rounds the pipeline REFUSED
  // (kept as incident history), so they grade like _bank even inside an active run:
  // their bytes are expected to be invalid — that is why they were rejected.
  if (segs.includes("rejected_rounds")) return "bank";
  return segs[0] === "active" ? "active" : "bank";
}

export interface WalkResult {
  dirs: string[];
  files: string[];
  /** Unreadable directories. Coverage gaps must be visible, not silently green. */
  errors: string[];
}

/** Walk `root` recursively, skipping SKIP_DIR_NAMES and dot-dirs. */
export async function walkTree(root: string): Promise<WalkResult> {
  const out: WalkResult = { dirs: [], files: [], errors: [] };
  const stack = [root];
  while (stack.length > 0) {
    const dir = stack.pop()!;
    let entries;
    try {
      entries = await readdir(dir, { withFileTypes: true });
    } catch (err) {
      out.errors.push(`unreadable directory ${dir}: ${errMsg(err)}`);
      continue;
    }
    for (const e of entries) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) {
        if (SKIP_DIR_NAMES.has(e.name) || e.name.startsWith(".")) continue;
        out.dirs.push(p);
        stack.push(p);
      } else if (e.isFile()) {
        out.files.push(p);
      }
    }
  }
  return out;
}

/** sha256 of every file under `dir` (INCLUDING dot-files and skipped-name subdirs —
 *  the mutation guard must see everything), keyed by relative path. */
export async function hashTree(dir: string): Promise<Map<string, string>> {
  const map = new Map<string, string>();
  const stack = [dir];
  while (stack.length > 0) {
    const d = stack.pop()!;
    for (const e of await readdir(d, { withFileTypes: true })) {
      const p = path.join(d, e.name);
      if (e.isDirectory()) stack.push(p);
      else if (e.isFile()) {
        map.set(path.relative(dir, p), createHash("sha256").update(await readFile(p)).digest("hex"));
      }
    }
  }
  return map;
}

function errMsg(err: unknown): string {
  return err instanceof Error ? err.message : String(err);
}

/** Key-order-insensitive canonical serialization — the EQUIVALENCE verdict is
 *  this full comparison, never the compact diff below (audit R2F2: a diff that
 *  enumerates fields is not an equivalence check; any field it forgets becomes
 *  a hole in the format-2 hard-fail gate). */
export function canonicalCoreJson(core: Core): string {
  const sortKeys = (value: unknown): unknown => {
    if (Array.isArray(value)) return value.map(sortKeys);
    if (value !== null && typeof value === "object") {
      return Object.fromEntries(
        Object.entries(value as Record<string, unknown>)
          .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
          .map(([k, v]) => [k, sortKeys(v)]),
      );
    }
    return value;
  };
  return JSON.stringify(sortKeys(core));
}

/** Compact structural diff between the committed core and the derived
 *  `assembleCore(proto, working)` render — the human-readable REPORT for a
 *  divergence the canonical comparison found. Statement-level (id-keyed) plus
 *  the top-level prose fields; deliberately not exhaustive. */
export function diffAssembledCore(committed: Core, derived: Core): string[] {
  const out: string[] = [];
  const cById = new Map(committed.statements.map((s) => [s.id, s] as const));
  const dById = new Map(derived.statements.map((s) => [s.id, s] as const));
  for (const id of cById.keys()) if (!dById.has(id)) out.push(`statement ${id}: committed-only`);
  for (const id of dById.keys()) if (!cById.has(id)) out.push(`statement ${id}: derived-only`);
  for (const [id, c] of cById) {
    const d = dById.get(id);
    if (!d) continue;
    if (c.status !== d.status) out.push(`statement ${id}: status ${c.status} → ${d.status}`);
    if (c.statement !== d.statement) out.push(`statement ${id}: claim text differs`);
    if ((c.proof_tex ?? "") !== (d.proof_tex ?? "")) out.push(`statement ${id}: proof bytes differ`);
    const deps = (s: Core["statements"][number]): string => [...new Set(s.depends_on ?? [])].sort().join(",");
    if (deps(c) !== deps(d)) out.push(`statement ${id}: depends_on differs`);
  }
  for (const field of [
    "tldr",
    "related_work",
    "interpretation",
    "technical_internal_limitation",
    "honest_scope",
  ] as const) {
    if ((committed[field] ?? "") !== (derived[field] ?? "")) out.push(`prose field ${field} differs`);
  }
  if (JSON.stringify(committed.project_justification ?? {}) !== JSON.stringify(derived.project_justification ?? {})) {
    out.push("project_justification differs");
  }
  if (committed.assumptions.length !== derived.assumptions.length) {
    out.push(`assumptions count ${committed.assumptions.length} → ${derived.assumptions.length}`);
  }
  if ((committed.bibliography ?? []).length !== (derived.bibliography ?? []).length) {
    out.push(`bibliography count ${(committed.bibliography ?? []).length} → ${(derived.bibliography ?? []).length}`);
  }
  return out;
}

/** Mirror of the apply's content-dedupe (`d0_apply.ts`): the validated-change count is
 *  computed over deduplicated arrays, so the expected count must be too. */
function dedupeByJson<T>(values: T[]): T[] {
  const seen = new Set<string>();
  return values.filter((v) => {
    const key = JSON.stringify(v);
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

function expectedChangeCount(proposals: RoundProposals): number {
  return (
    dedupeByJson(proposals.statements).length +
    dedupeByJson(proposals.definitions).length +
    dedupeByJson(proposals.assumptions).length +
    dedupeByJson(proposals.coreEdits).length
  );
}

/** Extract qid/specialization from proto_core.json or core.json raw bytes (no schema —
 *  identification must work even where full validation fails). */
export async function extractRunIdentity(dir: string): Promise<{ qid: string; spec: string } | null> {
  let names: string[];
  try {
    names = await readdir(dir);
  } catch {
    return null;
  }
  for (const suffix of ["proto_core.json", "core.json"]) {
    for (const n of names) {
      if (n !== suffix && !n.endsWith(`_${suffix}`)) continue;
      try {
        const raw = JSON.parse(await readFile(path.join(dir, n), "utf8")) as {
          qid?: unknown;
          specialization?: unknown;
        };
        if (typeof raw.qid === "string" && raw.qid.length > 0) {
          return {
            qid: raw.qid,
            spec: typeof raw.specialization === "string" ? raw.specialization : "replay",
          };
        }
      } catch {
        // fall through to the next candidate
      }
    }
  }
  return null;
}

/** True when `dir` holds a replayable store set: a canonical discovery dir, or any
 *  snapshot dir (e.g. `rejected_rounds/round_N/`) carrying its own proto_core.json. */
async function isRunDir(dir: string): Promise<boolean> {
  if (path.basename(dir) === "discovery") return true;
  let names: string[];
  try {
    names = await readdir(dir);
  } catch {
    return false;
  }
  return names.some((n) => n === "proto_core.json" || n.endsWith("_proto_core.json"));
}

/** Copy one archived run into a temp repo shaped as an active run, so production path
 *  resolution works. Copies the store dir AND the run-root state files: the apply
 *  validator derives the live proposal revision from `state.json` when mandates are
 *  pending, so omitting it would replay mandate-bearing runs on a different basis
 *  than production uses. */
export async function copyRunForReplay(
  realDir: string,
  tmpRepo: string,
  qid: string,
): Promise<{ tmpRun: string; tmpDiscovery: string }> {
  const tmpRun = path.join(tmpRepo, "doc", "research", "active", qid);
  const tmpDiscovery = path.join(tmpRun, "discovery");
  await cp(realDir, tmpDiscovery, { recursive: true });
  // Run-root state files live one level above a canonical discovery/ dir; snapshot
  // dirs may sit deeper, so search upward a bounded number of levels.
  let cursor = path.dirname(realDir);
  for (let depth = 0; depth < 3; depth += 1) {
    let names: string[] = [];
    try {
      names = await readdir(cursor);
    } catch {
      break;
    }
    const stateNames = names.filter(
      (n) =>
        n === "state.json" ||
        n === "state.archived.json" ||
        n.endsWith("_state.json") ||
        n.endsWith("_state.archived.json"),
    );
    if (stateNames.length > 0) {
      for (const n of stateNames) await copyFile(path.join(cursor, n), path.join(tmpRun, n));
      break;
    }
    cursor = path.dirname(cursor);
  }
  return { tmpRun, tmpDiscovery };
}

interface ProblemSink {
  notes: string[];
  warnings: string[];
  failures: string[];
}

function problemFn(sink: ProblemSink, tier: "active" | "bank") {
  return (msg: string, forceFail = false): void => {
    if (tier === "active" || forceFail) sink.failures.push(msg);
    else sink.warnings.push(msg);
  };
}

/** Validate one escalation-log receipt stream. `transaction_id` only exists on the
 *  newest generation of receipts (27 of 1051 entries in the 2026-07-30 corpus), so a
 *  receipt is identified by a non-empty `changed[]` — the field the apply constructs.
 *  Field completeness follows the generations observed in the real corpus: `id`+`kind`
 *  always; `from`/`to`/`reason` are mandatory only on the new (`transaction_id`-stamped)
 *  generation — 108 of 1663 historical elements legitimately omit them. */
function checkReceipts(
  entries: Awaited<ReturnType<typeof readEscalationLog>>,
  problem: (msg: string, forceFail?: boolean) => void,
): { total: number; applyReceipts: number } {
  const applyEntries = entries.filter((e) => Array.isArray(e.changed) && e.changed.length > 0);
  entries.forEach((e, i) => {
    if (e.changed === undefined) return;
    const isNewGeneration = typeof e.transaction_id === "string";
    const label = isNewGeneration ? (e.transaction_id as string) : `entry ${i + 1}`;
    if (!Array.isArray(e.changed)) {
      problem(`apply receipt ${label}: changed is not an array`);
      return;
    }
    for (const c of e.changed) {
      if (typeof c?.id !== "string" || typeof c?.kind !== "string") {
        problem(`apply receipt ${label}: malformed changed[] element (id/kind)`);
        break;
      }
      if (
        isNewGeneration &&
        (typeof c.from !== "string" || typeof c.to !== "string" || typeof c.reason !== "string")
      ) {
        problem(`apply receipt ${label}: new-generation element missing from/to/reason`);
        break;
      }
    }
  });
  return { total: entries.length, applyReceipts: applyEntries.length };
}

/** Locate a pending apply transaction in a (copied) discovery dir. */
function findPendingTransaction(tmpDiscovery: string, qid: string): string | undefined {
  const txnPath = path.join(tmpDiscovery, "d0_apply_transaction.json");
  const legacyTxnPath = path.join(tmpDiscovery, `${qid}_d0_apply_transaction.json`);
  return [txnPath, legacyTxnPath].find((p) => existsSync(p));
}

/** Grade a pending apply transaction by production's OWN recovery validator
 *  (`validatePendingApplyTransaction`, the exact prefix `recoverPendingApply` runs),
 *  so a transaction the harness passes is one recovery could replay. Runs
 *  INDEPENDENTLY of the ordinary proto/working preview prerequisites — recovery
 *  itself needs neither a loadable working cursor nor a schema-valid proto, and a
 *  corrupt transaction must gate even when the stores around it are also broken. */
async function checkPendingTransaction(
  ctx: PipelineContext,
  pendingTxn: string,
  sink: ProblemSink,
  problem: (msg: string, forceFail?: boolean) => void,
): Promise<void> {
  sink.notes.push("pending d0_apply_transaction.json; check-mode skipped (guard refuses by design)");
  try {
    const { tx } = await validatePendingApplyTransaction(
      JSON.parse(await readFile(pendingTxn, "utf8")),
      () => readFile(protoCoreJsonPath(ctx), "utf8"),
      pendingTxn,
    );
    checkReceipts([tx.escalation_entry], problem);
    const entry = tx.escalation_entry as { changed?: unknown; directive?: unknown };
    if (!Array.isArray(entry.changed)) {
      // The apply constructs `changed` on every transaction it writes; an entry
      // without it would make recovery return undefined against its contract.
      problem("pending apply transaction: escalation_entry.changed is missing");
    } else if (
      entry.changed.length === 0 &&
      (typeof entry.directive !== "string" || entry.directive.length === 0)
    ) {
      // Mirror of the writer's own guard (`changed.length === 0 && !directive` returns
      // before the transaction write; "" is falsy there): an empty receipt without a
      // non-empty directive cannot have been produced by the current writer.
      // Directive-only applies legitimately carry changed=[].
      problem("pending apply transaction: escalation_entry.changed is empty with no directive");
    }
  } catch (err) {
    problem(`pending apply transaction fails production recovery validation: ${errMsg(err)}`);
  }
}

/** Run the read-only apply validator inside an already-populated temp run. */
async function checkApply(
  ctx: PipelineContext,
  working: WorkingState,
  sink: ProblemSink,
  problem: (msg: string, forceFail?: boolean) => void,
): Promise<void> {
  try {
    const proposals = await readRoundProposals(ctx, working);
    const expected = expectedChangeCount(proposals);
    const changed = await applyProposedChanges({ ctx, ids: null, checkOnly: true });
    sink.notes.push(`apply check-mode validated ${changed.length} pending change(s)`);
    if (changed.length !== expected) {
      // A silent count drift is a current-code bug, not historical damage: the
      // partial-apply guard inside applyProposedChanges throws on any unapplicable
      // selection, so reaching here with a mismatch means the validator counted
      // differently than the proposal store. Fail every tier.
      sink.failures.push(
        `apply check-mode count mismatch: validated ${changed.length}, pending proposals ${expected}`,
      );
    }
  } catch (err) {
    const msg = errMsg(err);
    if (msg.includes("predates the store fold")) {
      problem(`legacy pre-fold proposals shape: ${msg}`);
    } else {
      problem(`apply check-mode refused/failed: ${msg}`);
    }
  }
}

/** Replay one archived run dir inside a temp copy. Never touches the original. */
export async function replayRun(realDir: string, researchRoot: string): Promise<ReplayTargetResult> {
  const tier = tierOf(researchRoot, realDir);
  const res: ReplayTargetResult = {
    rel: relToRoot(researchRoot, realDir),
    tier,
    qid: null,
    notes: [],
    warnings: [],
    failures: [],
  };
  const problem = problemFn(res, tier);

  const identity = await extractRunIdentity(realDir);
  if (identity === null) {
    problem("no qid extractable from proto_core.json/core.json; store replay skipped");
    return res;
  }
  res.qid = identity.qid;

  const tmpRepo = await mkdtemp(path.join(os.tmpdir(), "d0replay-"));
  try {
    const { tmpRun, tmpDiscovery } = await copyRunForReplay(realDir, tmpRepo, identity.qid);
    const ctx: PipelineContext = {
      repoRoot: tmpRepo,
      qid: identity.qid,
      specialization: identity.spec,
      dryRun: true,
      resume: true,
    };
    const before = await hashTree(tmpRun);

    // -- 1. store loads through production readers -------------------------------
    let proto: Core | null = null;
    let core: Core | null = null;
    let working: WorkingState | null = null;

    const protoPath = protoCoreJsonPath(ctx);
    if (existsSync(protoPath)) {
      try {
        proto = await readTypedCore(protoPath);
      } catch (err) {
        problem(`proto_core.json failed readTypedCore: ${errMsg(err)}`);
      }
    } else {
      res.notes.push("no proto_core.json");
    }

    const corePath = coreJsonPath(ctx);
    if (existsSync(corePath)) {
      try {
        core = await readTypedCore(corePath);
      } catch (err) {
        problem(`core.json failed readTypedCore: ${errMsg(err)}`);
      }
    } else {
      res.notes.push("no core.json");
    }
    try {
      working = await loadWorkingState(ctx);
      if (working === null) res.notes.push("no d0_working.json");
    } catch (err) {
      working = null;
      problem(`d0_working.json failed loadWorkingState: ${errMsg(err)}`);
    }

    // -- 3. apply receipts -------------------------------------------------------
    try {
      const entries = await readEscalationLog(ctx);
      const { total, applyReceipts } = checkReceipts(entries, problem);
      res.notes.push(`${total} escalation entries, ${applyReceipts} apply receipts`);
    } catch (err) {
      problem(`d0_escalation_log.jsonl failed readEscalationLog: ${errMsg(err)}`);
    }

    // -- 2. read-only apply validator over the pending round ---------------------
    // A pending transaction is graded UNCONDITIONALLY (recovery needs neither store);
    // the apply preview needs the stores it reads.
    const pendingTxn = findPendingTransaction(tmpDiscovery, identity.qid);
    if (pendingTxn !== undefined) {
      await checkPendingTransaction(ctx, pendingTxn, res, problem);
    } else if (proto !== null && working !== null) {
      await checkApply(ctx, working, res, problem);
    }

    // -- 6. assemble-equivalence (Phase 1) ---------------------------------------
    // Derive the core from the archived (proto, working) pair through the pure
    // `assembleCore` and diff it against the committed core.json. Historical drift
    // is precisely the bug class Phase 1 retires, so legacy-format runs REPORT
    // divergences (reviewed, never assumed benign); runs written by the
    // post-consolidation writer (`store_format` ≥ 2) hard-fail on any divergence —
    // EXCEPT when a D0.R in-place edit is on record for the run (`d0r_raw.jsonl`),
    // which is a sanctioned post-solve editor of the published artifact.
    if (proto !== null && core !== null && working !== null) {
      try {
        const derived = assembleCore(proto, working);
        // Purity/stability: assembling the same pair twice must be byte-identical.
        const once = JSON.stringify(derived);
        const twice = JSON.stringify(assembleCore(proto, working));
        if (once !== twice) {
          res.failures.push("assembleCore is not byte-stable over the same (proto, working) pair");
        }
        // VERDICT: full canonical equality. The compact diff only narrates it.
        const equivalent = canonicalCoreJson(core) === canonicalCoreJson(derived);
        const diffs = equivalent ? [] : diffAssembledCore(core, derived);
        if (!equivalent && diffs.length === 0) {
          diffs.push("field-level content differs outside the compact diff's coverage (full canonical comparison)");
        }
        if (diffs.length > 0) {
          const postMigration = (working.store_format ?? 0) >= 2;
          const d0rEdited = (await readdir(realDir)).some(
            (n) => n === "d0r_raw.jsonl" || n.endsWith("_d0r_raw.jsonl"),
          );
          const head = diffs.slice(0, 6).join("; ") + (diffs.length > 6 ? `; … (${diffs.length - 6} more)` : "");
          const line = `assemble-equivalence: derived core diverges from committed core.json (${diffs.length}): ${head}`;
          if (postMigration && !d0rEdited) res.failures.push(line);
          else res.warnings.push(line + (d0rEdited ? " [D0.R edit on record]" : " [legacy-format cursor]"));
        } else {
          res.notes.push("assemble-equivalence: derived core matches committed core.json");
        }
      } catch (err) {
        // A pair the assembler cannot even render is a review item on legacy runs
        // and a bug on post-migration runs.
        const line = `assemble-equivalence: assembleCore threw: ${errMsg(err)}`;
        if ((working.store_format ?? 0) >= 2) res.failures.push(line);
        else res.warnings.push(line);
      }
    }

    // -- mutation guard ----------------------------------------------------------
    const after = await hashTree(tmpRun);
    const added = [...after.keys()].filter((k) => !before.has(k)).sort();
    const removed = [...before.keys()].filter((k) => !after.has(k)).sort();
    const changedFiles = [...before.keys()]
      .filter((k) => after.has(k) && after.get(k) !== before.get(k))
      .sort();
    if (added.length + removed.length + changedFiles.length > 0) {
      res.failures.push(
        `MUTATION under read-only replay: added=[${added.join(", ")}] removed=[${removed.join(", ")}] changed=[${changedFiles.join(", ")}]`,
      );
    }
    return res;
  } finally {
    await rm(tmpRepo, { recursive: true, force: true });
  }
}

/** Replay one review packet: structural validation, then the packet's own proposal
 *  payload through the apply validator against the sibling proto. The packet embeds
 *  the `durable_working_state` it was assembled from, and its `proposed_*` arrays are
 *  the round's proposal bundle — so a temp run seeded with (sibling proto, packet
 *  working ⊕ packet proposals, sibling escalation log) replays the exact adjudication
 *  input the orchestrator saw. This is the check that catches an apply-contract-invalid
 *  packet (the round_34 incident class) instead of grading it "structurally valid". */
export async function replayPacketFile(
  file: string,
  researchRoot: string,
): Promise<ReplayTargetResult> {
  const tier = tierOf(researchRoot, file);
  const res: ReplayTargetResult = {
    rel: relToRoot(researchRoot, file),
    tier,
    qid: null,
    notes: [],
    warnings: [],
    failures: [],
  };
  const problem = problemFn(res, tier);

  let pkt: Record<string, unknown>;
  try {
    pkt = JSON.parse(await readFile(file, "utf8")) as Record<string, unknown>;
    if (typeof pkt.contract !== "string") throw new Error("missing contract string");
    for (const k of [
      "proposed_statement_changes",
      "proposed_definition_changes",
      "proposed_assumptions",
      "proposed_core_edits",
      "provisional_proofs",
    ]) {
      if (pkt[k] !== undefined && !Array.isArray(pkt[k])) throw new Error(`${k} is not an array`);
    }
    CoreSchema.parse(pkt.current_typed_core);
  } catch (err) {
    problem(`packet failed structural validation: ${errMsg(err)}`);
    return res;
  }

  const dir = path.dirname(file);
  const identity = await extractRunIdentity(dir);
  if (identity === null) {
    problem("no run identity extractable next to packet; validator replay skipped");
    return res;
  }
  res.qid = identity.qid;

  const arr = (k: string): unknown[] => (Array.isArray(pkt[k]) ? (pkt[k] as unknown[]) : []);
  const packetProposals = {
    statements: arr("proposed_statement_changes"),
    definitions: arr("proposed_definition_changes"),
    assumptions: arr("proposed_assumptions"),
    coreEdits: arr("proposed_core_edits"),
    proofs: arr("provisional_proofs"),
  };

  // Cross-check: where the captured working state carries a proposals payload, the
  // packet arrays must be the same bundle — they are rendered from it.
  const dws = pkt.durable_working_state as (WorkingState & { proposals?: Record<string, unknown[]> }) | undefined;
  if (dws?.proposals !== undefined) {
    const pairs: Array<[string, unknown[], unknown[]]> = [
      ["statements", packetProposals.statements, dws.proposals.statements ?? []],
      ["definitions", packetProposals.definitions, dws.proposals.definitions ?? []],
      ["assumptions", packetProposals.assumptions, dws.proposals.assumptions ?? []],
      ["coreEdits", packetProposals.coreEdits, dws.proposals.coreEdits ?? []],
      // Proofs drift matters too: the validator replays proof promotion from the
      // packet's provisional_proofs, so a divergence from the durable store changes
      // what a paired claim+proof bundle would do.
      ["proofs", packetProposals.proofs, dws.proposals.proofs ?? []],
    ];
    for (const [kind, fromPacket, fromWorking] of pairs) {
      if (JSON.stringify(fromPacket) !== JSON.stringify(fromWorking)) {
        problem(`packet ${kind} diverge from durable_working_state.proposals — packet/store drift`);
      }
    }
  }

  const tmpRepo = await mkdtemp(path.join(os.tmpdir(), "d0replay-pkt-"));
  try {
    const tmpRun = path.join(tmpRepo, "doc", "research", "active", identity.qid);
    const tmpDiscovery = path.join(tmpRun, "discovery");
    await mkdir(tmpDiscovery, { recursive: true });
    const names = await readdir(dir);
    // extractRunIdentity can succeed from core.json alone; the validator replay needs
    // the PROTO specifically, so its absence is a per-packet problem, not a crash.
    const protoName = names.find((n) => n === "proto_core.json" || n.endsWith("_proto_core.json"));
    if (protoName === undefined) {
      problem("packet has no sibling proto_core.json; validator replay skipped");
      return res;
    }
    await copyFile(path.join(dir, protoName), path.join(tmpDiscovery, "proto_core.json"));
    // The packet is self-contained: only the packet dir's own escalation log is used
    // (a nested snapshot must not borrow the live run's later entries).
    const logName = names.find(
      (n) => n === "d0_escalation_log.jsonl" || n.endsWith("_d0_escalation_log.jsonl"),
    );
    if (logName !== undefined) {
      await copyFile(path.join(dir, logName), path.join(tmpDiscovery, "d0_escalation_log.jsonl"));
    }
    const workingSeed = { ...(dws ?? { round: 0, solved: {}, resolved_oeqs: {} }), proposals: packetProposals };
    await writeFile(path.join(tmpDiscovery, "d0_working.json"), JSON.stringify(workingSeed), "utf8");
    // Run-root state (live proposal-revision basis for mandate resolution).
    let cursor = dir;
    for (let depth = 0; depth < 3; depth += 1) {
      cursor = path.dirname(cursor);
      let rootNames: string[] = [];
      try {
        rootNames = await readdir(cursor);
      } catch {
        break;
      }
      const stateNames = rootNames.filter((n) => n === "state.json" || n.endsWith("_state.json"));
      if (stateNames.length > 0) {
        for (const n of stateNames) await copyFile(path.join(cursor, n), path.join(tmpRun, n));
        break;
      }
    }

    const ctx: PipelineContext = {
      repoRoot: tmpRepo,
      qid: identity.qid,
      specialization: identity.spec,
      dryRun: true,
      resume: true,
    };
    let working: WorkingState | null = null;
    try {
      working = await loadWorkingState(ctx);
    } catch (err) {
      problem(`packet durable_working_state failed loadWorkingState: ${errMsg(err)}`);
    }
    if (working !== null) {
      await checkApply(ctx, working, res, problem);
    }
    return res;
  } finally {
    await rm(tmpRepo, { recursive: true, force: true });
  }
}

/** CLI flag parsing, exported so the contract is unit-testable. Returns an error
 *  string (usage violation) or the parsed options. `--only` REQUIRES a value that is
 *  not itself a flag: `--only --verbose` and a bare trailing `--only` are usage errors,
 *  not silent full/empty runs. */
export function parseReplayArgs(
  args: string[],
): { error: string } | { only: string | null; verbose: boolean } {
  let only: string | null = null;
  let verbose = false;
  for (let i = 0; i < args.length; i += 1) {
    const a = args[i];
    if (a === "--verbose") {
      verbose = true;
    } else if (a === "--only") {
      const v = args[i + 1];
      if (v === undefined || v.startsWith("--")) return { error: "--only requires a value" };
      only = v;
      i += 1;
    } else {
      return { error: `Unknown argument: ${a}` };
    }
  }
  return { only, verbose };
}

export interface ReplaySummary {
  runResults: ReplayTargetResult[];
  packetResults: ReplayTargetResult[];
  solveTotal: number;
  solveOk: number;
  packetTotal: number;
  runTotal: number;
  failures: string[];
  warnings: string[];
}

export async function runReplay(opts: {
  researchRoot: string;
  only?: string | null;
  log?: (line: string) => void;
  verbose?: boolean;
}): Promise<ReplaySummary> {
  const log = opts.log ?? (() => {});
  const only = opts.only ?? null;
  const failures: string[] = [];
  const warnings: string[] = [];

  const roots = [path.join(opts.researchRoot, "active"), path.join(opts.researchRoot, "_bank")].filter(
    (p) => existsSync(p),
  );
  const walks = await Promise.all(roots.map(walkTree));
  for (const w of walks) {
    // Unreadable directories are coverage gaps; a green result must mean "everything
    // was seen", so they gate.
    failures.push(...w.errors.map((e) => `walk: ${e}`));
  }
  const allDirs = walks.flatMap((w) => w.dirs);
  const allFiles = walks.flatMap((w) => w.files).sort();

  const runDirCandidates: string[] = [];
  for (const d of allDirs) {
    if (await isRunDir(d)) runDirCandidates.push(d);
  }
  let runDirs = runDirCandidates;
  if (only !== null) runDirs = runDirs.filter((d) => relToRoot(opts.researchRoot, d).includes(only));
  runDirs.sort();

  // A target whose replay throws OUTSIDE the classified paths is a harness bug or an
  // unanticipated artifact shape; either way it must gate as a failure on that target
  // and the sweep must CONTINUE — an aborted sweep silently un-covers everything after
  // the throwing target.
  const guarded = async (
    relPath: string,
    fn: () => Promise<ReplayTargetResult>,
  ): Promise<ReplayTargetResult> => {
    try {
      return await fn();
    } catch (err) {
      return {
        rel: relPath,
        tier: tierOf(opts.researchRoot, path.join(opts.researchRoot, relPath)),
        qid: null,
        notes: [],
        warnings: [],
        failures: [`unhandled replay exception: ${errMsg(err)}`],
      };
    }
  };

  log(`Replaying ${runDirs.length} run dir(s) under ${opts.researchRoot} ...`);
  const runResults: ReplayTargetResult[] = [];
  for (const dir of runDirs) {
    const r = await guarded(relToRoot(opts.researchRoot, dir), () => replayRun(dir, opts.researchRoot));
    runResults.push(r);
    const status = r.failures.length > 0 ? "FAIL" : r.warnings.length > 0 ? "warn" : "ok";
    if (opts.verbose === true || status !== "ok") {
      log(`[${status}] (${r.tier}) ${r.rel}${r.qid !== null ? ` qid=${r.qid}` : ""}`);
      for (const n of opts.verbose === true ? r.notes : []) log(`    note: ${n}`);
      for (const w of r.warnings) log(`    warn: ${w}`);
      for (const f of r.failures) log(`    FAIL: ${f}`);
    }
    failures.push(...r.failures.map((f) => `${r.rel}: ${f}`));
    warnings.push(...r.warnings.map((w) => `${r.rel}: ${w}`));
  }

  // ---- global file sweeps over the REAL tree (read-only by construction) -------
  const sweepFiles = only === null ? allFiles : allFiles.filter((f) => relToRoot(opts.researchRoot, f).includes(only));

  const solveRe = /(^|_)solve_.*\.json$/; // clearRoundOutputs' production pattern
  const solveFiles = sweepFiles.filter((f) => solveRe.test(path.basename(f)));
  let solveOk = 0;
  for (const f of solveFiles) {
    try {
      await readSolveUnitOutput(f, path.basename(f));
      solveOk += 1;
    } catch (err) {
      const line = `solve output ${relToRoot(opts.researchRoot, f)} failed production ingest: ${errMsg(err)}`;
      if (tierOf(opts.researchRoot, f) === "active") failures.push(line);
      else warnings.push(line);
    }
  }
  if (solveFiles.length > 0) log(`Solve outputs: ${solveOk}/${solveFiles.length} pass production ingest.`);

  const packetFiles = sweepFiles.filter((f) => {
    const b = path.basename(f);
    return b === "proposal_review_packet.json" || b.endsWith("_proposal_review_packet.json");
  });
  const packetResults: ReplayTargetResult[] = [];
  for (const f of packetFiles) {
    const r = await guarded(relToRoot(opts.researchRoot, f), () => replayPacketFile(f, opts.researchRoot));
    packetResults.push(r);
    const status = r.failures.length > 0 ? "FAIL" : r.warnings.length > 0 ? "warn" : "ok";
    if (opts.verbose === true || status !== "ok") {
      log(`[${status}] (${r.tier}) packet ${r.rel}`);
      for (const n of opts.verbose === true ? r.notes : []) log(`    note: ${n}`);
      for (const w of r.warnings) log(`    warn: ${w}`);
      for (const f2 of r.failures) log(`    FAIL: ${f2}`);
    }
    failures.push(...r.failures.map((x) => `packet ${r.rel}: ${x}`));
    warnings.push(...r.warnings.map((x) => `packet ${r.rel}: ${x}`));
  }
  if (packetFiles.length > 0) {
    const ok = packetResults.filter((r) => r.failures.length === 0 && r.warnings.length === 0).length;
    log(`Review packets: ${ok}/${packetFiles.length} fully green (see warn/FAIL lines for the rest).`);
  }

  log("Assemble-equivalence: ACTIVE (diffed on every run dir with a loadable proto/core/working trio).");

  return {
    runResults,
    packetResults,
    solveTotal: solveFiles.length,
    solveOk,
    packetTotal: packetFiles.length,
    runTotal: runDirs.length,
    failures,
    warnings,
  };
}
