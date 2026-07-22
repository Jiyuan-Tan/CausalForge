import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { frozenClosuresComplete, frozenTheoremsProven, progressed } from "../graph/progress.js";
import { hasRealSorry, stripLeanComments } from "../graph/extractor.js";
import { runFiller, type FillerEscalation, type FillerResult } from "./proof_filler.js";
import { runReviewer, type ReviewerResult, type ReviewerEscalation, type StatementWitness } from "./proof_reviewer.js";
import { lintUnusedHypotheses } from "./unused_hypothesis_lint.js";
import { refreshGraphForGate } from "../graph/refresh.js";
import { graphPath, saveGraph } from "../graph/store.js";
import { frozenNlFingerprint, frozenMutationReason } from "../graph/frozen_nl_guard.js";
import type { GraphSkeletonRow } from "../graph/skeleton.js";
import type { FormalizationGraph } from "../graph/types.js";
import type { CodexRunInput } from "../shared/codex.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import { recordSubstrateGateList } from "../pipeline_support.js";
import { appendPipelineLog } from "../log.js";
import { loadState, saveState } from "../state.js";
import type { StateJson } from "../types.js";
import { restoreCarryoverProofs } from "./proof_carryover.js";
import { createHash } from "node:crypto";
import { PROOF_SCAFFOLD_MAX, REPEATED_F25_ERROR_MAX } from "./loop_limits.js";
import { isPaperTmpPath } from "../paths.js";

/** Result of the F3.5 unused-hypothesis gate: `blocking` = definite-transitive findings (a real
 *  statement defect — a public theorem forwards a hypothesis only into a bridge where the same
 *  parameter is provably unused); `advisory` = direct/wildcard-suspect findings (likely false
 *  positives, surfaced not blocked). Mirrors the dispatcher's F3.5 checkpoint policy. */
export interface UnusedHypGateResult {
  blocking: string[];
  advisory: string[];
}

/** Default F3.5 gate: lint every `.lean` under `leanDir` for unused hypotheses. Deterministic,
 *  no LLM. Best-effort — an unreadable tree yields no findings rather than failing the loop. */
async function defaultUnusedHypGate(leanDir: string): Promise<UnusedHypGateResult> {
  if (!leanDir) return { blocking: [], advisory: [] };
  let rels: string[];
  try {
    rels = (await readdir(leanDir, { recursive: true })).map(String).filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  } catch {
    return { blocking: [], advisory: [] };
  }
  const blocking: string[] = [];
  const advisory: string[] = [];
  for (const rel of rels) {
    let src: string;
    try {
      src = await readFile(path.join(leanDir, rel), "utf8");
    } catch {
      continue; // best-effort (file vanished between readdir and read) — same as the sibling scanners
    }
    for (const f of lintUnusedHypotheses(src).findings) {
      const msg = `${rel}:${f.declLine} ${f.theoremName}.${f.hypothesisName}${f.viaTheorem ? ` (via ${f.viaTheorem})` : ""}`;
      if (f.severity === "definite" && f.transitive) blocking.push(msg);
      else advisory.push(msg);
    }
  }
  return { blocking, advisory };
}

/** The orchestrator escalation menu (Claude meta handles these via runIntervention). */
export type EscalationRoute = "hint" | "build-substrate" | "fix-source" | "unclear" | "bank-partial" | "abandon" | "redo-math";
export type ProofReviewPhase = "2.5" | "3" | "3.5" | "4";

export type LoopOutcome =
  | { status: "completed" }
  | { status: "escalate"; route: EscalationRoute; reason: string;
      /** Logical F-phase which raised this escalation. The combined loop enters at F2.5 but
       * must keep F3/F3.5/F4 checkpoint rows truthful in the pipeline ledger. */
      phase?: ProofReviewPhase;
      /** Only on route="redo-math": the witnessed broken node, the reverse-dependency closure a D0
       *  re-solve invalidates, and whether any dependent is already proven (→ approval, not auto). */
      redoMath?: { obj_id: string; witness: StatementWitness; dependents: string[]; touchesProven: boolean } };

interface RefreshState {
  graph: FormalizationGraph;
  skeleton: GraphSkeletonRow[];
  dirty: string[];
  hashes: Record<string, string>;
}

function fillerRoute(e: FillerEscalation): EscalationRoute {
  if (e.kind === "needs-substrate") return "build-substrate";
  // `ambiguous-spec` is NOT a claim that the note is wrong — it's the filler saying it can't tell
  // which faithful encoding is intended. Routing it to `fix-source` would tell the orchestrator the
  // note is at fault when nobody has determined that; `unclear` keeps the two apart.
  // `unparsable-output` likewise places no fault on the note (a mechanical model-reply failure).
  if (e.kind === "ambiguous-spec" || e.kind === "unparsable-output") return "unclear";
  return "fix-source";
}

/** A reviewer escalation that is NOT an auto-fixable scaffold mismatch routes to the orchestrator:
 *  `needs-substrate` → build the missing layer; a genuinely-diagnosed defect (note-wrong,
 *  statement-wrong, claim-false — the `futile` set above) → fix-source (a human decision, since the
 *  note is the frozen contract and is never auto-rewritten). Anything else that reaches here —
 *  `unadjudicable` or a model-invented kind that couldn't be auto-rerouted to F2 — is a genuine
 *  "can't place fault" case, NOT a claim that the note is wrong, so it gets its own `unclear` route
 *  instead of being lumped into fix-source. */
function reviewerRoute(e: ReviewerEscalation): EscalationRoute {
  if (e.kind === "needs-substrate") return "build-substrate";
  if (e.kind === "note-wrong" || e.kind === "statement-wrong" || e.kind === "claim-false") return "fix-source";
  return "unclear";
}

/** Fix ①: build an F2 re-scaffold directive that carries the reviewer's PER-TARGET diagnosis
 *  (`driftNotes`) verbatim, so the scaffolder receives the SPECIFIC fix ("should be eventual / ∀ᶠ n",
 *  "constant must be uniform over the class", …) rather than a generic "make it match the note" that
 *  drops the diagnosis and invites the same-shape re-drift. Targets with no note fall back to bare id. */
function withDriftNotes(base: string, targets: string[], driftNotes: Record<string, string> = {}): string {
  const perTarget = targets.map((id) => (driftNotes[id] ? `• ${id}: ${driftNotes[id]}` : `• ${id}`)).join("\n");
  return `${base}\nReviewer's specific per-target diagnosis (apply EACH precisely — do NOT re-emit the same shape the reviewer just rejected):\n${perTarget}`;
}

/** Reverse-dependency (blast radius) of a broken node: every node whose statement/proof USES it,
 *  transitively (edge `from` USES `to`, so we walk `to → from`). `touchesProven` flags whether any
 *  dependent already has a complete proof — the expensive case a D0 re-solve would silently undo. */
function planRedoMath(graph: FormalizationGraph, brokenId: string): { dependents: string[]; touchesProven: boolean } {
  const rev = new Map<string, string[]>();
  for (const e of graph.edges) {
    if (e.kind !== "statement-uses" && e.kind !== "proof-uses") continue;
    if (!rev.has(e.to)) rev.set(e.to, []);
    rev.get(e.to)!.push(e.from);
  }
  const dependents = new Set<string>();
  const stack = [brokenId];
  while (stack.length) {
    const cur = stack.pop()!;
    for (const d of rev.get(cur) ?? []) if (!dependents.has(d)) { dependents.add(d); stack.push(d); }
  }
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  return { dependents: [...dependents], touchesProven: [...dependents].some((id) => byId.get(id)?.proof.state === "complete") };
}

/** Research-file forbidden proof cheats (comment-stripped). The filler is FORBIDDEN to
 *  axiomatize/admit or use opaque/native/unsafe escapes: those assert claims UNPROVEN while
 *  evading the real-sorry completion check and faking node `complete`. */
async function scanResearchCheatTokens(leanDir: string): Promise<string[]> {
  const out: string[] = [];
  let files: string[];
  try {
    files = (await readdir(leanDir, { recursive: true })).map(String).filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  } catch {
    return out;
  }
  for (const f of files) {
    let text: string;
    try {
      text = await readFile(path.join(leanDir, f), "utf8");
    } catch {
      continue;
    }
    const stripped = stripLeanComments(text);
    for (const [i, line] of stripped.split(/\r?\n/).entries()) {
      // Keep this aligned with the bank gate so F3 rejects proof-laundering before banking.
      const m = line.match(/\b(axiom|opaque|native_decide|unsafe|admit)\b/);
      if (m) out.push(`${f}:${i + 1}:${m[1]}`);
    }
  }
  return out;
}

/** True iff any research `.lean` file carries a REAL `sorry`/`admit` proof token (comment-aware:
 *  mentions in docstrings/comments do not count). The proof-fill phase is done once this is false. */
/**
 * Dotted lake module names for THIS RUN's Lean only (every `.lean` under `leanDir`, incl. nested
 * `Helpers/`), derived from each file's path relative to the package root.
 *
 * why: the compile gate must build only this run's modules — lake pulls in their dependencies
 * anyway. A bare `lake build` builds the WHOLE CausalSmith package, so an unrelated run's broken
 * module fails THIS run's gate (a spurious escalation on work we don't own) and contends with
 * concurrent lake builds from other sessions.
 */
export async function leanModuleTargets(repoRoot: string, leanDir: string): Promise<string[]> {
  if (!leanDir) return [];
  let rels: string[];
  try {
    rels = (await readdir(leanDir, { recursive: true })).map(String).filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  } catch {
    return [];
  }
  return rels.map((rel) =>
    path
      .relative(repoRoot, path.join(leanDir, rel))
      .replace(/\.lean$/, "")
      .split(path.sep)
      .join("."),
  );
}

/**
 * Emit a per-run sibling BARREL (`<leanDir>.lean`) importing every module in the run, so the whole
 * run is ONE buildable/verifiable lake target.
 *
 * why: research modules are NOT reachable from the top-level `CausalSmith.lean` barrel, so the
 * DEFAULT target skips them — `lake -d CausalSmith build` reports green while the run's oleans stay
 * STALE, and a `#print axioms` against those lies in both directions (hit live 2026-07-11). We
 * deliberately do NOT wire research runs into the top-level barrel: that would make one broken run
 * break every other run's default build (the same cross-run coupling the compile gate avoids).
 * Regenerated at F-stage entry so it cannot drift from the file set. Deterministic (sorted).
 */
export async function writeRunBarrel(repoRoot: string, leanDir: string): Promise<string | null> {
  const mods = (await leanModuleTargets(repoRoot, leanDir)).sort();
  if (mods.length === 0) return null;
  const barrelPath = `${leanDir}.lean`;
  // `import` must be at the very top of a Lean file, and a `/-! -/` module docstring is a
  // DECLARATION — so the overview goes AFTER the imports, not before (a plain `/- -/` copyright
  // comment is fine above them).
  const src =
    "/-\nCopyright (c) 2026 Jiyuan Tan. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Jiyuan Tan\n-/\n\n" +
    mods.map((m) => `import ${m}`).join("\n") +
    "\n\n/-! # Run barrel (auto-generated)\n\nAggregates every module of this causalsmith run so the whole run is ONE buildable target\n(`lake build <this module>`). Research modules are not reachable from the top-level\n`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale\noleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/\n";
  await writeFile(barrelPath, src, "utf8");
  return barrelPath;
}

/**
 * Real compile gate: `lake build` THIS RUN's modules (never the whole package — see
 * `leanModuleTargets`). Serialized behind the shared lake mutex so it cannot race a concurrent
 * stage build. A non-zero exit returns the trailing error text (enough for the orchestrator to
 * route a fix) rather than throwing — a red tree is a loop-blocking condition, not a crash.
 *
 * NB `sorry` is a WARNING: lake still exits 0 on a tree with sorries. That is fine here only
 * because the done-gate runs the textual `anyRealSorry` scan BEFORE this. The two are
 * complementary, not redundant — do not drop either.
 */
export async function buildRunModules(repoRoot: string, leanDir: string): Promise<{ ok: boolean; errors: string }> {
  const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
  const { withLakeBuildLock } = await import("../shared/build_mutex.js");
  const targets = await leanModuleTargets(repoRoot, leanDir);
  // No targets = we cannot verify anything. Do NOT fail open (that silently restores the hole the
  // gate exists to close); block and say so.
  if (targets.length === 0) {
    return { ok: false, errors: `compile gate: no Lean modules found under ${leanDir} — nothing could be verified` };
  }
  return withLakeBuildLock(repoRoot, async () => {
    const r = await spawnWithInactivityTimeout("lake", ["build", ...targets], {
      cwd: repoRoot,
      env: process.env,
      inactivityTimeoutMs: 30 * 60_000,
      maxTotalMs: 60 * 60_000,
    });
    if (r.exitCode === 0) return { ok: true, errors: "" };
    const errs = `${r.stdout}\n${r.stderr}`
      .split("\n")
      .filter((l) => /error/i.test(l))
      .slice(0, 25)
      .join("\n");
    return { ok: false, errors: errs.trim() || `lake build exited ${r.exitCode}` };
  });
}

async function anyRealSorry(leanDir: string): Promise<boolean> {
  let files: string[];
  try {
    files = (await readdir(leanDir, { recursive: true })).map(String).filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  } catch {
    return false;
  }
  for (const f of files) {
    try {
      const text = await readFile(path.join(leanDir, f), "utf8");
      // `admit` closes the term like `sorry`, so it must block the same completion gate.
      if (hasRealSorry(text) || /\badmit\b/.test(stripLeanComments(text))) return true;
    } catch {
      continue;
    }
  }
  return false;
}

// Total proof-review iterations, accumulated across resumes via `proof_loop_counters.iters`.
const MAX_ITERS = 60;
/** Phase-A scaffold-reroute rounds before giving up and escalating the statement gate. */
const SCAFFOLD_MAX = PROOF_SCAFFOLD_MAX;
/** Reroutes spent on TAGGING-ONLY crosswalk completeness (untagged `@realizes`). Kept small and
 *  SEPARATE from statement-drift rerouting so a tag the scaffolder can't place doesn't burn the full
 *  SCAFFOLD_MAX budget. After this many failed attempts the loop ESCALATES the remaining untagged
 *  symbols to the orchestrator (an incomplete symbol→Lean crosswalk is surfaced, never shipped silently). */
const TAG_REROUTE_MAX = 2;

/**
 * The proof–review loop replaces the legacy split proof/review stages. The reviewer runs at the TOP of each
 * iteration — so iteration 0 reviews the raw scaffold (the old F2.5) before any proof effort —
 * then the filler advances, then we re-refresh and loop. Terminates when every frozen theorem's
 * uses-closure is complete+matched (final convergence review = the old F4, dual-model), or
 * escalates (filler-stuck / reviewer-blocked / no-progress) for the orchestrator. The `refresh`,
 * `fill`, `review` deps are injectable for testing; production defaults wire the real agents.
 */
export async function runProofReviewLoop(args: {
  ctx: { repoRoot: string; qid: string; specialization: string };
  deps: {
    runCodex: (o: CodexRunInput) => Promise<{ stdout: string; stderr: string }>;
    runClaude?: (o: ClaudeRunInput) => Promise<string>;
  };
  formalizationDir?: string;
  leanDir?: string;
  // AUDIT-FORM: texPath is a dead pass-through kept because bin callers outside formalization still pass it.
  texPath?: string;
  corePath?: string;
  noProgressK?: number;
  /** Load-bearing orchestrator PROOF hint for phase B (lemma names / tactic strategy / Mathlib
   *  API), read from `state.flags.f3_filler_directive` on `--resume` and injected verbatim into
   *  every filler call for the whole loop run. Constant within a run (cleared/updated by the
   *  orchestrator between resumes); a proof hint only, never a statement/hypothesis license. */
  fillerDirective?: string | null;
  // injectable seams (default to the real impls)
  refresh?: () => Promise<RefreshState>;
  /** Proof filler. `directive` is supplied for a local compile-repair pass when the independent
   *  build gate finds a red tree after the model claimed completion. */
  fill?: (graph: FormalizationGraph, directive?: string) => Promise<FillerResult>;
  review?: (s: RefreshState, mode: "delta" | "convergence") => Promise<ReviewerResult>;
  /** Phase-A re-scaffold (F2 revise-mode). Given a directive + the flagged target obj_ids, edit
   *  the Lean statements in place to match the note, preserving existing proofs. When absent, a
   *  scaffold-mismatch can't be auto-fixed and Phase A escalates instead. */
  scaffold?: (a: { redirect: string; targets: string[] }) => Promise<void>;
  /** F3.5 unused-hypothesis gate (injectable for tests; defaults to the real lint over leanDir). */
  lintUnused?: (leanDir: string) => Promise<UnusedHypGateResult>;
  /** Compile gate (injectable for tests; defaults to a real `lake build` of the package).
   *  The `sorry` scan is TEXTUAL, so it passes a tree that does not COMPILE — see the done-gate. */
  buildCheck?: () => Promise<{ ok: boolean; errors: string }>;
  /** The pipeline's SHARED in-memory `StateJson`. `pipeline.ts` loads state ONCE at run start and
   *  re-saves that same object after each stage — so anything this loop writes straight to disk is
   *  CLOBBERED (last-writer-wins, deterministic). Passing the shared object here lets the loop
   *  mutate what the pipeline will actually persist. Without it, the iteration caps go inert (every
   *  resume gets a fresh budget) and `cited_checks: []` defeats bankEntry's cited-mismatch refusal. */
  state?: StateJson;
}): Promise<LoopOutcome> {
  const formalizationDir = args.formalizationDir ?? "";
  const leanDir = args.leanDir ?? "";
  const noProgressK = args.noProgressK ?? 10;
  const lintUnusedGate = args.lintUnused ?? defaultUnusedHypGate;
  const buildGate = args.buildCheck ?? (() => buildRunModules(args.ctx.repoRoot, leanDir));
  const phaseStartedAt = new Map<string, number>([["2.5", Date.now()]]);
  const markPhaseStarted = (stage: "3" | "3.5" | "4") => phaseStartedAt.set(stage, Date.now());
  const logPhaseCompleted = async (
    stage: "2.5" | "3" | "3.5" | "4",
    message: string,
  ): Promise<void> => {
    try {
      await appendPipelineLog(args.ctx, {
        stage,
        status: "completed",
        duration_ms: Math.max(0, Date.now() - (phaseStartedAt.get(stage) ?? Date.now())),
        message,
      });
    } catch (e) {
      // Phase logging is diagnostic. A ledger write failure must not invalidate a green proof.
      console.warn(`[${stage}] phase completion log failed (non-fatal): ${e instanceof Error ? e.message : String(e)}`);
    }
  };

  // ── ITERATION BUDGETS PERSIST ACROSS RESUMES ────────────────────────────────────────────────
  // These were in-process locals, so EVERY `--resume` silently handed the loop a fresh budget:
  // an orchestrator could re-roll the scaffold→review loop without bound, with no flag, no audit
  // trail and no gate. The reviewer is an LLM and non-deterministic on hard nodes, so unbounded
  // re-rolls means re-rolling until it blinks — a drifting node eventually draws a spurious
  // `matched` (laundering by resampling). Persisting them makes a cap a real circuit breaker:
  // exhausting any budget trips `proof_loop_cap_hit`, which BLOCKS the next resume until MAIN
  // clears it with `--clear-gate proof_loop_cap_hit` (a sub never resets its own cap).
  const zeroCounters = () => ({
    iters: 0,
    scaffold_rounds: 0,
    stale: 0,
    tag_reroutes: 0,
    node_strikes: {} as Record<string, number>,
    review_error_strikes: {} as Record<string, number>,
    // Comparand for the identically-red build cap. Persisted WITH `stale`: an in-process
    // local reset the cap to zero on every `--resume` (fresh null ≠ current errors), which
    // refunded the circuit breaker the persisted counters exist to enforce.
    last_build_error_sig: "",
  });
  const readState = async () => loadState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization);
  let counters = zeroCounters();
  try {
    // Prefer the shared object (what the pipeline will save); fall back to disk when running
    // standalone (bin/f3_loop.ts, tests).
    const seed = args.state?.flags.proof_loop_counters ?? (await readState()).flags.proof_loop_counters;
    counters = { ...zeroCounters(), ...(seed ?? {}) };
  } catch { /* no state yet (tests / cold start): start from zero */ }
  /** Persist the counters; optionally trip the cap flag. Writes BOTH the shared in-memory object
   *  (which `pipeline.ts` re-saves after the stage, and which would otherwise clobber us) and the
   *  disk (durability if the process dies mid-loop). Best-effort — a ledger failure must not sink a
   *  run whose Lean is green. */
  const saveCounters = async (capHit?: string) => {
    if (args.state) {
      args.state.flags.proof_loop_counters = counters;
      if (capHit) args.state.flags.proof_loop_cap_hit = capHit;
    }
    try {
      const st = await readState();
      st.flags.proof_loop_counters = counters;
      if (capHit) st.flags.proof_loop_cap_hit = capHit;
      await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, st);
    } catch { /* best-effort */ }
  };
  /** A budget ran out: persist + trip the cap, then escalate. */
  const capOut = async (
    route: "fix-source" | "bank-partial",
    reason: string,
    phase: ProofReviewPhase = "2.5",
  ): Promise<LoopOutcome> => {
    await saveCounters(reason);
    return { status: "escalate", route, reason, phase };
  };

  // Transient run logs (the reviewer-call debug log) go in a `logs/` subfolder, created up front, so
  // they don't clutter the qid folder root alongside the durable spec/state/graph artifacts.
  const logDir = formalizationDir ? path.join(formalizationDir, "logs") : "";
  if (logDir) await mkdir(logDir, { recursive: true }).catch(() => {});

  const refresh: () => Promise<RefreshState> =
    args.refresh ??
    (async () => {
      const r = await refreshGraphForGate({ formalizationDir, qid: args.ctx.qid, spec: args.ctx.specialization, leanDir });
      // why: surface the refresh diagnostic (e.g. duplicate @node) as the blocking reason instead
      // of a generic "no graph" — r.error distinguishes corrupt/invalid state from an absent graph.
      if (!r.graph) throw new Error(r.error ? `proof-review loop: graph refresh failed — ${r.error}` : "proof-review loop: no graph to refresh");
      return { graph: r.graph, skeleton: r.skeleton, dirty: r.dirty, hashes: r.hashes };
    });
  const fill: (g: FormalizationGraph, directive?: string) => Promise<FillerResult> =
    args.fill ?? ((graph, directive) => runFiller({
      ctx: args.ctx,
      deps: args.deps,
      graph,
      leanDir,
      texPath: args.texPath,
      corePath: args.corePath,
      directive: [args.fillerDirective, directive].filter((x): x is string => !!x?.trim()).join("\n\n") || null,
    }));
  const review: (s: RefreshState, mode: "delta" | "convergence") => Promise<ReviewerResult> =
    args.review ??
    ((s, mode) => runReviewer({ ctx: args.ctx, deps: args.deps, graph: s.graph, skeleton: s.skeleton, dirty: s.dirty, hashes: s.hashes, mode, leanDir, texPath: args.texPath, corePath: args.corePath, debugLogDir: logDir || undefined }));

  const persist = async (g: FormalizationGraph) => {
    if (formalizationDir) await saveGraph(graphPath(formalizationDir, args.ctx.qid, args.ctx.specialization), g);
  };

  let state = await refresh();

  // Frozen-note immutability baseline: the `.md`/graph NL of every from-note (frozen) node is the
  // paper's claim as F3 sees it; a stage must fix the LEAN, never weaken the frozen NL to match it
  // (doing so desyncs the NL from the `.tex` that P3 reads — the A-1/D1 laundering). Snapshot here
  // and re-check at the top of each phase iteration; a drift halts the loop loudly (see
  // graph/frozen_nl_guard.ts).
  const frozenBaseline = frozenNlFingerprint(state.graph);
  const frozenGuard = (phase: ProofReviewPhase): LoopOutcome | null => {
    const reason = frozenMutationReason(frozenBaseline, state.graph);
    return reason ? { status: "escalate", route: "fix-source", reason, phase } : null;
  };

  // ── PHASE A — STATEMENT/DEFINITION GATE (the old F2.5, now with auto-repair). Review the frozen
  // theorem statements + from-tex definitions. On a `scaffold-mismatch` (the note is faithful but
  // the Lean statement fails to realize it) reroute to F2 revise-mode — which preserves existing
  // proofs via carry-over — and re-review. On `note-wrong` / unbuilt substrate / unclassifiable
  // laundering, ESCALATE: the note is the frozen contract and is never auto-rewritten. Only once
  // the statements pass do we enter the proof-fill loop. Bounded by SCAFFOLD_MAX.
  let phaseAClean = false;
  // Seeded from the PERSISTED counters, so a resume continues the budget instead of resetting it.
  let tagRerouteAttempts = counters.tag_reroutes;
  // Per-node strike counter: if the SAME node is flagged across this many scaffold-reroute
  // rounds without converging, stop re-scaffolding it and ESCALATE for a deliberate
  // re-encoding by the orchestrator — instead of burning the whole budget thrashing one node.
  const PER_NODE_FLAG_MAX = 3;
  const nodeFlagCount = new Map<string, number>(Object.entries(counters.node_strikes));
  const strikeCap = (targets: string[]): string | null => {
    let capped: string | null = null;
    for (const t of targets) {
      if (t.startsWith("sym:")) continue; // tagging gaps are governed by TAG_REROUTE_MAX
      const n = (nodeFlagCount.get(t) ?? 0) + 1;
      nodeFlagCount.set(t, n);
      counters.node_strikes[t] = n; // persisted: strikes carry across resumes
      if (n >= PER_NODE_FLAG_MAX && !capped) capped = t;
    }
    return capped;
  };
  /** Fail closed when F2.5 returns the same normalized target+diagnostic three times. */
  const repeatedErrorCap = async (
    category: string,
    targets: string[],
    diagnostic: string,
  ): Promise<LoopOutcome | null> => {
    const normalizedDiagnostic = diagnostic.replace(/\s+/g, " ").trim();
    const normalizedTargets = [...new Set(targets)].sort();
    const signature = createHash("sha256")
      // Free-text notes are deliberately excluded: paraphrase, punctuation, and volatile attempt
      // numbers must not reset the recurrence counter for the same failure class and target set.
      .update(JSON.stringify({ category, targets: normalizedTargets }))
      .digest("hex")
      .slice(0, 16);
    const count = (counters.review_error_strikes[signature] ?? 0) + 1;
    counters.review_error_strikes[signature] = count;
    await saveCounters();
    if (count < REPEATED_F25_ERROR_MAX) return null;
    return await capOut(
      "fix-source",
      `[repeated-f2.5-error] identical ${category} failure flagged ${count} times ` +
        `(signature=${signature}; targets=${normalizedTargets.join(", ") || "none"}): ` +
        normalizedDiagnostic,
    );
  };
  // Budget is CUMULATIVE across resumes (counters.scaffold_rounds), not per-call.
  while (counters.scaffold_rounds < SCAFFOLD_MAX) {
    // Charge and persist this round before any external call so a crash cannot refund it.
    counters.scaffold_rounds++;
    await saveCounters();
    const mutated = frozenGuard("2.5");
    if (mutated) return mutated;
    const r = await review(state, "delta");
    state = { ...state, graph: r.graph };
    await persist(r.graph);
    // Captures a failed F2 re-scaffold / refresh so we escalate as a CONTROLLED loop outcome
    // (resumable checkpoint) rather than letting the throw crash the run — the main pipeline loop
    // has no stage-level try/catch, so an uncaught scaffold failure would abort the whole run.
    let scaffoldFailure: string | null = null;
    const reroute = async (redirect: string, targets: string[]): Promise<boolean> => {
      if (!args.scaffold) return false;
      try {
        await args.scaffold({ redirect, targets });
        state = await refresh();
        return true;
      } catch (err) {
        scaffoldFailure = err instanceof Error ? err.message : String(err);
        return false;
      }
    };
    // Untagged SETUP/ENV symbols (crosswalk-completeness tagging gaps). Non-blocking for faithfulness,
    // but the reviewer usually WRAPS them in a `scaffold-mismatch` escalate with no rerouteable target
    // (a `sym:` id has no backing node) — so we merge them into the reroute targets in BOTH the escalate
    // path and the escalate-null path below, capped by TAG_REROUTE_MAX.
    const untaggedSyms = Object.entries(state.graph.symbolReview ?? {})
      .filter(([, v]) => /untagged/i.test(v.verdict))
      .map(([id]) => id);
    const tagRedirect = () =>
      "TAGGING-ONLY (crosswalk completeness — do NOT change any statement, hypothesis, or proof): the " +
      "core symbols below carry no `@realizes` tag. Add an inline `-- @realizes <symbol>(<short hint>)` on " +
      "the decl that realizes each — for a computed quantity, the `def` that computes it; for a world " +
      "primitive, its carrier field + constraining predicate. Untagged: " + untaggedSyms.join(", ");
    if (r.escalate) {
      // Escalate kinds that must NOT be auto-rerouted to F2 — surface to the orchestrator instead:
      //  • `note-wrong` (the frozen note disagrees with the .tex — a human fixes the note);
      //  • `needs-substrate` (a primitive must be built first);
      //  • `statement-wrong` (a FROZEN theorem/lemma/def STATEMENT is genuinely wrong / under-specified
      //    vs the spec — fixing it needs DELIBERATE judgment: add a load-bearing hypothesis, complete
      //    an omitted clause, fix the logical form. Auto-rescaffolding a frozen statement risks F2
      //    GERRYMANDERING it to pass, a faithfulness hazard — so the orchestrator (or human) makes the
      //    statement change, then re-gates).
      // EVERYTHING ELSE — `scaffold-mismatch` (a SETUP/env realization F2 can mechanically retype),
      // `unadjudicable`, or a model-INVENTED kind — is scaffold-fixable: reroute the drifted targets to
      // F2, bounded by SCAFFOLD_MAX. (The reviewer mislabels kinds, so this escalates ONLY on the three
      // explicit protect-kinds and reroutes anything else.)
      const futile =
        r.escalate.kind === "note-wrong" ||
        r.escalate.kind === "needs-substrate" ||
        r.escalate.kind === "statement-wrong" ||
        r.escalate.kind === "claim-false" || // a refuted claim can't be rescaffolded — never reroute to F2
        r.escalate.kind === "missing-review-evidence" ||
        r.escalate.kind === "missing-review-target" ||
        r.escalate.kind === "unparsable-output" ||
        r.escalate.kind === "missing-peer-reviewer";
      if (!futile) {
        // Real statement/def drift targets (backing nodes); a `sym:` obj_id is a tagging gap, handled
        // via untaggedSyms so it doesn't count as a drift target.
        const driftTargets = [...new Set([
          ...(r.escalate.obj_id && !r.escalate.obj_id.startsWith("sym:") ? [r.escalate.obj_id] : []),
          ...r.blocking,
        ])];
        // A TAG-ONLY reroute (nothing but untagged `@realizes`) is capped so a tag the scaffolder can't
        // place doesn't burn the SCAFFOLD_MAX budget; past the cap, ESCALATE the gap (never proceed).
        const tagOnly = driftTargets.length === 0 && untaggedSyms.length > 0;
        if (tagOnly && tagRerouteAttempts >= TAG_REROUTE_MAX) {
          return { status: "escalate", route: "fix-source", phase: "2.5",
            reason: `[tagging-gap] ${untaggedSyms.length} core symbol(s) still untagged after ${tagRerouteAttempts} F2 tag-reroute(s): ${untaggedSyms.join(", ")}` };
        }
        if (tagOnly) counters.tag_reroutes = ++tagRerouteAttempts;
        const targets = [...new Set([...driftTargets, ...untaggedSyms])];
        const redirect = driftTargets.length ? r.escalate.reason : tagRedirect();
        const repeated = await repeatedErrorCap(
          `review-${r.escalate.kind}`,
          targets,
          withDriftNotes(redirect, targets, r.driftNotes),
        );
        if (repeated) return repeated;
        const cappedNode = strikeCap(driftTargets);
        await saveCounters();
        if (cappedNode) {
          return await capOut("fix-source",
            `[per-node-strikes] '${cappedNode}' flagged in ${PER_NODE_FLAG_MAX} scaffold-reroute rounds without converging — escalating for deliberate re-encoding by the orchestrator. Last: [${r.escalate.kind}] ${r.escalate.reason}`);
        }
        if (targets.length && (await reroute(withDriftNotes(redirect, targets, r.driftNotes), targets))) continue;
      }
      // F3→D0 rewind. A `claim-false` escalation carrying a concrete WITNESS is evidence the math
      // CLAIM is refuted, not that the proof is hard — route a D0-AUTHORED node back to discovery. Two
      // guards: the witness is the laundering firewall (a filler that merely gave up has none), and the
      // node must NOT be frozen-from-note — a refuted PAPER claim is a human decision (the paper is
      // wrong), never an auto re-derive. Either guard failing falls through to `fix-source` below (the
      // `futile` set keeps `claim-false` from being rerouted to F2 — you can't rescaffold a false claim).
      if (r.escalate.kind === "claim-false" && r.escalate.witness && r.escalate.obj_id) {
        const node = state.graph.nodes.find((n) => n.id === r.escalate!.obj_id);
        if (node && node.provenance !== "from-note") {
          const redo = planRedoMath(state.graph, r.escalate.obj_id);
          return {
            status: "escalate", route: "redo-math", phase: "2.5",
            reason: `[claim-false→D0] ${r.escalate.reason}`,
            redoMath: { obj_id: r.escalate.obj_id, witness: r.escalate.witness, ...redo },
          };
        }
      }
      if (scaffoldFailure) return { status: "escalate", route: "fix-source", phase: "2.5", reason: `F2 re-scaffold did not complete: ${scaffoldFailure}` };
      return { status: "escalate", route: reviewerRoute(r.escalate), phase: "2.5", reason: `[${r.escalate.kind}] ${r.escalate.reason}` };
    }
    if (r.blocking.length > 0) {
      // Statement/def drift without an explicit classification: treat as scaffold-fixable if we
      // can re-scaffold (the note already passed F1.5 drift-watch), else escalate for a human.
      const repeated = await repeatedErrorCap(
        "review-blocking",
        r.blocking,
        withDriftNotes("Fix the Lean statement(s)/def(s) to faithfully match the note.", r.blocking, r.driftNotes),
      );
      if (repeated) return repeated;
      const cappedNode = strikeCap(r.blocking);
      await saveCounters();
      if (cappedNode) {
        return await capOut("fix-source",
          `[per-node-strikes] '${cappedNode}' flagged in ${PER_NODE_FLAG_MAX} scaffold-reroute rounds without converging — escalating for deliberate re-encoding by the orchestrator. Last: reviewer flagged ${r.blocking.join(", ")}`);
      }
      if (await reroute(withDriftNotes("Fix the Lean statement(s)/def(s) to faithfully match the note.", r.blocking, r.driftNotes), r.blocking)) continue;
      if (scaffoldFailure) return { status: "escalate", route: "fix-source", phase: "2.5", reason: `F2 re-scaffold did not complete: ${scaffoldFailure}` };
      return { status: "escalate", route: "hint", phase: "2.5", reason: `reviewer flagged: ${r.blocking.join(", ")}` };
    }
    // CROSSWALK COMPLETENESS (escalate-null path): the reviewer surfaced untagged symbols WITHOUT an
    // escalate. Same tag-reroute-then-escalate policy as the escalate path above — route to F2 to add
    // the `@realizes` tag (tagged → cluster hash changes → re-reviews `matched`), capped by
    // TAG_REROUTE_MAX; past the cap (or no scaffolder), ESCALATE — never ship an incomplete crosswalk.
    if (untaggedSyms.length) {
      const repeated = await repeatedErrorCap(
        "review-untagged-symbols",
        untaggedSyms,
        withDriftNotes(tagRedirect(), untaggedSyms, r.driftNotes),
      );
      if (repeated) return repeated;
      if (tagRerouteAttempts < TAG_REROUTE_MAX) {
        counters.tag_reroutes = ++tagRerouteAttempts;
        await saveCounters();
        if (await reroute(withDriftNotes(tagRedirect(), untaggedSyms, r.driftNotes), untaggedSyms)) continue;
        if (scaffoldFailure) return { status: "escalate", route: "fix-source", phase: "2.5", reason: `F2 re-scaffold did not complete: ${scaffoldFailure}` };
      }
      return { status: "escalate", route: "fix-source", phase: "2.5",
        reason: `[tagging-gap] ${untaggedSyms.length} core symbol(s) carry no @realizes tag after ${tagRerouteAttempts} F2 tag-reroute(s): ${untaggedSyms.join(", ")}` };
    }
    phaseAClean = true;
    break;
  }
  if (!phaseAClean) {
    return await capOut("fix-source", `scaffold gate did not converge in ${SCAFFOLD_MAX} rounds`);
  }
  await logPhaseCompleted("2.5", "statement/definition faithfulness review completed");

  // F2 rewinds preserve identical-signature proofs as inert comments to keep
  // the statement-only F2.5 contract. Once Phase A accepts those statements,
  // reactivate the proofs mechanically before F3: re-proving unchanged work is
  // both expensive and an avoidable source of drift.
  const restored = await restoreCarryoverProofs(leanDir);
  if (restored.count > 0) {
    console.warn(
      `[causalsmith] restored ${restored.count} signature-matched carry-over proof(s) before F3; ` +
        "the filler will see only changed/new obligations.",
    );
    state = await refresh();
    await persist(state.graph);
  }

  // ── PHASE B — PROOF-FILL LOOP (the old F3, with the old F4 as the final convergence review).
  // Statements are settled; advance proofs, re-checking the dirty frontier each iteration so the
  // assumption- and definition-gate catch any laundering the filler introduces.
  markPhaseStarted("3");
  while (counters.iters < MAX_ITERS) {
    // Charge and persist this round before any external call so a crash cannot refund it.
    counters.iters++;
    await saveCounters();
    const mutated = frozenGuard("3");
    if (mutated) return mutated;
    // 0. Anti-laundering: forbidden proof-cheat tokens assert goals unproven while evading the
    // sorry-scan and faking node `complete`. Reject before completion can pass.
    const laundered = await scanResearchCheatTokens(leanDir);
    if (laundered.length > 0) {
      return {
        status: "escalate",
        route: "fix-source",
        phase: "3",
        reason: `filler LAUNDERED ${laundered.length} forbidden proof-cheat token(s) (must be proven or left as \`sorry\`): ${laundered.slice(0, 10).join(", ")}`,
      };
    }
    // 1. Review the dirty frontier (assumptions/defs the filler may have touched).
    const r = await review(state, "delta");
    state = { ...state, graph: r.graph };
    await persist(r.graph);
    if (r.escalate) return { status: "escalate", route: reviewerRoute(r.escalate), phase: "3", reason: `[${r.escalate.kind}] ${r.escalate.reason}` };
    if (r.blocking.length > 0) {
      return { status: "escalate", route: "hint", phase: "3", reason: `reviewer flagged: ${r.blocking.join(", ")}` };
    }

    // 2. Done? The proof-fill phase is complete when there is NO real `sorry` anywhere in the Lean
    // tree (comment-aware) — a HARD, UNCONDITIONAL gate — AND the frozen graph is settled (either
    // every from-note headline theorem is a linked complete decl, so all inlined intermediate lemmas
    // are discharged too, or the full graph closure is settled). The `!treeSorry` conjunct is
    // mandatory and is NOT subsumed by the graph check: the graph closure can report "complete" while
    // a real sorry sits in a decl that IS load-bearing but was never `proof-uses`-linked into the
    // headline closure (e.g. a witness-membership obligation a later self-patch left as `sorry` —
    // 2026-06-28). Trusting the graph over the file there let an undetected sorry reach the F5 bank
    // gate. A file-level sorry is always a liability the bank-soundness gate rejects, so block here
    // (keep filling / escalate filler-stuck) rather than completing past it. Then run F3.5 (the
    // deterministic unused-hypothesis lint) and the dual-model F4 convergence review BEFORE
    // completing. The lint needs complete proofs (only meaningful at the done-point); a
    // definite-transitive finding is a real statement defect → block; direct/advisory findings may be
    // wildcard-tactic false positives → surface, don't block.
    const treeSorry = await anyRealSorry(leanDir);
    if (!treeSorry && (frozenTheoremsProven(state.graph) || frozenClosuresComplete(state.graph))) {
      // COMPILE GATE — must run BEFORE F3.5 and the F4 convergence review. `anyRealSorry` is a
      // TEXT scan, and the graph check reads the graph: a tree full of type errors satisfies both
      // (no `sorry` appears in code that never elaborates). Without this, F3.5 lints and the
      // dual-model F4 review CERTIFIES a non-compiling tree, and F5 can bank it — a theorem that
      // does not compile is not a theorem. Observed live 2026-07-11 (eid_lingam_direction_min_order:
      // a scaffold reroute left the tree red; F3.5 + F4 both ran on it anyway).
      const build = await buildGate();
      if (!build.ok) {
        // A red tree is unfinished F3 work, not an orchestrator checkpoint. Feed the independent
        // diagnostics straight back to the filler even though the graph currently says `complete`
        // and the source contains no `sorry`. Previously we returned `[hint]`; on resume the same
        // preflight build ran before the filler, creating an inescapable red-build checkpoint loop.
        // The comparand is the PERSISTED signature (not an in-process local): a resume must
        // continue the identically-red count, not refund the cap a fresh budget.
        const buildSig = createHash("sha256").update(build.errors).digest("hex").slice(0, 16);
        if (counters.last_build_error_sig === buildSig) counters.stale++;
        else counters.stale = 0;
        counters.last_build_error_sig = buildSig;
        await saveCounters();
        if (counters.stale >= noProgressK) {
          return await capOut(
            "bank-partial",
            `lake build remained identically red across ${noProgressK} F3 repair iterations:\n${build.errors}`,
            "3",
          );
        }
        const repair = await fill(
          state.graph,
          [
            "F3 LOCAL COMPILE REPAIR — the independent build gate is RED.",
            "Fix these diagnostics in the research files. Do not change frozen statements, add assumptions, or touch inherited clean declarations.",
            "Run a low-noise build that preserves the exit status and prints the diagnostic tail before returning.",
            build.errors,
          ].join("\n"),
        );
        await persist(repair.graph);
        if (repair.escalate) {
          return { status: "escalate", route: fillerRoute(repair.escalate), phase: "3", reason: repair.escalate.reason };
        }
        state = await refresh();
        continue;
      }
      counters.last_build_error_sig = "";
      counters.stale = 0;
      await logPhaseCompleted("3", "proof filling completed; no proof holes and the Lean build is green");
      markPhaseStarted("3.5");
      const lint = await lintUnusedGate(leanDir);
      if (lint.blocking.length > 0) {
        return { status: "escalate", route: "fix-source", phase: "3.5", reason: `F3.5 unused-hypothesis (definite-transitive): ${lint.blocking.join("; ")}` };
      }
      if (lint.advisory.length > 0) console.warn(`[f3.5] advisory unused-hypothesis finding(s): ${lint.advisory.join("; ")}`);
      await logPhaseCompleted("3.5", "unused-hypothesis lint completed");
      // Final convergence review (dual) = the old F4.
      markPhaseStarted("4");
      const conv = await review(state, "convergence");
      await persist(conv.graph);
      // Delivery-role review must survive the process boundary: accepted banking independently
      // checks one current receipt from each peer. Replace the set on every F4 run so retries do
      // not accumulate stale or duplicate approvals.
      const deliveryReceipts = conv.deliveryReviewReceipts ?? [];
      const citedReceipts = conv.citedReviewReceipts ?? [];
      if (args.state) {
        args.state.delivery_review_receipts = deliveryReceipts;
        args.state.cited_review_receipts = citedReceipts;
        args.state.cited_checks = citedReceipts.map((receipt) => ({
          name: receipt.node_id,
          check_status: receipt.check_status,
          cite_id: receipt.cite_id,
          locator: receipt.locator,
          reviewer: receipt.reviewer,
        }));
        try {
          const st = await loadState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization);
          st.delivery_review_receipts = deliveryReceipts;
          st.cited_review_receipts = citedReceipts;
          st.cited_checks = args.state.cited_checks;
          await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, st);
        } catch (e) {
          return {
            status: "escalate",
            route: "fix-source",
            phase: "4",
            reason: `F4 could not persist reviewer receipts: ${e instanceof Error ? e.message : String(e)}`,
          };
        }
      }
      // Best-effort ledger write; a failure must not sink a run whose Lean is green.
      const recordGates = async (gates: typeof conv.substrateGates, what: string) => {
        if (gates.length === 0) return;
        try {
          const ledger = await recordSubstrateGateList(args.ctx, gates);
          if (ledger) console.warn(`[f4] recorded ${gates.length} ${what} → ${ledger}`);
        } catch (e) {
          console.warn(`[f4] ${what} ledger write failed (non-fatal): ${e instanceof Error ? e.message : String(e)}`);
        }
      };
      // GATED rows are the orchestrator's BUILD QUEUE — owed even when this run escalates, so they
      // are written before any early return. Disclosure only: the orchestrator must still register
      // each with `bin/gate.ts`, and `bankEntry`'s `auditSubstrateGates` refuses tier `accepted`
      // until it has.
      await recordGates(conv.substrateGates.filter((g) => g.gate_class !== "cited"), "substrate gate(s)");

      if (conv.escalate) return { status: "escalate", route: reviewerRoute(conv.escalate), phase: "4", reason: `[${conv.escalate.kind}] ${conv.escalate.reason}` };
      if (conv.blocking.length > 0) return { status: "escalate", route: "hint", phase: "4", reason: `convergence review flagged: ${conv.blocking.join(", ")}` };
      // CITED match gate: a `cited-mismatch` (the Lean def does NOT faithfully encode its cited
      // source) or a `cited-underspecified` (the def is not self-contained — a distinguishing
      // hypothesis/class is named but not encoded) BLOCKS banking — surface to the orchestrator
      // (fix the def or the citation; never auto-rewrite a banked def). Other cited verdicts
      // (verified / attested / unverifiable) pass.
      const cited = conv.substrateGates.filter((g) => g.gate_class === "cited");
      // Persist the source-match verdicts BEFORE acting on them: `bankEntry` re-checks these, so a
      // later `bank_entry.ts --tier accepted` (or a resume re-entering at F5) cannot bank past a
      // mismatch just because this in-process check is no longer on the stack.
      if (cited.length > 0 && citedReceipts.length === 0) {
        const severity = (status: string): number =>
          status === "cited-mismatch" || status === "cited-underspecified" ? 3
          : status === "unknown" || status === "cited-source-unverifiable" ? 2
          : 1;
        const deduped = new Map<string, { name: string; check_status: string; cite_id?: string; locator?: string }>();
        for (const g of cited) {
          const row = {
            name: g.name,
            check_status: g.check_status ?? "unknown",
            ...(g.source?.cite_id ? { cite_id: g.source.cite_id } : {}),
            ...(g.source?.locator ? { locator: g.source.locator } : {}),
          };
          const key = `${row.name}\u0000${row.cite_id ?? ""}\u0000${row.locator ?? ""}`;
          const prior = deduped.get(key);
          if (!prior || severity(row.check_status) > severity(prior.check_status)) deduped.set(key, row);
        }
        const checks = [...deduped.values()];
        // Write the SHARED object too: `pipeline.ts` re-saves its own stale copy after the stage,
        // so a disk-only write is clobbered — which would leave `cited_checks: []` on disk and
        // silently defeat bankEntry's refusal of tier `accepted` on a cited-mismatch.
        if (args.state) args.state.cited_checks = checks;
        try {
          const st = await loadState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization);
          st.cited_checks = checks;
          await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, st);
        } catch (e) {
          console.warn(`[f4] persisting cited_checks failed (non-fatal): ${e instanceof Error ? e.message : String(e)}`);
        }
      }
      const citedBad = cited.filter(
        (g) => g.check_status === "cited-mismatch" || g.check_status === "cited-underspecified",
      );
      if (citedBad.length > 0) {
        return {
          status: "escalate",
          route: "fix-source",
          phase: "4",
          reason: `${citedBad[0].check_status} — cited def does not faithfully + self-containedly encode the cited source (blocks banking): ${citedBad.map((g) => g.name).join(", ")}`,
        };
      }
      // CITED rows are written ONLY once the match gate passes: the registry documents what a
      // BANKED theorem assumes, so a mismatched def must never appear there as an accepted
      // dependency of a run that in fact halted.
      await recordGates(cited, "cited dependency/ies");
      await logPhaseCompleted("4", "dual-model convergence review completed");
      return { status: "completed" };
    }

    // 3. Filler advances.
    const prev = state.graph;
    const f = await fill(state.graph);
    await persist(f.graph);
    if (f.escalate) return { status: "escalate", route: fillerRoute(f.escalate), phase: "3", reason: f.escalate.reason };

    // 4. Re-refresh from the (now-edited) Lean + graph; check progress.
    state = await refresh();
    if (progressed(prev, state.graph)) counters.stale = 0;
    else if (++counters.stale >= noProgressK) return await capOut("bank-partial", "no progress across iterations", "3");
  }
  return await capOut("bank-partial", `loop exceeded ${MAX_ITERS} iterations`, "3");
}
