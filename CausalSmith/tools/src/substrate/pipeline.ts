// CausalSmith/tools/src/substrate/pipeline.ts
import { mkdir, writeFile, readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { ensureRequirement } from "./requirement.js";
import {
  substrateRunDir, substrateLeanDir, substrateModulePrefix, causaleanRoot,
} from "./paths.js";
import { withPromotionLock } from "../shared/build_mutex.js";
import {
  createInitialSubstrateState, loadSubstrateState, saveSubstrateState, substrateStateExists,
} from "./state.js";
import { runScaffolder as realScaffolder } from "./scaffolder.js";
import { runFillers as realFillers } from "./filler.js";
import { runReviewer as realReviewer } from "./reviewer.js";
import { buildTargets as realBuild } from "./build.js";
import { coordinate as realCoordinate } from "./coordinate.js";
import type { RoundReport, SubstrateState } from "./types.js";

export const BUILD_CAP = 10;
export const REVIEW_CAP = 3;
export const COORD_CAP = 3;
export const FILLER_CONCURRENCY = 4;

export interface SubstratePipelineDeps {
  runScaffolder: typeof realScaffolder;
  runFillers: typeof realFillers;
  runReviewer: typeof realReviewer;
  buildTargets: typeof realBuild;
  coordinate: typeof realCoordinate;
  writePlan?: (runDir: string, md: string) => Promise<void>;
}

const realDeps: SubstratePipelineDeps = {
  runScaffolder: realScaffolder, runFillers: realFillers, runReviewer: realReviewer,
  buildTargets: realBuild, coordinate: realCoordinate,
  writePlan: async (runDir, md) => { await mkdir(runDir, { recursive: true }); await writeFile(path.join(runDir, "plan.md"), md, "utf8"); },
};

/**
 * Canned no-op deps for `--dry-run`: drive one clean build→review→coordinate→done
 * cycle with NO side effects (no real workers, no real Causalean mutation). The
 * requirement gate, state, and artifact writes still run — that is the mechanics
 * we want to exercise. `coordinate` here is the canned no-op, so the real
 * `coordinate()` (codex agent + Causalean mutation) is never invoked under dry-run.
 */
export function dryRunDeps(): SubstratePipelineDeps {
  let scaffoldCalls = 0;
  return {
    runScaffolder: async () => {
      scaffoldCalls += 1;
      return scaffoldCalls === 1
        ? { decision: "build", plan_markdown: "[dry-run]", codex_prompts: [{ id: "d", target_decls: [], prompt: "dry" }] }
        : { decision: "review", plan_markdown: "[dry-run]", codex_prompts: [] };
    },
    runFillers: async () => [],
    buildTargets: async () => ({ ok: true, errors: [], sorryCount: 0, perFile: {} }),
    runReviewer: async () => ({
      pass: true, findings: "",
      checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true },
    }),
    coordinate: async () => ({ ok: true, log: "[dry-run] would coordinate (no files moved)" }),
  };
}

async function listLeanFiles(leanDir: string): Promise<string[]> {
  const entries = await readdir(leanDir, { withFileTypes: true }).catch(() => []);
  const files: string[] = [];
  for (const entry of entries) {
    const abs = path.join(leanDir, entry.name);
    if (entry.isDirectory()) files.push(...await listLeanFiles(abs));
    else if (entry.isFile() && entry.name.endsWith(".lean")) files.push(abs);
  }
  return files.sort();
}

function leanModuleTargets(leanDir: string, modulePrefix: string, files: string[]): string[] {
  // why: nested Lean files map to dotted module path segments, not basenames.
  return files.map((f) =>
    `${modulePrefix}.${path.relative(leanDir, f).replace(/\.lean$/, "").split(path.sep).join(".")}`);
}

export async function runSubstratePipeline(
  opts: { repoRoot: string; slug: string; resume: boolean; dryRun?: boolean },
  deps?: SubstratePipelineDeps,
): Promise<SubstrateState> {
  const { repoRoot, slug } = opts;
  // Honor an explicitly-passed deps bundle; otherwise pick canned dry-run deps
  // (no real agents / no real promotion) when dryRun, else the real deps.
  const d: SubstratePipelineDeps = deps ?? (opts.dryRun ? dryRunDeps() : realDeps);
  const runDir = substrateRunDir(repoRoot, slug);
  const leanDir = substrateLeanDir(repoRoot, slug);
  const modulePrefix = substrateModulePrefix(slug);
  const writePlan = d.writePlan ?? realDeps.writePlan!;

  // 1. Requirement gate.
  const req = await ensureRequirement(repoRoot, slug);
  if (req.status === "bootstrapped") {
    const msg = `Wrote a blank requirement.md to ${runDir}/requirement.md — fill it in and re-run \`causalsmith study ${slug}\`.`;
    console.log(msg);
    return { ...createInitialSubstrateState(slug), phase: "halted", terminalMessage: msg };
  }
  if (req.status === "invalid") {
    const msg = `requirement.md is missing/empty sections: ${req.check?.missingSections.join(", ")}. Fill them in and re-run.`;
    console.log(msg);
    return { ...createInitialSubstrateState(slug), phase: "halted", terminalMessage: msg };
  }
  const requirement = req.text!;

  // 2. State.
  if (!opts.resume && (await substrateStateExists(repoRoot, slug))) {
    throw new Error(`substrate state already exists for ${slug}; use --resume`);
  }
  let state = opts.resume ? await loadSubstrateState(repoRoot, slug) : createInitialSubstrateState(slug);
  let planMarkdown: string | null = null;

  // On resume, reload the plan ledger so the scaffolder regains its status
  // context. Best-effort — ignore read errors.
  if (opts.resume) {
    planMarkdown = await readFile(path.join(runDir, "plan.md"), "utf8").catch(() => null);
  }

  // 3. Loop.
  for (;;) {
    if (state.phase === "build") {
      // Scaffold step: the scaffolder plans + emits filler prompts (or decides
      // review/escalate). On a `build` decision we PERSIST the prompts and
      // advance to the resumable `fill` phase — a crash/stop/parse-failure after
      // this checkpoint resumes into filling WITHOUT re-running the (expensive)
      // scaffolder.
      const out = await d.runScaffolder({
        repoRoot, runDir, slug, requirement, leanDir, modulePrefix,
        planMarkdown, lastReport: state.lastReport, lastReview: state.lastReview,
        buildRounds: state.buildRounds, buildCap: BUILD_CAP,
      });
      planMarkdown = out.plan_markdown;
      await writePlan(runDir, out.plan_markdown);
      state.lastReview = null; // consumed

      if (out.decision === "escalate") {
        state.phase = "escalated";
        state.terminalMessage = `Scaffolder escalated: ${out.escalation?.reason ?? "(no reason)"}`;
      } else if (out.decision === "review") {
        state.phase = "review";
      } else {
        state.pendingPrompts = out.codex_prompts;
        state.phase = "fill";
      }
      await saveSubstrateState(repoRoot, slug, state);
    } else if (state.phase === "fill") {
      // Proof-fill step (resumable): run the codex fillers on the persisted
      // prompts, rebuild, then hand control back to the scaffolder (phase
      // `build`) so it assesses the build and decides review vs. another round.
      const reports = await d.runFillers({ repoRoot, runDir, round: state.buildRounds + 1, leanDir, modulePrefix, prompts: state.pendingPrompts, concurrency: FILLER_CONCURRENCY });
      const files = await listLeanFiles(leanDir);
      const targets = files.length > 0
        ? leanModuleTargets(leanDir, modulePrefix, files)
        : [modulePrefix];
      const build = await d.buildTargets(repoRoot, targets);
      const report: RoundReport = { round: state.buildRounds + 1, fillers: reports, build };
      state.lastReport = report;
      state.buildRounds += 1;
      state.moduleFiles = files;
      state.pendingPrompts = []; // consumed
      await saveRound(runDir, report);
      if (state.buildRounds >= BUILD_CAP) {
        state.phase = "halted";
        state.terminalMessage = `Reached BUILD_CAP (${BUILD_CAP}) without the scaffolder requesting review.`;
      } else {
        state.phase = "build";
      }
      await saveSubstrateState(repoRoot, slug, state);
    } else if (state.phase === "review") {
      const verdict = await d.runReviewer({ repoRoot, runDir, round: state.reviewRounds + 1, slug, requirement, leanDir, modulePrefix });
      state.lastReview = verdict;
      let reviewPassed = verdict.pass;
      if (verdict.pass) {
        const files = await listLeanFiles(leanDir);
        const targets = files.length > 0
          ? leanModuleTargets(leanDir, modulePrefix, files)
          : [modulePrefix];
        const build = await d.buildTargets(repoRoot, targets);
        // A model PASS is not enough; deterministic Lean diagnostics must also be sorry-free.
        if (!build.ok || build.sorryCount !== 0) {
          state.moduleFiles = files;
          state.lastReport = { round: state.buildRounds, fillers: [], build };
          state.lastReview = {
            ...verdict,
            pass: false,
            findings: [`deterministic build gate rejected reviewer PASS: ok=${build.ok}, sorryCount=${build.sorryCount}`, verdict.findings].filter(Boolean).join("\n"),
            checks: { ...verdict.checks, sorry_free: false }, // why: saved verdict must reflect deterministic build failure, not only sorry count.
          };
          reviewPassed = false;
        }
      }
      if (reviewPassed) {
        state.phase = "coordinate";
      } else {
        state.reviewRounds += 1;
        if (state.reviewRounds >= REVIEW_CAP) {
          state.phase = "halted";
          state.terminalMessage = `Reached REVIEW_CAP (${REVIEW_CAP}); last findings: ${state.lastReview?.findings ?? verdict.findings}`;
        } else {
          state.phase = "build";
        }
      }
    } else if (state.phase === "coordinate" || state.phase === "promote") {
      // `promote` is the legacy phase name; treat an in-flight run's `promote`
      // state as `coordinate`.
      const files = await listLeanFiles(leanDir);
      // Serialize coordination across concurrent `--study` runs: the whole step
      // (Causalean root edit + merges into shared existing files + lake build +
      // library_index + embed + doc:gen) mutates the shared Causalean, so two
      // runs must never interleave — otherwise they clobber each other's
      // snapshots and race on the `.lake` build dir. A queued run waits here.
      const res = await withPromotionLock(causaleanRoot(repoRoot), () =>
        d.coordinate({
          repoRoot, slug, leanDir, requirement, modulePrefix, runDir,
          leanFiles: files, round: state.coordinateRounds + 1,
          lastFailureLog: state.lastCoordinateLog,
        }));
      if (res.ok) {
        state.phase = "done";
        state.terminalMessage = "Coordinated into Causalean.";
      } else if (res.timedOut) {
        // The verify chain (build/index/embed/doc) was watchdog-killed AFTER the
        // substrate files were promoted into Causalean — it went silent for the
        // full timeout without exiting (a genuine hang, or killed mid-flight). We
        // do NOT roll back (that destroys already-promoted work and a mid-build
        // rollback is unsafe) and do NOT burn a retry. Escalate: a human verifies
        // and keeps or reverts. The promotion is UNVERIFIED until then.
        state.phase = "escalated";
        state.terminalMessage =
          "Coordinate verify chain timed out (watchdog kill after going silent) AFTER the substrate files were promoted into Causalean. NOT rolled back and NOT retried — a rollback would destroy already-promoted work, and the verify step may have hung or been mid-compile. The promotion is UNVERIFIED: a human must re-run the FULL integration gate — `lake build` → `lake exe library_index` (in the Causalean root) → `npm run embed:library` → `npm run lint:embeddings` → `npm run doc:gen` → `npm run doc:check` (in tools/) — then either keep the promotion or revert it manually. Last log tail:\n" +
          res.log.slice(-2000);
      } else {
        state.coordinateRounds += 1;
        state.lastCoordinateLog = res.log.slice(-4000);
        if (state.coordinateRounds >= COORD_CAP) {
          state.phase = "halted";
          state.terminalMessage = `Reached COORD_CAP (${COORD_CAP}); coordination failed and was rolled back; Causalean restored. Last failing log:\n${res.log.slice(-2000)}`;
        } else {
          // Retry: re-enter coordinate with the failure log fed back to codex.
          state.phase = "coordinate";
        }
      }
    } else {
      // done | halted | escalated
      await saveSubstrateState(repoRoot, slug, state);
      return state;
    }
    await saveSubstrateState(repoRoot, slug, state);
  }
}

async function saveRound(runDir: string, report: RoundReport): Promise<void> {
  await mkdir(runDir, { recursive: true });
  await writeFile(path.join(runDir, `round_${report.round}.json`), `${JSON.stringify(report, null, 2)}\n`, "utf8");
}
