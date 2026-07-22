#!/usr/bin/env -S node --import tsx
/**
 * Run the REAL proof-review loop (`runProofReviewLoop`) — the actual F3 (it absorbs
 * the legacy proof/review stages): reviewer at the top of each iteration, then the filler, refresh,
 * loop until every frozen theorem's uses-closure is complete+matched (final dual-model
 * convergence review) or it escalates. Drives the migrated module to zero sorrys.
 *
 * Usage: node --import tsx tools/bin/f3_loop.ts <qid> <spec> <leanDir>
 * Makes live Codex+Claude calls and edits <leanDir>. Run from the CausalSmith package root.
 */
import path from "node:path";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import { execSync } from "node:child_process";
import { loadState } from "../src/state.js";
import { artifactPaths, defaultDeps } from "../src/pipeline_support.js";
import { coreJsonPath } from "../src/discovery/stages/d0_core.js";
import { runProofReviewLoop } from "../src/formalization/proof_review_loop.js";
import { runStage2 } from "../src/formalization/stage2.js";
import { startSharedLeanLsp } from "../src/shared/lean_lsp_server.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


async function main() {
  const [qid, spec, leanDirArg] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
  if (!qid || !spec || !leanDirArg) {
    console.error("Usage: f3_loop.ts <qid> <spec> <leanDir>");
    process.exit(1);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const ctx = { repoRoot, qid, specialization: spec, dryRun: false, resume: true, noveltyTarget: "field" as const };
  const paths = artifactPaths(ctx, state);
  const deps = defaultDeps(ctx);
  const leanDir = path.isAbsolute(leanDirArg) ? leanDirArg : path.join(repoRoot, leanDirArg);

  // Explicit prebuild: warm the leanDir's oleans BEFORE the reviewer so codex's lean-lsp loads
  // imports from cache instead of cold-elaborating the closure. Does NOT warm the in-memory server
  // (each codex run spawns its own) — that needs a shared server — but it removes the import-load
  // cost. Non-fatal: a build failure just means lean-lsp elaborates as before.
  try {
    const relMod = path.relative(repoRoot, leanDir).replace(/[\\/]/g, ".");
    const mods = readdirSync(leanDir)
      .filter((f) => f.endsWith(".lean"))
      .map((f) => `${relMod}.${f.replace(/\.lean$/, "")}`);
    if (mods.length > 0) {
      console.log(`[f3-loop] prebuild: lake build ${mods.length} module(s) to warm oleans…`);
      execSync(`lake build ${mods.join(" ")}`, { cwd: repoRoot, stdio: "inherit", timeout: 30 * 60 * 1000 });
      console.log(`[f3-loop] prebuild done.`);
    }
  } catch (e) {
    console.warn(`[f3-loop] prebuild failed (continuing; lean-lsp will elaborate on demand): ${e instanceof Error ? e.message : String(e)}`);
  }

  // Shared lean-lsp server: ONE streamable-HTTP `lean-lsp-mcp` (= one `lake serve`)
  // that every codex process this loop spawns — reviewer, its subagents, the
  // per-target fillers, the convergence reviewers — attaches to via URL, instead
  // of each spawning its own and re-paying the ~52s import-elaboration cold-start.
  // Exporting the URL flips `leanLspCodexFlags` (codex.ts) into shared mode for
  // every codex call inside this process. Non-fatal: if the server fails to boot,
  // we fall back to per-process stdio lean-lsp (slower, but correct).
  let shared: Awaited<ReturnType<typeof startSharedLeanLsp>> | null = null;
  try {
    console.log(`[f3-loop] starting shared lean-lsp HTTP server…`);
    shared = await startSharedLeanLsp(repoRoot);
    process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL = shared.url;
    console.log(`[f3-loop] shared lean-lsp at ${shared.url} (one lake serve for the whole run).`);
  } catch (e) {
    console.warn(`[f3-loop] shared lean-lsp failed to start (falling back to per-codex stdio): ${e instanceof Error ? e.message : String(e)}`);
  }

  console.log(`[f3-loop] runProofReviewLoop on ${qid}_${spec}; leanDir=${leanDir}`);
  try {
    const outcome = await runProofReviewLoop({
      ctx,
      deps,
      // Keep the standalone driver behavior aligned with the dispatcher: proof
      // hints and persistent iteration budgets must survive a checkpoint/resume.
      // Without these two fields, `f3_directive.ts` is silently ignored here and
      // every standalone launch risks operating on a detached counter snapshot.
      state,
      fillerDirective: state.flags.f3_filler_directive ?? null,
      formalizationDir: paths.formalizationDir,
      leanDir,
      texPath: paths.tex,
      corePath: coreJsonPath(ctx),
      // Phase-A re-scaffold seam (F2 revise-mode); mirrors the dispatcher wiring.
      scaffold: async ({ redirect, targets }) => {
        state.flags.scaffold_redirect = [
          redirect,
          targets.length ? `Declarations to edit (by obj_id): ${targets.join(", ")}` : "",
        ].filter(Boolean).join("\n\n");
        state.flags.scaffold_redirect_count = (state.flags.scaffold_redirect_count ?? 0) + 1;
        await runStage2({ ctx, state, deps });
      },
    });
    console.log(`\n=== F3 LOOP OUTCOME: ${qid}_${spec} ===`);
    console.log(JSON.stringify(outcome, null, 2));
    process.exitCode = outcome.status === "completed" ? 0 : 2;
  } finally {
    if (shared) {
      delete process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL;
      await shared.stop();
      console.log(`[f3-loop] shared lean-lsp stopped.`);
    }
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(70);
});
