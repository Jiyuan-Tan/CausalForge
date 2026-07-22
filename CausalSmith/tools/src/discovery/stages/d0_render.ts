// Stage 0-RENDER — render the frozen, discharged core into the prose .tex note.
//
// The core (typed skeleton + filled proofs + prose fields) is the source of truth.
// D0-RENDER is now a DETERMINISTIC render (pure `renderCoreTex`, no LLM, no agent
// dispatch): formal parts emitted verbatim from the typed core, prose fields
// (project_justification / related_work / interpretation, per-statement notes)
// emitted into their sections. There is no \coreref-resolution failure mode — the
// render generates references by construction. Same renderer as D-1.2
// (D0_CORE_REDESIGN.md §12.7).
import { existsSync } from "node:fs";
import { copyFile, mkdir, mkdtemp, readFile, rename, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { artifactPaths } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { coreJsonPath } from "./d0_core.js";
import { CoreSchema } from "../core/schema.js";
import { renderCoreTex } from "../core/render_tex.js";
import { assertCanonicalAlignedRowTerminators } from "../core/latex_serialization.js";
import { runGates } from "../framework/gates.js";
import { proseConsistencyGate } from "../framework/gate_registrations.js";
import { loadWorkingState } from "./d0_working.js";
import { pendingStatementSupersessions, readRoundProposals } from "../solve/proposals.js";
import { spawnWithInactivityTimeout } from "../../workers/spawn.js";
import { readTypedCore } from "../core/core_io.js";
import {
  loadSemanticManifest,
  validateCoreManifest,
  validateRenderedManifest,
} from "../semantic_manifest.js";

export interface Stage0RenderResult {
  message: string;
  texPath: string;
  pdfPath: string;
  logPath: string;
}

async function publishVerifiedArtifact(source: string, destination: string): Promise<void> {
  if (!existsSync(source)) throw new Error(`Stage 0-RENDER verified artifact is missing: ${source}`);
  const staged = `${destination}.tmp-${process.pid}-${Date.now()}`;
  try {
    await copyFile(source, staged);
    // The staging file lives beside the destination, so rename is an atomic
    // publication on the same filesystem and replaces any stale canonical file.
    await rename(staged, destination);
  } finally {
    await rm(staged, { force: true });
  }
}

/** Deterministically render the frozen core into the .tex note. No LLM, no deps. */
export async function runStage0Render(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<Stage0RenderResult> {
  const corePath = coreJsonPath(args.ctx);
  if (!existsSync(corePath)) {
    // why: D0-CORE/PROVE is retired; D0-SOLVE now produces the core.
    throw new Error(`Stage 0-RENDER requires a core at ${corePath} (run D0-SOLVE first)`);
  }
  const core = await readTypedCore(corePath);
  const working = await loadWorkingState(args.ctx);
  const pendingSupersessions = pendingStatementSupersessions(await readRoundProposals(args.ctx, working));
  const coreIds = new Set(core.statements.map((statement) => statement.id));
  const duplicateChains = pendingSupersessions.filter(
    ({ obsoleteId, replacementId }) => coreIds.has(obsoleteId) && coreIds.has(replacementId),
  );
  if (duplicateChains.length > 0) {
    throw new Error(
      `Stage 0-RENDER refuses a core containing both sides of ${duplicateChains.length} pending supersession(s): ` +
        duplicateChains.map((s) => `${s.obsoleteId}→${s.replacementId}`).join(", ") + ". " +
        "Adjudicate the gated deletion first; rendering both versions would publish duplicate headline chains.",
    );
  }
  for (const statement of core.statements) {
    if (statement.proof_tex) assertCanonicalAlignedRowTerminators(statement.proof_tex, `${statement.id}.proof_tex`);
  }
  const semanticManifest = await loadSemanticManifest(args.ctx);
  validateCoreManifest(semanticManifest, "core", core);
  const paths = artifactPaths(args.ctx, args.state);
  await mkdir(path.dirname(paths.tex), { recursive: true });
  const tex = renderCoreTex(core);
  assertCanonicalAlignedRowTerminators(tex, paths.tex);
  validateRenderedManifest(semanticManifest, tex);

  // A deterministic renderer must fail here, not at a later reviewer/manual
  // maximality check. Compile in a temporary output directory so auxiliary TeX
  // files never pollute the run directory. The candidate `.tex` also stays in the
  // temporary directory until both passes succeed: a failed render must not replace
  // the last verified canonical TeX while leaving its old PDF/log beside it.
  const texOut = await mkdtemp(path.join(os.tmpdir(), "causalsmith-d0-tex-"));
  const stem = path.basename(paths.tex, path.extname(paths.tex));
  const pdfPath = path.join(path.dirname(paths.tex), `${stem}.pdf`);
  const logPath = path.join(path.dirname(paths.tex), `${stem}.log`);
  const candidateTex = path.join(texOut, `${stem}.tex`);
  try {
    await writeFile(candidateTex, tex, "utf8");
    for (let pass = 1; pass <= 2; pass++) {
      const compiled = await spawnWithInactivityTimeout(
        "pdflatex",
        ["-interaction=nonstopmode", "-halt-on-error", `-output-directory=${texOut}`, candidateTex],
        { cwd: args.ctx.repoRoot, inactivityTimeoutMs: 60_000, maxTotalMs: 120_000 },
      );
      if (compiled.exitCode !== 0 || compiled.killedDueToInactivity || compiled.killedDueToTotalTimeout) {
        const diagnostic = `${compiled.stdout}\n${compiled.stderr}`.trim().split("\n").slice(-40).join("\n");
        throw new Error(`Stage 0-RENDER pdflatex verification failed on pass ${pass} for ${paths.tex}:\n${diagnostic}`);
      }
    }
    await publishVerifiedArtifact(path.join(texOut, `${stem}.pdf`), pdfPath);
    await publishVerifiedArtifact(path.join(texOut, `${stem}.log`), logPath);
    // Publish TeX last: its successful rename is the commit point for the newly
    // verified render bundle.
    await publishVerifiedArtifact(candidateTex, paths.tex);
  } finally {
    await rm(texOut, { recursive: true, force: true });
  }

  // Prose-drift lint (advisory, non-blocking): the D0 change-apply loop has no prose
  // channel and this render is verbatim, so a late headline reframe can leave the
  // tldr/project_justification asserting a claim the revised statements no longer
  // deliver. Surface it so the D0.R prose-sync / the D0.5 referee fixes it at source
  // instead of rendering the stale overclaim silently.
  const proseWarnings = runGates([proseConsistencyGate], core).warn;
  let message = "Stage 0-RENDER rendered the prose note (deterministic; canonical aligned rows; two-pass pdflatex verified and canonical PDF/log published)";
  if (proseWarnings.length > 0) {
    const lines = proseWarnings.map((w) => `  ⚠ ${w.detail}`);
    const banner = `PROSE-DRIFT — ${proseWarnings.length} warning(s) (prose may have drifted from the reframed statements; sync the prose fields):\n${lines.join("\n")}`;
    console.warn(banner);
    message += `\n${banner}`;
  }
  return { message, texPath: paths.tex, pdfPath, logPath };
}
