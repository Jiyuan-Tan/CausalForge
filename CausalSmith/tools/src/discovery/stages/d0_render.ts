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
import { mkdir, rename, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { artifactPaths } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { coreJsonPath } from "./d0_core.js";
import { renderCoreTex } from "../core/render_tex.js";
import { assertCanonicalAlignedRowTerminators } from "../core/latex_serialization.js";
import { runGates } from "../framework/gates.js";
import { proseConsistencyGate } from "../framework/gate_registrations.js";
import { loadWorkingState } from "./d0_working.js";
import { pendingStatementSupersessions, readRoundProposals } from "../solve/proposals.js";
import { readTypedCore } from "../core/core_io.js";
import {
  loadSemanticManifest,
  validateCoreManifest,
  validateRenderedManifest,
} from "../semantic_manifest.js";

export interface Stage0RenderResult {
  message: string;
  texPath: string;
}

async function publishRenderedTex(tex: string, destination: string): Promise<void> {
  const staged = `${destination}.tmp-${process.pid}-${Date.now()}`;
  try {
    await writeFile(staged, tex, "utf8");
    // The staging file lives beside the destination, so rename atomically
    // replaces the prior source preview without exposing a partial write.
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
  const semanticManifest = await loadSemanticManifest(args.ctx);
  validateCoreManifest(semanticManifest, "core", core);
  const paths = artifactPaths(args.ctx, args.state);
  await mkdir(path.dirname(paths.tex), { recursive: true });
  const tex = renderCoreTex(core);
  assertCanonicalAlignedRowTerminators(tex, paths.tex);
  validateRenderedManifest(semanticManifest, tex);

  // D reviews the structured/shared paper view, not a PDF. Publish the source
  // preview only; typography, packages, and PDF compilation belong to the later
  // paper/publication boundary and must not block mathematical discovery.
  await publishRenderedTex(tex, paths.tex);

  // Prose-drift lint (advisory, non-blocking): the D0 change-apply loop has no prose
  // channel and this render is verbatim, so a late headline reframe can leave the
  // tldr/project_justification asserting a claim the revised statements no longer
  // deliver. Surface it so the D0.R prose-sync / the D0.5 referee fixes it at source
  // instead of rendering the stale overclaim silently.
  const proseWarnings = runGates([proseConsistencyGate], core).warn;
  let message = "Stage 0-RENDER published the deterministic TeX source preview (canonical aligned rows; no compilation in D)";
  if (proseWarnings.length > 0) {
    const lines = proseWarnings.map((w) => `  ⚠ ${w.detail}`);
    const banner = `PROSE-DRIFT — ${proseWarnings.length} warning(s) (prose may have drifted from the reframed statements; sync the prose fields):\n${lines.join("\n")}`;
    console.warn(banner);
    message += `\n${banner}`;
  }
  return { message, texPath: paths.tex };
}
