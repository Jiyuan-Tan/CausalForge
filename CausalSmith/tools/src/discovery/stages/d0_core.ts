// D0 core path helper.
//
// The former D0-CORE author (which pre-committed proof routes + a lemma
// decomposition for D0-PROVE to follow) is RETIRED — deciding the decomposition
// is part of solving, so the math solver owns it end-to-end (see `stage0_solve.ts`,
// D0_CORE_REDESIGN.md §4 simplified). This module now only exports the shared path
// of the solved core `<qid>_core.json`, consumed by D0-SOLVE / D0-RENDER / D0.R /
// D0.5.
import { artifactPath } from "../../paths.js";
import type { PipelineContext } from "../../types.js";

/** Filesystem path for `<qid>_core.json` (the solved core), alongside the .tex artifacts. */
export function coreJsonPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "core.json", [`${ctx.qid}_core.json`]);
}
