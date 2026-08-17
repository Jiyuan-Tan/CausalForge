// CausalSmith/tools/src/substrate/state.ts
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import path from "node:path";
import { substrateLeanDir, substrateStatePath } from "./paths.js";
import { substrateStateSchema, type SubstrateState } from "./types.js";

export function createInitialSubstrateState(slug: string): SubstrateState {
  return {
    slug,
    phase: "build",
    buildRounds: 0,
    reviewRounds: 0,
    coordinateRounds: 0,
    lastCoordinateLog: null,
    moduleFiles: [],
    pendingPrompts: [],
    lastReport: null,
    lastReview: null,
    layeringReviewStatus: "current",
    terminalMessage: null,
    terminalRequirementHash: null,
    terminalEscalationKind: null,
    requirementVersion: 0,
  };
}

export async function substrateStateExists(repoRoot: string, slug: string): Promise<boolean> {
  return existsSync(substrateStatePath(repoRoot, slug));
}

export async function loadSubstrateState(repoRoot: string, slug: string): Promise<SubstrateState> {
  const file = substrateStatePath(repoRoot, slug);
  const raw = JSON.parse(await readFile(file, "utf8")) as Record<string, any>;
  const checks = raw.lastReview?.checks;
  if (checks && !("layered" in checks)) {
    // Legacy reviewer verdicts predate the layering audit. Preserve their
    // evidence but never manufacture a passing `layered:true` result.
    checks.layered = false;
    raw.lastReview.pass = false;
    raw.lastReview.findings = [
      raw.lastReview.findings,
      "Legacy review predates the dependency-layering check; a fresh review is required before coordination.",
    ].filter(Boolean).join("\n");
    raw.layeringReviewStatus = "legacy-unreviewed";
    const terminal = raw.phase === "done" || raw.phase === "halted" || raw.phase === "escalated";
    const resumablePostReview = raw.phase === "review" || raw.phase === "coordinate" || raw.phase === "promote";
    if (terminal) {
      // Terminal authority belongs to the pipeline/orchestrator that set it. Migration may mark
      // legacy evidence stale, but must never reopen the phase or clear its terminal receipt/hash.
      const audit = raw.phase === "done"
        ? "Legacy completed output predates the dependency-layering check; audit the promoted modules separately."
        : "Legacy terminal output predates the dependency-layering check; audit it separately before any authorized recovery.";
      raw.terminalMessage = [raw.terminalMessage, audit].filter(Boolean).join("\n");
    } else if (resumablePostReview) {
      if (existsSync(substrateLeanDir(repoRoot, slug))) {
        raw.phase = "review";
        raw.terminalMessage = null;
      } else {
        raw.phase = "halted";
        raw.terminalMessage = [
          raw.terminalMessage,
          "Legacy layering review is missing and staging sources are unavailable; audit the prior output separately.",
        ].filter(Boolean).join("\n");
      }
    }
  }
  return substrateStateSchema.parse(raw);
}

export async function saveSubstrateState(repoRoot: string, slug: string, state: SubstrateState): Promise<void> {
  const file = substrateStatePath(repoRoot, slug);
  await mkdir(path.dirname(file), { recursive: true });
  const tmp = `${file}.tmp`;
  await writeFile(tmp, `${JSON.stringify(state, null, 2)}\n`, "utf8");
  await rename(tmp, file);
}
