// Re-export shim. Canonical implementation lives in shared/codex.ts so both
// the research and (future) study pipelines share one codex dispatcher
// (spec §8.2). Existing imports from `../workers/codex.js` continue to work
// unchanged.
export { runCodex, type CodexRunInput } from "../shared/codex.js";
