import { readFile } from "node:fs/promises";
import { repairLatexStringsDeep } from "../discovery/core/latex_serialization.js";

/**
 * Uniform loader for the presentation pipeline's JSON caches (equivalence /
 * proof-audit / gate / p1 / P2 `_cache_keys` / components). One shape for what
 * every call site used to hand-roll:
 *   - absent or unreadable file → the supplied defaults (or `{}`);
 *   - `defaults` supplies required sub-map skeletons (e.g. gate_cache's three
 *     verdict maps) so consumers never null-check;
 *   - the legacy-escape read-repair runs on every load by default: cache VALUES
 *     are model-authored LaTeX and pre-escape-fix runs persisted corrupted
 *     strings (lost `\to`/`\ref`), while cache KEYS are input-content hashes,
 *     so repairing values never invalidates a cache. Pass `repair: false` only
 *     for caches whose values are NOT model-authored LaTeX (e.g. the components
 *     cache, whose values are Lean-derived text guarded by zod).
 *
 * Saving stays `writeJsonAtomic` at each site (a crash or concurrent-worker
 * race mid-write must not corrupt the cache; the next run would throw on parse
 * until the operator deletes it and re-pays every cached verdict).
 */
export async function loadJsonCache<T extends object>(
  path: string,
  opts: { defaults?: object; repair?: boolean } = {},
): Promise<T> {
  const cache = {
    ...(opts.defaults ?? {}),
    ...(JSON.parse(await readFile(path, "utf8").catch(() => "{}")) as object),
  } as T;
  if (opts.repair !== false) repairLatexStringsDeep(cache);
  return cache;
}
