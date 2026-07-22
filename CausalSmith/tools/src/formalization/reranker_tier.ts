import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";

/**
 * Phase 2c cross-encoder reranker — TS surface. The heavy model lives behind the warm
 * `scripts/rerank_daemon.py` (spawned on first use); this module only shells out to the client
 * `scripts/rerank_query.py`, which sends decl NAMES and gets back per-name relevance scores
 * (passage text is built Python-side from the index, identical to training). Every failure
 * (no model, python missing, stale) degrades to "no reranking" — retrieval never breaks.
 */

export interface RerankerMeta {
  model: string;
  base: string;
  passage: string;
  pool: number;
}

/** Load the committed reranker sidecar, or null when reranking is not configured. */
export function loadRerankerMeta(root: string): RerankerMeta | null {
  const metaPath = path.join(root, "doc", "retrieval_reranker.meta.json");
  if (!fs.existsSync(metaPath)) return null;
  try {
    const m = JSON.parse(fs.readFileSync(metaPath, "utf8")) as Partial<RerankerMeta>;
    if (!m.model) return null;
    return { model: m.model, base: m.base ?? "", passage: m.passage ?? "nbr", pool: m.pool ?? 50 };
  } catch {
    return null;
  }
}

/** True when the reranker meta AND its (gitignored) model directory are both present. */
export function rerankerAvailable(root: string): boolean {
  const meta = loadRerankerMeta(root);
  if (!meta) return false;
  const dir = path.isAbsolute(meta.model) ? meta.model : path.join(root, meta.model);
  return fs.existsSync(dir);
}

export interface RerankRequest { query: string; names: string[]; }

/**
 * Score each request's candidate names against its query with the cross-encoder, in ONE
 * subprocess call (the daemon holds the model warm across requests). Returns a score array per
 * request, aligned to `names`. On any failure returns null so the caller keeps the pre-rerank
 * order. `timeoutMs` caps a stuck model load (default 300 s — the first call cold-starts the
 * daemon ~10 s; later calls are ~1 s).
 */
export function rerankBatch(reqs: RerankRequest[], timeoutMs = 300_000): number[][] | null {
  if (reqs.length === 0) return [];
  const script = path.resolve(import.meta.dirname, "..", "..", "scripts", "rerank_query.py");
  if (!fs.existsSync(script)) return null;
  const out = path.join(os.tmpdir(), `rerank_${process.pid}_${reqs.length}.json`);
  try {
    execFileSync("python3", [script, "--out", out], {
      input: reqs.map((r) => JSON.stringify({ query: r.query.replace(/\r?\n/g, " "), names: r.names })).join("\n"),
      timeout: timeoutMs,
      maxBuffer: 64 * 1024 * 1024,
    });
    const scores = JSON.parse(fs.readFileSync(out, "utf8")) as number[][];
    // Shape guard: one score row per request, each aligned to that request's names.
    if (!Array.isArray(scores) || scores.length !== reqs.length) return null;
    for (let i = 0; i < reqs.length; i++) {
      if (!Array.isArray(scores[i]) || scores[i].length !== reqs[i].names.length) return null;
    }
    return scores;
  } catch {
    return null;
  } finally {
    fs.rmSync(out, { force: true });
  }
}
