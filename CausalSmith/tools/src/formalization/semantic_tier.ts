import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { inClusterSubstrate, type ClusterKey } from "../constants.js";

export interface SemHit { name: string; sim: number; }
export interface SemOpts { k: number; floor: number; cluster: ClusterKey | null; exclude: Set<string>; graphProp?: number; }

/** Cheap runtime staleness check (defense-in-depth; the authoritative content check is
 *  scripts/check_embeddings_fresh.py). Catches added/removed decls and a new index commit. */
export function isEmbeddingsStale(
  meta: { names: string[]; index_commit?: string },
  index: { commit?: string; names: string[] },
): boolean {
  if (meta.index_commit !== index.commit) return true;
  if (meta.names.length !== index.names.length) return true;
  const m = new Set(meta.names);
  return !index.names.every((n) => m.has(n));
}

export class SemanticTier {
  constructor(
    private names: string[],
    private vecs: Float32Array, // row-major, normalized (the base "nl" view)
    private dim: number,
    private fileOf: (name: string) => string | undefined,
    // Additional row-aligned view matrices (e.g. statement / dependency-graph neighbourhood).
    // A decl's similarity is the MAX cosine over the base view and every extra view, so a
    // view can only ever raise a decl's score — never lower a hit the base view already found.
    private extraViews: Float32Array[] = [],
    // Undirected refs-graph neighbourhood as row indices per decl (Ch4 graph propagation).
    // Empty ⇒ propagation is a no-op regardless of `opts.graphProp`.
    private adjacency: number[][] = [],
  ) {}

  /** Max cosine of decl row `i` over the base view and every extra view (multi-view scoring). */
  private simOf(i: number, q: Float32Array): number {
    const off = i * this.dim;
    let best = 0;
    for (let d = 0; d < this.dim; d++) best += this.vecs[off + d] * q[d];
    for (const view of this.extraViews) {
      let dot = 0;
      for (let d = 0; d < this.dim; d++) dot += view[off + d] * q[d];
      if (dot > best) best = dot;
    }
    return best;
  }

  topK(q: Float32Array, opts: SemOpts): SemHit[] {
    const n = this.names.length;
    const raw = new Float32Array(n);
    for (let i = 0; i < n; i++) raw[i] = this.simOf(i, q);

    // Ch4 one-hop graph propagation: a word-poor target whose refs-graph neighbour matches the
    // query gets score'(d) = sim(d) + λ·max_{n∈adj(d)} sim(n). λ<1 keeps the boost below a direct
    // hit; it can lift a below-floor gap target over the floor via its neighbour. Uses RAW sims of
    // neighbours (pre-propagation) so it stays a single hop.
    const lam = opts.graphProp ?? 0;
    const eff = lam > 0 && this.adjacency.length === n ? new Float32Array(n) : raw;
    if (eff !== raw) {
      for (let i = 0; i < n; i++) {
        let bestNbr = 0;
        for (const j of this.adjacency[i]) if (raw[j] > bestNbr) bestNbr = raw[j];
        eff[i] = raw[i] + lam * bestNbr;
      }
    }

    const hits: SemHit[] = [];
    for (let i = 0; i < n; i++) {
      const name = this.names[i];
      if (opts.exclude.has(name)) continue;
      if (opts.cluster) {
        const f = this.fileOf(name);
        // Membership in the requested cluster's roots — the SAME predicate lexical retrieval
        // uses. A single-label assignment drops the substrate clusters share (Causalean/PO/).
        if (!f || !inClusterSubstrate(f, opts.cluster)) continue;
      }
      if (eff[i] >= opts.floor) hits.push({ name, sim: eff[i] });
    }
    hits.sort((a, b) => b.sim - a.sim || a.name.localeCompare(b.name));
    return hits.slice(0, opts.k);
  }
}

/** Load an extra embedding view (e.g. "nbr", "stmt"), reordered to match `primaryNames` so
 *  its rows align with the base view. Returns null (view simply skipped) when the sidecar is
 *  absent, wrong-dim, stale vs the index commit, or truncated — never throws. */
function loadAlignedView(
  root: string,
  view: string,
  primaryNames: string[],
  dim: number,
  indexCommit?: string,
): Float32Array | null {
  const metaPath = path.join(root, "doc", `library_embeddings.${view}.meta.json`);
  const f32Path = path.join(root, "doc", `library_embeddings.${view}.f32`);
  if (!fs.existsSync(metaPath) || !fs.existsSync(f32Path)) return null;
  try {
    const meta = JSON.parse(fs.readFileSync(metaPath, "utf8")) as { dim: number; names: string[]; index_commit?: string };
    if (meta.dim !== dim) return null;
    if (indexCommit && meta.index_commit !== indexCommit) {
      console.warn(`[semantic_tier] ${view} view stale vs index — skipping (run \`npm run embed:library -- --view ${view}\`)`);
      return null;
    }
    const buf = fs.readFileSync(f32Path);
    if (buf.byteLength !== meta.names.length * dim * 4) return null;
    const raw = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);
    const rowOf = new Map<string, number>();
    meta.names.forEach((n, i) => rowOf.set(n, i));
    const aligned = new Float32Array(primaryNames.length * dim);
    for (let i = 0; i < primaryNames.length; i++) {
      const r = rowOf.get(primaryNames[i]);
      if (r !== undefined) aligned.set(raw.subarray(r * dim, (r + 1) * dim), i * dim);
    }
    return aligned;
  } catch {
    return null;
  }
}

/** Undirected refs-graph neighbourhood as row indices per decl, aligned to `names` row order.
 *  Neighbours = a decl's `refs` plus its reverse-refs (what uses it), capped like the nbr view
 *  so propagation cost stays bounded. Rows for names absent from the index get no neighbours. */
const MAX_ADJ = 16;
export function buildAdjacency(names: string[], entries: { name: string; refs?: string[] | null }[]): number[][] {
  const row = new Map<string, number>();
  names.forEach((n, i) => row.set(n, i));
  const adj: Set<number>[] = names.map(() => new Set<number>());
  for (const e of entries) {
    const ri = row.get(e.name);
    if (ri === undefined) continue;
    for (const r of e.refs ?? []) {
      const rj = row.get(r);
      if (rj === undefined || rj === ri) continue;
      adj[ri].add(rj); // ri references rj
      adj[rj].add(ri); // …so rj is used-by ri (reverse edge) — undirected neighbourhood
    }
  }
  return adj.map((s) => [...s].slice(0, MAX_ADJ));
}

/** Load the embedding sidecar produced by embed_library.py. Returns null if absent (semantic tier disabled). */
export function loadSemanticTier(root: string, fileOf: (name: string) => string | undefined): SemanticTier | null {
  const metaPath = path.join(root, "doc", "library_embeddings.meta.json");
  const f32Path = path.join(root, "doc", "library_embeddings.f32");
  if (!fs.existsSync(metaPath) || !fs.existsSync(f32Path)) return null;
  const meta = JSON.parse(fs.readFileSync(metaPath, "utf8")) as { dim: number; names: string[]; index_commit?: string };
  const lib = JSON.parse(fs.readFileSync(path.join(root, "doc", "library_index.json"), "utf8")) as {
    commit?: string;
    entries: { name: string; refs?: string[] | null }[];
  };
  const idx = { commit: lib.commit, names: lib.entries.map((e) => e.name) };
  if (isEmbeddingsStale(meta, idx)) {
    console.warn("[semantic_tier] embeddings stale vs library_index.json — disabling semantic tier (run `npm run embed:library`)");
    return null;
  }
  const buf = fs.readFileSync(f32Path);
  const expectedBytes = meta.names.length * meta.dim * 4;
  if (!Number.isInteger(meta.dim) || meta.dim <= 0 || buf.byteLength !== expectedBytes) {
    // why: stale/truncated sidecars otherwise produce undefined vector reads.
    console.warn(`[semantic_tier] embeddings shape mismatch: got ${buf.byteLength} bytes, expected ${expectedBytes} (${meta.names.length}×${meta.dim}×4) — disabling semantic tier`);
    return null;
  }
  const vecs = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);

  // Multi-view (Phase 1): fold in extra decl views (statement structure, dependency-graph
  // neighbourhood) when their sidecars are present + fresh. Scored by max-sim (see SemanticTier),
  // so a view only ever helps. `RETRIEVAL_VIEWS` (comma list, or "none"/"") overrides which
  // views load — used to A/B them on the eval; default enables both.
  // Default: neighbourhood view only. On the eval it beat nl-only across every stratum
  // (gap hit@3 +10%, recall@10 +13%); the `stmt` view diluted hit@3 off-the-shelf (a NL
  // query vs raw Lean syntax is noisy in un-fine-tuned bge) so it is left off by default —
  // set RETRIEVAL_VIEWS=nbr,stmt to A/B it, e.g. once a fine-tuned encoder lands (Phase 2).
  const enabled = (process.env.RETRIEVAL_VIEWS ?? "nbr")
    .split(",").map((s) => s.trim()).filter((s) => s && s !== "none");
  const extraViews: Float32Array[] = [];
  for (const view of enabled) {
    const av = loadAlignedView(root, view, meta.names, meta.dim, lib.commit);
    if (av) extraViews.push(av);
  }
  const adjacency = buildAdjacency(meta.names, lib.entries);
  return new SemanticTier(meta.names, vecs, meta.dim, fileOf, extraViews, adjacency);
}

/**
 * Embed query texts at runtime with the SAME model as `embed_library.py` (via the
 * `scripts/embed_text.py` subprocess), so a live query can be cosine-matched against the
 * decl vectors. Returns one normalized vector per input text (empty array for empty input).
 * NB: loads the model once per call (~30 s) — batch all queries into ONE call; do not call
 * per-item in a loop. Throws if python/model/meta are unavailable; callers should catch and
 * fall back to lexical-only.
 */
export function embedQueries(texts: string[], root: string): Float32Array[] {
  if (texts.length === 0) return [];
  const meta = JSON.parse(fs.readFileSync(path.join(root, "doc", "library_embeddings.meta.json"), "utf8")) as { dim: number };
  const dim = meta.dim;
  const script = path.resolve(import.meta.dirname, "..", "..", "scripts", "embed_text.py");
  const out = path.join(os.tmpdir(), `ceq_${process.pid}_${texts.length}.f32`);
  // 180 s cap: a stuck model load must degrade to lexical, never stall the F2 pipeline.
  execFileSync("python3", [script, "--out", out], {
    input: texts.map((t) => t.replace(/\r?\n/g, " ")).join("\n"),
    timeout: 180_000,
    maxBuffer: 64 * 1024 * 1024,
  });
  const buf = fs.readFileSync(out);
  const all = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);
  fs.rmSync(out, { force: true });
  return texts.map((_, i) => all.subarray(i * dim, (i + 1) * dim));
}
