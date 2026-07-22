import { z } from "zod";
import { createHash } from "node:crypto";
import { citedDependencies, renderedNodes, refTargets, envForNode, type OverrideEnv } from "./graph_view.js";
import { isUndeliveredNode } from "../graph/types.js";
import { appendAfterAnchoredEnvs, normalizeAnchoredEnvScopeMarkers, parseAnchoredEnvs } from "./tex_anchors.js";
import type { FormalizationGraph } from "../graph/types.js";

/**
 * The formal layer as a typed JSON artifact — the SOURCE OF TRUTH that P1 emits and P2/P3/P4
 * consume. `formal_layer.tex` is a derived read-only view (see `blocksToTex`). The block's
 * `obj_id` is the graph NODE id (matching every env label, in-body `\cref{obj:<id>}`, the
 * crosswalk, and the rendered `data-objid`); the `alias` (`A-1`/`T-1`) is display-only. Replaces
 * the legacy `formal_layer.tex` + `frozen_hashes.json` pair, whose LaTeX-label join key drifted
 * from the crosswalk key.
 */
export const FormalBlock = z.object({
  obj_id: z.string(), // node id — the canonical join key
  alias: z.string().nullable(), // display only (the note's P-/A-/T- anchor)
  kind: z.enum(["setup", "definition", "assumption", "lemma", "theorem", "gate"]),
  env: z.enum(["theoremv", "assumptionv", "lemmav", "definitionv", "citedv", "propositionv", "remarkv"]).nullable(), // null for setup/prose-only
  title: z.string().nullable(),
  body: z.string(), // rendered LaTeX statement
  ref_set: z.array(z.string()),
  lean: z.object({ decl: z.string(), file: z.string() }).nullable(),
  status: z.string(), // graph review.status
  provenance: z.string(),
  /** Published propositions used as Lean premises but intentionally omitted from the journal-style
   * theorem hypothesis list. These stay exact/source-bound and generate a local scope footnote. */
  cited_dependencies: z.array(z.object({
    node_id: z.string(),
    cite_id: z.string(),
    cite_key: z.string().nullable(),
    locator: z.string().nullable(),
    statement: z.string(),
    status: z.string(),
  })).default([]),
  body_hash: z.string(), // sha256 of the whitespace-normalized body — the freeze
});
export type FormalBlock = z.infer<typeof FormalBlock>;

export const FormalLayerSource = z.object({
  commit: z.string().nullable(), // pinned at P4
  blocks: z.array(FormalBlock),
});
export type FormalLayerSource = z.infer<typeof FormalLayerSource>;

/** Per-block freeze: sha256 of the whitespace-normalized body (matches the legacy `hashEnvBody`). */
export function hashBody(body: string): string {
  return createHash("sha256").update(body.replace(/\s+/g, " ").trim()).digest("hex");
}

/** One LaTeX env for a block, or "" for a non-env (setup / prose-only) block. */
export function texEnvFor(b: FormalBlock): string {
  if (!b.env) return "";
  const title = b.title ? `[${b.title}]` : "";
  const scopeMark = b.cited_dependencies.length > 0 ? "*" : "";
  return `\\begin{${b.env}}{${b.obj_id}}${title}${scopeMark}\n${b.body.trim()}\n\\end{${b.env}}`;
}

/** Reader-facing trust-boundary note. It is outside the frozen theorem body, so the mathematical
 * statement stays conventional while the machine-verification scope remains impossible to miss. */
export function citedScopeFootnote(b: FormalBlock): string {
  if (!b.env || b.cited_dependencies.length === 0) return "";
  const sources = b.cited_dependencies.map((d) => {
    const cite = d.cite_key ? `\\citep{${d.cite_key}}` : `\\texttt{${d.cite_id.replace(/^cite:/, "")}}`;
    return d.locator ? `${cite} (${d.locator})` : cite;
  });
  const joined = sources.length === 1
    ? sources[0]
    : `${sources.slice(0, -1).join(", ")} and ${sources[sources.length - 1]}`;
  return [
    `% CAUSALSMITH-CITED-SCOPE-BEGIN ${b.obj_id}`,
    `\\verificationfootnotetext{\\textbf{Formalization scope.} This result uses the published conclusion ${joined}. ` +
      `The cited source proof is not formalized here: Lean verifies its use and all remaining steps. ` +
      `If that cited conclusion is false, the portions of this result that depend on it are not certified.}`,
    `% CAUSALSMITH-CITED-SCOPE-END ${b.obj_id}`,
  ].join("\n");
}

/** One complete paper block: frozen environment plus an optional generated scope footnote. */
export function texBlockFor(b: FormalBlock): string {
  const env = texEnvFor(b);
  if (!env) return "";
  const note = citedScopeFootnote(b);
  return note ? `${env}\n${note}` : env;
}

/** The derived `.tex` view / the paper's frozen env text — shared by the P1 human view and P2's
 *  mechanical paper assembly so the two never diverge. */
export function blocksToTex(blocks: FormalBlock[]): string {
  return blocks.map(texBlockFor).filter((s) => s !== "").join("\n\n");
}

/** Re-impose generated cited-dependency footnotes after any model prose revision. Sentinels make
 * this idempotent and ensure a model cannot silently delete, soften, or duplicate the disclaimer. */
export function normalizeCitedScopeFootnotes(tex: string, blocks: FormalBlock[]): string {
  const noteById = new Map(
    blocks.map((b) => [b.obj_id, citedScopeFootnote(b)] as const).filter(([, note]) => note !== ""),
  );
  let clean = tex;
  // Match each known sentinel by its exact obj-id. A broad `[^\n]+` end-marker
  // match can swallow reader prose when a revision glues that prose to the marker
  // line. Preserve the following newline, or insert one only for that glued case.
  for (const id of noteById.keys()) {
    const escaped = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const re = new RegExp(
      `\\n?% CAUSALSMITH-CITED-SCOPE-BEGIN ${escaped}\\n[\\s\\S]*?% CAUSALSMITH-CITED-SCOPE-END ${escaped}`,
      "g",
    );
    clean = clean.replace(re, (match, offset: number, source: string) => {
      const next = source[offset + match.length];
      return next !== undefined && next !== "\n" ? "\n" : "";
    });
  }
  clean = normalizeAnchoredEnvScopeMarkers(clean, new Set(noteById.keys()));
  if (noteById.size === 0) return clean;
  return appendAfterAnchoredEnvs(clean, noteById);
}

/**
 * P4 equality lint: every env-bearing block must appear in the assembled `paper.tex` with a matching
 * body (whitespace-insensitive — reflow is not drift). Returns the obj_ids that are missing or
 * differ. Replaces the legacy frozen-hash compare with a check against the JSON source of truth.
 */
export function paperEnvMismatches(paperTex: string, blocks: FormalBlock[]): string[] {
  const norm = (s: string) => s.replace(/\s+/g, " ").trim();
  const paper = new Map(parseAnchoredEnvs(paperTex).map((e) => [e.obj_id, norm(e.body)]));
  const problems: string[] = [];
  for (const b of blocks) {
    if (!b.env) continue; // non-env (setup/prose-only) blocks are not paper envs
    const got = paper.get(b.obj_id);
    if (got === undefined) problems.push(`${b.obj_id}: env missing from paper.tex`);
    else if (got !== norm(b.body)) problems.push(`${b.obj_id}: body differs from formal_layer.json`);
  }
  return problems;
}

/**
 * Build the source block list from the graph + the rendered bodies/titles (P1). One block per
 * rendered (frozen, env-kind) node; `obj_id` is the node id, with `lean`/`status`/`provenance`/
 * `ref_set` read straight from the graph so the join is explicit rather than re-derived later.
 */
export function blocksFromGraph(
  g: FormalizationGraph,
  bodies: Map<string, string>,
  titles: Map<string, string>,
  /** Outline `env_overrides:` — re-kind an object's env (e.g. a constructive "assumption" that is
   *  really a definition, or a non-result framing object → `remarkv`). Applied OVER `envForNode`. */
  envOverrides?: Record<string, OverrideEnv>,
  /** Sink for a rejected override (e.g. a `remarkv` demotion of a proof-critical object). */
  log: (msg: string) => void = () => {},
  citedPresentation: {
    citeKeyByNodeId?: Map<string, string>;
    locatorByNodeId?: Map<string, string>;
  } = {},
): FormalBlock[] {
  // A node is load-bearing iff some PROVED node (theorem/lemma) depends on it — such a node may
  // never be demoted to `remarkv` (that would hide a proof input as an interpretive aside).
  const provedDeps = new Set<string>();
  for (const m of g.nodes) {
    if (!isUndeliveredNode(m) && (m.kind === "theorem" || m.kind === "lemma")) {
      for (const t of refTargets(g, m.id)) provedDeps.add(t.id);
    }
  }
  const envForId = (n: { id: string }): ReturnType<typeof envForNode> => {
    const ov = envOverrides?.[n.id];
    if (!ov) return envForNode(n as Parameters<typeof envForNode>[0]);
    if (ov === "remarkv" && provedDeps.has(n.id)) {
      log(`env_override ${n.id}=remarkv ignored — a proved result depends on it (load-bearing)`);
      return envForNode(n as Parameters<typeof envForNode>[0]);
    }
    return ov;
  };
  // Order by the `bodies` map (P1 passes it in the rendered/topological order); any rendered node
  // without a supplied body is appended in graph order. Order is cosmetic for the reference view
  // (P2 places envs per the outline's per-section `objs:` lists), but preserving it keeps the
  // derived `.tex` view stable against the legacy assemble.
  const pos = new Map([...bodies.keys()].map((id, i) => [id, i] as const));
  const ordered = [...renderedNodes(g)].sort(
    (a, b) => (pos.get(a.id) ?? Number.MAX_SAFE_INTEGER) - (pos.get(b.id) ?? Number.MAX_SAFE_INTEGER),
  );
  return ordered.map((n) => {
    const body = bodies.get(n.id) ?? "";
    return FormalBlock.parse({
      obj_id: n.id,
      alias: n.obj_id ?? null,
      kind: n.kind,
      env: envForId(n),
      title: titles.get(n.id) ?? null,
      body,
      ref_set: refTargets(g, n.id).map((t) => t.id),
      lean: isUndeliveredNode(n) ? null : n.lean.decl_name ? { decl: n.lean.decl_name, file: n.lean.file ?? "Basic.lean" } : null,
      status: isUndeliveredNode(n) ? "undelivered" : n.review.status,
      provenance: n.provenance,
      cited_dependencies: citedDependencies(g, n.id).map((d) => ({
        node_id: d.id,
        cite_id: d.gate?.source ?? d.id,
        cite_key: citedPresentation.citeKeyByNodeId?.get(d.id) ?? null,
        locator: citedPresentation.locatorByNodeId?.get(d.id) ?? null,
        statement: d.nl.statement,
        status: d.review.status,
      })),
      body_hash: hashBody(body),
    });
  });
}
