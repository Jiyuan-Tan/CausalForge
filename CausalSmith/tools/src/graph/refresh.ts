import { existsSync } from "node:fs";
import { buildGraphFromMd, objIdToNodeId } from "./from_note.js";
import { extractFromLean } from "./extractor.js";
import { mintHiddenDefNodes, mintAnnotatedNodes } from "./hidden.js";
import { graphDerivedSkeleton, type GraphSkeletonRow } from "./skeleton.js";
import { dirtyFrontier } from "./diff.js";
import { validate } from "./validator.js";
import { setNodeReview } from "./mutate.js";
import { statementHash } from "./hash.js";
import { graphPath, loadGraph, saveGraph } from "./store.js";
import type { FormalizationGraph, ReviewStatus, ValidationResult } from "./types.js";
import type { CrosswalkEntry, CrosswalkVerdict } from "../types.js";

export interface GateGraphRefresh {
  graph: FormalizationGraph | null;
  skeleton: GraphSkeletonRow[];
  dirty: string[];
  hashes: Record<string, string>;
  coverage: ValidationResult | null;
  error?: string;
}

/** Map a reviewer crosswalk verdict onto the node review vocabulary. `unmatched`
 *  is the skeleton placeholder (not yet a real verdict) → leave node unreviewed. */
function verdictToStatus(v: CrosswalkVerdict): ReviewStatus | null {
  if (v === "exact" || v === "equivalent") return "matched";
  if (v === "unmatched") return null;
  return "drift"; // stronger/weaker/missing/extra/encoding-drift/drift
}

/** crosswalk obj_id → graph node id (AUX-<decl> hidden-defs → aux_<decl>). */
function objIdToNode(objId: string): string {
  return objId.startsWith("AUX-") ? `aux_${objId.slice(4)}` : objIdToNodeId(objId);
}

/**
 * Write a gate's reviewer crosswalk verdicts back onto the graph's node review
 * state (status + the statement hash it was reviewed at). `derivedObjIds` (F4's
 * PRIMITIVE-vs-DERIVED audit) override a `matched` to `derived`. Pure; caller persists.
 */
export function applyVerdictsToGraph(
  graph: FormalizationGraph,
  crosswalk: CrosswalkEntry[],
  hashes: Record<string, string>,
  derivedObjIds: Set<string> = new Set(),
): FormalizationGraph {
  let g = graph;
  for (const e of crosswalk) {
    let status = verdictToStatus(e.verdict);
    if (status === "matched" && derivedObjIds.has(e.obj_id)) status = "derived";
    if (!status) continue;
    const id = objIdToNode(e.obj_id);
    const node = g.nodes.find((n) => n.id === id);
    if (!node) continue;
    // Record the hash the node was reviewed at. Prefer the Lean-extracted statement hash;
    // for a hypothesis-backed node with no standalone decl, fall back to the hash of its NL
    // statement (the symmetric convention `dirtyFrontier` reads) — never a constant sentinel,
    // which would defeat staleness detection (the node would be trusted forever).
    const hash = hashes[id] ?? statementHash(node.nl.statement);
    g = setNodeReview(g, id, status, hash, e.note);
  }
  return g;
}

/**
 * Refresh the formalization graph from current Lean for a gate (F2.5/F4): load the
 * persisted graph (or build it from the `.md` if absent), extract annotations +
 * edges + proof state, mint hidden-def nodes, persist, and return the edge-augmented
 * skeleton, the dirty frontier, and the coverage validation. Best-effort: an
 * absent graph returns `graph:null`; failures include `error` for diagnostics.
 */
export async function refreshGraphForGate(a: {
  formalizationDir: string;
  qid: string;
  spec: string;
  leanDir: string;
  mdPath?: string;
}): Promise<GateGraphRefresh> {
  try {
    const p = graphPath(a.formalizationDir, a.qid, a.spec);
    let g: FormalizationGraph | null = existsSync(p)
      ? await loadGraph(p)
      : a.mdPath && existsSync(a.mdPath)
        ? await buildGraphFromMd(a.qid, a.spec, a.mdPath)
        : null;
    if (!g) return { graph: null, skeleton: [], dirty: [], hashes: {}, coverage: null };
    // NOTE: do NOT hard-fail on `ext0.unlinked` here — a filler legitimately adds new
    // `-- @node:` helper tags that are "unlinked" ONLY until `mintAnnotatedNodes` registers
    // them below. Duplicate @node tags, by contrast, survive minting and are caught by the
    // post-mint `ext.unlinked` check (extractFromLean early-returns duplicates as unlinked).
    const ext0 = await extractFromLean(g, a.leanDir);
    g = await mintHiddenDefNodes(ext0.graph, a.leanDir);
    // Register agent-introduced `@node:`-tagged helper lemmas the filler added, then
    // re-extract so the freshly-minted nodes get linked (decl_name/file) and hashed.
    g = await mintAnnotatedNodes(g, a.leanDir);
    const ext = await extractFromLean(g, a.leanDir);
    if (ext.unlinked.length > 0) {
      // why: post-mint duplicate/unmatched @node tags must not persist a stale or partially linked graph.
      throw new Error(`graph refresh found unlinked Lean @node annotations: ${ext.unlinked.map((u) => `${u.id}->${u.decl_name}@${u.file}`).join(", ")}`);
    }
    g = ext.graph;
    await saveGraph(p, g);
    return {
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: dirtyFrontier(g, ext.hashes),
      hashes: ext.hashes,
      coverage: validate(g),
    };
  } catch (err) {
    return {
      graph: null,
      skeleton: [],
      dirty: [],
      hashes: {},
      coverage: null,
      // why: callers need to distinguish corrupt/invalid graph state from no graph artifact.
      error: err instanceof Error ? err.message : String(err),
    };
  }
}
