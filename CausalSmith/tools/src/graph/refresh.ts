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
import type { FormalizationGraph, GraphNode, ReviewStatus, ValidationResult } from "./types.js";
import type { CrosswalkEntry, CrosswalkVerdict } from "../types.js";

export interface GateGraphRefresh {
  graph: FormalizationGraph | null;
  skeleton: GraphSkeletonRow[];
  dirty: string[];
  hashes: Record<string, string>;
  coverage: ValidationResult | null;
  error?: string;
  /** Inert invented `@node:` tags stripped by the self-heal below. Non-empty means the
   *  scaffolder emitted a tag naming no real node; surfaced so the heal is never silent. */
  strippedTags?: { id: string; file: string }[];
}

/**
 * Remove `-- @node: <id>` comment lines for the given ids from every `.lean` file under
 * `leanDir`. Comment-only, so it cannot change what any declaration means. Used to clear
 * inert invented tags that would otherwise dead-lock every future graph refresh.
 */
async function stripNodeTags(leanDir: string, ids: string[]): Promise<{ id: string; file: string }[]> {
  const { readdir, readFile, writeFile } = await import("node:fs/promises");
  const path = await import("node:path");
  const wanted = new Set(ids);
  const removed: { id: string; file: string }[] = [];
  const walk = async (dir: string): Promise<string[]> => {
    const out: string[] = [];
    for (const e of await readdir(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) out.push(...(await walk(p)));
      else if (e.name.endsWith(".lean")) out.push(p);
    }
    return out;
  };
  for (const file of await walk(leanDir)) {
    const src = await readFile(file, "utf8");
    const kept = src.split("\n").filter((line) => {
      const m = /^\s*--\s*@node:\s*(\S+)\s*$/.exec(line);
      if (!m || !wanted.has(m[1])) return true;
      removed.push({ id: m[1], file: path.relative(leanDir, file) });
      return false;
    });
    if (kept.length !== src.split("\n").length) await writeFile(file, kept.join("\n"), "utf8");
  }
  return removed;
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
 * Resolve a reviewer target without changing an exact graph id. Legacy note aliases
 * (`T-1` → `t1`) remain available for legacy graph ids, while stamped `obj_id`
 * aliases are accepted only for from-note nodes. AUX aliases remain available for
 * the agent-introduced hidden-definition surface.
 * Anything else is a persistence error, not a verdict that may be silently ignored.
 */
function resolveVerdictNode(graph: FormalizationGraph, objId: string): GraphNode {
  const exact = graph.nodes.filter((n) => n.id === objId);
  if (exact.length === 1) return exact[0];

  const legacyId = objIdToNode(objId);
  const candidates = graph.nodes.filter((n) =>
    n.id === legacyId
    || (n.provenance === "from-note" && n.obj_id === objId),
  );
  if (candidates.length === 1) return candidates[0];

  const detail = candidates.length === 0
    ? "no graph node or unambiguous legacy/from-note alias"
    : `ambiguous aliases: ${candidates.map((n) => n.id).sort().join(", ")}`;
  throw new Error(`review verdict target resolution failed for ${JSON.stringify(objId)}: ${detail}`);
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
  /** Reviewer-facing target → exact graph node id. `null` marks a synthetic symbol-cluster
   *  row, which is persisted separately in `symbolReview` by proof_reviewer. */
  targetOwners?: ReadonlyMap<string, string | null>,
): FormalizationGraph {
  // Resolve the ENTIRE batch before changing a review. A later bad row must not leave an
  // earlier row applied if callers catch the deterministic resolution error.
  const resolved: { entry: CrosswalkEntry; node: GraphNode; status: ReviewStatus }[] = [];
  for (const e of crosswalk) {
    let status = verdictToStatus(e.verdict);
    if (status === "matched" && derivedObjIds.has(e.obj_id)) status = "derived";
    if (!status) continue;
    let node: GraphNode;
    if (targetOwners?.has(e.obj_id)) {
      const owner = targetOwners.get(e.obj_id)!;
      if (owner === null) continue;
      const bound = graph.nodes.find((n) => n.id === owner);
      if (!bound) {
        throw new Error(`review verdict target resolution failed for ${JSON.stringify(e.obj_id)}: bound graph node ${JSON.stringify(owner)} is missing`);
      }
      node = bound;
    } else {
      node = resolveVerdictNode(graph, e.obj_id);
    }
    resolved.push({ entry: e, node, status });
  }

  let g = graph;
  for (const { entry: e, node, status } of resolved) {
    const id = node.id;
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
    let strippedTags: { id: string; file: string }[] = [];
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
    // Ids the graph already knew BEFORE minting. An unlinked tag naming one of these is a
    // REAL ambiguity (two decls claiming one node, or a mis-anchor) and stays fatal below.
    const preMintIds = new Set(g.nodes.map((n) => n.id));
    g = await mintHiddenDefNodes(ext0.graph, a.leanDir);
    // Register agent-introduced `@node:`-tagged helper lemmas the filler added, then
    // re-extract so the freshly-minted nodes get linked (decl_name/file) and hashed.
    g = await mintAnnotatedNodes(g, a.leanDir);
    let ext = await extractFromLean(g, a.leanDir);
    // SELF-HEAL (bounded, once): a scaffolder that invents a tag value and repeats it on
    // several helper lemmas creates a tag naming no real node. `mintAnnotatedNodes` mints it
    // against the FIRST decl and skips the rest, so extraction then reports a duplicate on
    // every subsequent refresh — permanently. Because the patch pass dies here BEFORE the
    // reviewer's redirect is applied, the reviewer re-flags the same targets next round and the
    // loop burns its whole scaffold budget without ever converging: a cosmetic defect turned
    // into a hard deadlock. Such a tag is INERT — it names no plan node, so it cannot mis-anchor
    // one or make coverage depend on source order (the hazard the duplicate check exists for).
    // Strip those comment lines, drop the phantom node minted from them, and re-extract once.
    // Tags naming a pre-existing node are untouched and still fail closed.
    if (ext.unlinked.length > 0 && ext.unlinked.every((u) => !preMintIds.has(u.id))) {
      const inertIds = [...new Set(ext.unlinked.map((u) => u.id))];
      strippedTags = await stripNodeTags(a.leanDir, inertIds);
      if (strippedTags.length > 0) {
        g = { ...g, nodes: g.nodes.filter((n) => !(inertIds.includes(n.id) && !preMintIds.has(n.id))) };
        ext = await extractFromLean(g, a.leanDir);
      }
    }
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
      ...(strippedTags.length ? { strippedTags } : {}),
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
