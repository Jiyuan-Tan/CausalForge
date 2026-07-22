/**
 * Read-side query layer over the typed study graph (spec §8.3) plus the
 * deterministic index builder consumed by `tools/bin/build_index.ts`,
 * `tools/bin/reconcile_bank.ts`, and (Phase 2) `study/stage*.ts`.
 *
 * Writers are responsible for acquiring `shared/graph_lock.ts#withGraphWriteLock`
 * around their critical section. Readers do not lock; they tolerate seeing
 * either the pre-swap or post-swap `index.json` via the atomic rename in
 * `writeIndexAtomic`.
 */

import { readdirSync, readFileSync } from "node:fs";
import { readdir, readFile, rename, writeFile } from "node:fs/promises";
import path from "node:path";
import {
  OUTBOUND_EDGES,
  SCHEMA_VERSION,
  nodeIdOf,
  nodeTypeOf,
  type Assumption,
  type BankedTheorem,
  type EdgeKind,
  type Insight,
  type Method,
  type Note,
  type NodeTypeName,
  type OpenQuestion,
  type OpenQuestionStatus,
  type Paper,
  type StudyNode,
} from "./kb_types.js";

export const INDEX_SCHEMA_VERSION = 1 as const;

export interface GraphIndex {
  schema_version: 1;
  generated_at: string;
  counts: Record<NodeTypeName, number>;
  byName: {
    method: Record<string, string>;
    assumption: Record<string, string>;
  };
  forward: Record<string, Partial<Record<EdgeKind, string[]>>>;
  reverse: Record<string, Partial<Record<EdgeKind, string[]>>>;
}

const NODE_TYPE_DIRS: NodeTypeName[] = [
  "paper",
  "insight",
  "method",
  "assumption",
  "note",
  "open_question",
  "study_target",
  "banked_theorem",
  "theorem",
  "next_study_recommendation",
];

// ---------------------------------------------------------------------------
// Loading
// ---------------------------------------------------------------------------

/**
 * Walks every `nodes/<type>/*.json` under `studyDir`, JSON-parses, validates
 * the current `SCHEMA_VERSION`, and returns a flat list. Skips non-JSON / hidden files.
 * Throws on any node missing its id field — corrupt graphs fail loud.
 */
export async function loadAllNodes(studyDir: string): Promise<StudyNode[]> {
  const out: StudyNode[] = [];
  for (const type of NODE_TYPE_DIRS) {
    const dir = path.join(studyDir, "nodes", type);
    let entries: string[];
    try {
      entries = await readdir(dir);
    } catch (err: unknown) {
      // Missing per-type dir is fine in fresh/partial bootstraps.
      if ((err as { code?: string })?.code === "ENOENT") continue;
      throw err;
    }
    for (const name of entries) {
      if (!name.endsWith(".json") || name.startsWith(".")) continue;
      const full = path.join(dir, name);
      const raw = await readFile(full, "utf8");
      const parsed = JSON.parse(raw) as StudyNode;
      if ((parsed as { schema_version?: number }).schema_version !== SCHEMA_VERSION) {
        throw new Error(
          `loadAllNodes: ${full} has unexpected schema_version=${(parsed as { schema_version?: number }).schema_version} (expected ${SCHEMA_VERSION})`,
        );
      }
      // nodeIdOf throws if no id field — that's the intended fail-loud path.
      nodeIdOf(parsed);
      out.push(parsed);
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Index builder (pure)
// ---------------------------------------------------------------------------

export function buildIndex(
  nodes: StudyNode[],
  opts?: { generatedAt?: string },
): GraphIndex {
  const sorted = [...nodes].sort((a, b) => nodeIdOf(a).localeCompare(nodeIdOf(b)));
  const counts: Record<NodeTypeName, number> = {
    paper: 0,
    insight: 0,
    method: 0,
    assumption: 0,
    note: 0,
    open_question: 0,
    study_target: 0,
    banked_theorem: 0,
    theorem: 0,
    next_study_recommendation: 0,
  };
  const byName: GraphIndex["byName"] = { method: {}, assumption: {} };
  const forward: GraphIndex["forward"] = {};
  const reverse: GraphIndex["reverse"] = {};

  for (const node of sorted) {
    const type = nodeTypeOf(node);
    const id = nodeIdOf(node);
    counts[type] += 1;
    if (type === "method") {
      const m = node as Method;
      if (m.name) byName.method[m.name] = id;
    } else if (type === "assumption") {
      const a = node as Assumption;
      if (a.name) byName.assumption[a.name] = id;
    }
    const accessors = OUTBOUND_EDGES[type];
    for (const acc of accessors) {
      const list = (node as unknown as Record<string, unknown>)[acc.field];
      if (!Array.isArray(list)) continue;
      // Stage 5b item 1 — accept either plain string ids OR
      // {paper_id, used_for, rationale} annotated cite entries (Paper.cites).
      // The edge index keys on the target id only; annotations live on the
      // source node and are surfaced separately by consumers.
      const targets: string[] = [];
      for (const x of list) {
        if (typeof x === "string") targets.push(x);
        else if (x && typeof x === "object") {
          const bag = x as Record<string, unknown>;
          if (typeof bag.paper_id === "string") targets.push(bag.paper_id);
        }
      }
      if (targets.length === 0) continue;
      const slot = (forward[id] ??= {});
      const existing = slot[acc.kind] ?? [];
      slot[acc.kind] = [...existing, ...targets];
      for (const target of targets) {
        const rslot = (reverse[target] ??= {});
        const rlist = rslot[acc.kind] ?? [];
        rslot[acc.kind] = [...rlist, id];
      }
    }
  }

  // Deterministic sorting of every edge list.
  for (const map of [forward, reverse]) {
    for (const id of Object.keys(map)) {
      const slot = map[id];
      for (const kind of Object.keys(slot) as EdgeKind[]) {
        slot[kind] = [...(slot[kind] ?? [])].sort();
      }
    }
  }

  return {
    schema_version: INDEX_SCHEMA_VERSION,
    generated_at: opts?.generatedAt ?? new Date().toISOString(),
    counts,
    byName,
    forward,
    reverse,
  };
}

// ---------------------------------------------------------------------------
// Persistence
// ---------------------------------------------------------------------------

/**
 * Stable, sorted-key JSON serializer. Ensures byte-determinism across runs
 * given the same input (modulo the `generated_at` field, which callers set).
 */
export function serializeIndex(index: GraphIndex): string {
  return JSON.stringify(index, sortedKeysReplacer(index), 2) + "\n";
}

function sortedKeysReplacer(_root: unknown) {
  // JSON.stringify visits objects in declaration order; to force sorted output
  // we rebuild every object with sorted keys before serialization.
  return function replacer(_key: string, value: unknown): unknown {
    if (value && typeof value === "object" && !Array.isArray(value)) {
      const obj = value as Record<string, unknown>;
      const out: Record<string, unknown> = {};
      for (const k of Object.keys(obj).sort()) out[k] = obj[k];
      return out;
    }
    return value;
  };
}

export async function writeIndexAtomic(studyDir: string, index: GraphIndex): Promise<void> {
  const finalPath = path.join(studyDir, "index.json");
  const tmpPath = `${finalPath}.new`;
  await writeFile(tmpPath, serializeIndex(index), "utf8");
  await rename(tmpPath, finalPath);
}

export async function loadIndex(studyDir: string): Promise<GraphIndex | null> {
  const full = path.join(studyDir, "index.json");
  let raw: string;
  try {
    raw = await readFile(full, "utf8");
  } catch (err: unknown) {
    if ((err as { code?: string })?.code === "ENOENT") return null;
    throw err;
  }
  const parsed = JSON.parse(raw) as GraphIndex;
  if (parsed.schema_version !== INDEX_SCHEMA_VERSION) {
    throw new Error(
      `loadIndex: ${full} has unexpected schema_version=${parsed.schema_version} (expected ${INDEX_SCHEMA_VERSION}); run migrate_graph.ts`,
    );
  }
  return parsed;
}

// ---------------------------------------------------------------------------
// Graph object + queries (spec §8.3)
// ---------------------------------------------------------------------------

export interface Graph {
  nodes: Map<string, StudyNode>;
  index: GraphIndex;
  studyDir: string;
}

const DEFAULT_LIMIT = 20;

export async function loadGraph(studyDir: string): Promise<Graph> {
  const nodes = await loadAllNodes(studyDir);
  const nodeMap = new Map<string, StudyNode>();
  for (const n of nodes) nodeMap.set(nodeIdOf(n), n);
  let index = await loadIndex(studyDir);
  const totalNodes = nodes.length;
  const indexTotal = index ? Object.values(index.counts).reduce((a, b) => a + b, 0) : -1;
  if (!index || indexTotal !== totalNodes) {
    // Readers tolerate a stale index by rebuilding in-memory; they never write.
    index = buildIndex(nodes);
  }
  // Pad missing count keys (e.g. older on-disk indexes built before a node
  // type was introduced) so consumers see the full Record<NodeTypeName, number>.
  for (const t of NODE_TYPE_DIRS) {
    if (index.counts[t] === undefined) (index.counts as Record<string, number>)[t] = 0;
  }
  return { nodes: nodeMap, index, studyDir };
}

function nodesByType<T extends StudyNode>(graph: Graph, type: NodeTypeName): T[] {
  const out: T[] = [];
  for (const node of graph.nodes.values()) {
    if (nodeTypeOf(node) === type) out.push(node as T);
  }
  return out.sort((a, b) => nodeIdOf(a).localeCompare(nodeIdOf(b))) as T[];
}

function neighbourIdsOfKind(graph: Graph, id: string, kind: EdgeKind, direction: "forward" | "reverse"): string[] {
  const slot = graph.index[direction][id];
  if (!slot) return [];
  return slot[kind] ?? [];
}

export function insightsForMethod(
  graph: Graph,
  method_id: string,
  limit: number = DEFAULT_LIMIT,
): Insight[] {
  // Insights instantiate Methods (Insight.instantiates -> Method). So insights
  // pointing AT a method live in reverse[method_id].instantiates, then we
  // filter to actual Insight nodes (BankedTheorems also use 'instantiates').
  const candidates = neighbourIdsOfKind(graph, method_id, "instantiates", "reverse");
  const out: Insight[] = [];
  for (const id of candidates) {
    const node = graph.nodes.get(id);
    if (!node) continue;
    if (nodeTypeOf(node) === "insight") out.push(node as Insight);
    if (out.length >= limit) break;
  }
  return out;
}

export function notesForMethod(
  graph: Graph,
  method_id: string,
  limit: number = DEFAULT_LIMIT,
): Note[] {
  const candidates = neighbourIdsOfKind(graph, method_id, "discusses", "reverse");
  const out: Note[] = [];
  for (const id of candidates) {
    const node = graph.nodes.get(id);
    if (!node) continue;
    if (nodeTypeOf(node) === "note") out.push(node as Note);
    if (out.length >= limit) break;
  }
  return out;
}

export function bankedTheoremsForMethod(
  graph: Graph,
  method_id: string,
  limit: number = DEFAULT_LIMIT,
): BankedTheorem[] {
  const candidates = neighbourIdsOfKind(graph, method_id, "instantiates", "reverse");
  const out: BankedTheorem[] = [];
  for (const id of candidates) {
    const node = graph.nodes.get(id);
    if (!node) continue;
    if (nodeTypeOf(node) === "banked_theorem") out.push(node as BankedTheorem);
    if (out.length >= limit) break;
  }
  return out;
}

export function openQuestionsForMethod(
  graph: Graph,
  method_id: string,
  status?: "open" | "in_progress" | "closed" | "abandoned",
  limit: number = DEFAULT_LIMIT,
): OpenQuestion[] {
  const out: OpenQuestion[] = [];
  for (const q of nodesByType<OpenQuestion>(graph, "open_question")) {
    if (q.seed_method_id !== method_id) continue;
    if (status !== undefined) {
      const matchedStatus = matchOpenQuestionStatus(q.status, status);
      if (!matchedStatus) continue;
    }
    out.push(q);
    if (out.length >= limit) break;
  }
  return out;
}

function matchOpenQuestionStatus(
  actual: OpenQuestionStatus,
  filter: "open" | "in_progress" | "closed" | "abandoned",
): boolean {
  if (filter === "closed") {
    return typeof actual === "object" && actual !== null && "closed_by" in actual;
  }
  return actual === filter;
}

export function findMethodByName(graph: Graph, name: string): Method | null {
  return findByName(graph, "method", name) as Method | null;
}

export function findAssumptionByName(graph: Graph, name: string): Assumption | null {
  return findByName(graph, "assumption", name) as Assumption | null;
}

/**
 * Two-stage name lookup:
 *  1. Exact match against `byName.<type>`.
 *  2. Fuzzy: case-insensitive substring + Jaro-Winkler ≥ 0.92.
 * Phase 1 does NOT call the LLM tie-break that spec §8.3 mentions — that
 * lives in Phase 2's S0.5 stage. We ship the fuzzy backstop only.
 */
function findByName(graph: Graph, type: "method" | "assumption", name: string): StudyNode | null {
  const idx = graph.index.byName[type];
  const direct = idx[name];
  if (direct) {
    const node = graph.nodes.get(direct);
    if (node) return node;
  }
  const needle = name.trim().toLowerCase();
  let best: { id: string; score: number } | null = null;
  for (const [candName, id] of Object.entries(idx)) {
    const cand = candName.toLowerCase();
    let score = jaroWinkler(cand, needle);
    if (cand.includes(needle) || needle.includes(cand)) {
      score = Math.max(score, 0.93);
    }
    if (!best || score > best.score) best = { id, score };
  }
  if (best && best.score >= 0.92) {
    const node = graph.nodes.get(best.id);
    if (node) return node;
  }
  return null;
}

function jaroWinkler(a: string, b: string): number {
  if (a === b) return 1;
  if (a.length === 0 || b.length === 0) return 0;
  const matchWindow = Math.max(0, Math.floor(Math.max(a.length, b.length) / 2) - 1);
  const aMatches = new Array(a.length).fill(false);
  const bMatches = new Array(b.length).fill(false);
  let matches = 0;
  for (let i = 0; i < a.length; i++) {
    const lo = Math.max(0, i - matchWindow);
    const hi = Math.min(b.length - 1, i + matchWindow);
    for (let j = lo; j <= hi; j++) {
      if (bMatches[j] || a[i] !== b[j]) continue;
      aMatches[i] = true;
      bMatches[j] = true;
      matches += 1;
      break;
    }
  }
  if (matches === 0) return 0;
  let transpositions = 0;
  let k = 0;
  for (let i = 0; i < a.length; i++) {
    if (!aMatches[i]) continue;
    while (!bMatches[k]) k += 1;
    if (a[i] !== b[k]) transpositions += 1;
    k += 1;
  }
  transpositions /= 2;
  const jaro =
    (matches / a.length + matches / b.length + (matches - transpositions) / matches) / 3;
  // Winkler prefix bonus (up to 4 chars, scaling factor 0.1).
  let prefix = 0;
  for (let i = 0; i < Math.min(4, a.length, b.length); i++) {
    if (a[i] === b[i]) prefix += 1;
    else break;
  }
  return jaro + prefix * 0.1 * (1 - jaro);
}

export interface SubgraphEdge {
  from: string;
  kind: EdgeKind;
  to: string;
}

export interface Subgraph {
  nodes: StudyNode[];
  edges: SubgraphEdge[];
  truncated?: boolean;
}

export function neighborhood(
  graph: Graph,
  node_id: string,
  opts: { radius?: number; limit?: number } = {},
): Subgraph {
  const radius = opts.radius ?? 1;
  const limit = opts.limit ?? DEFAULT_LIMIT;
  const visited = new Set<string>();
  const edges: SubgraphEdge[] = [];
  if (!graph.nodes.has(node_id)) return { nodes: [], edges: [] };
  const frontier: Array<{ id: string; depth: number }> = [{ id: node_id, depth: 0 }];
  visited.add(node_id);
  let truncated = false;
  while (frontier.length > 0) {
    const { id, depth } = frontier.shift()!;
    if (depth >= radius) continue;
    const fwd = graph.index.forward[id] ?? {};
    const rev = graph.index.reverse[id] ?? {};
    const addNeighbours = (
      bucket: Partial<Record<EdgeKind, string[]>>,
      direction: "fwd" | "rev",
    ) => {
      for (const kind of Object.keys(bucket).sort() as EdgeKind[]) {
        for (const target of (bucket[kind] ?? []).slice().sort()) {
          if (direction === "fwd") edges.push({ from: id, kind, to: target });
          else edges.push({ from: target, kind, to: id });
          if (!visited.has(target)) {
            if (visited.size >= limit) {
              truncated = true;
              continue;
            }
            visited.add(target);
            frontier.push({ id: target, depth: depth + 1 });
          }
        }
      }
    };
    addNeighbours(fwd, "fwd");
    addNeighbours(rev, "rev");
  }
  const nodes: StudyNode[] = [];
  for (const id of Array.from(visited).sort()) {
    const node = graph.nodes.get(id);
    if (node) nodes.push(node);
  }
  const dedupedEdges = dedupeEdges(edges);
  return truncated ? { nodes, edges: dedupedEdges, truncated: true } : { nodes, edges: dedupedEdges };
}

function dedupeEdges(edges: SubgraphEdge[]): SubgraphEdge[] {
  const seen = new Set<string>();
  const out: SubgraphEdge[] = [];
  for (const e of edges.sort((a, b) =>
    `${a.from}|${a.kind}|${a.to}`.localeCompare(`${b.from}|${b.kind}|${b.to}`),
  )) {
    const key = `${e.from}|${e.kind}|${e.to}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(e);
  }
  return out;
}

export interface DangleReport {
  methods_without_banked: Method[];
  assumptions_never_relaxed: Assumption[];
}

export function dangle(graph: Graph): DangleReport {
  const methods_without_banked: Method[] = [];
  for (const m of nodesByType<Method>(graph, "method")) {
    const inst = graph.index.reverse[m.method_id]?.instantiates ?? [];
    let hasBt = false;
    for (const id of inst) {
      const node = graph.nodes.get(id);
      if (node && nodeTypeOf(node) === "banked_theorem") {
        hasBt = true;
        break;
      }
    }
    if (!hasBt) methods_without_banked.push(m);
  }
  const assumptions_never_relaxed: Assumption[] = [];
  for (const a of nodesByType<Assumption>(graph, "assumption")) {
    const rel = graph.index.reverse[a.assumption_id]?.relaxes ?? [];
    if (rel.length === 0) assumptions_never_relaxed.push(a);
  }
  return { methods_without_banked, assumptions_never_relaxed };
}

/** Minimal stand-ins for Phase 2 textbook/lecture-note registry (R8). */
export interface BookMeta {
  book_id: string;
  title: string;
}
export interface NoteMeta {
  note_meta_id: string;
  title: string;
}

export interface RegisteredSources {
  papers: Paper[];
  textbooks: BookMeta[];
  lecture_notes: NoteMeta[];
}

function loadRegistryMeta<T extends { title: string }>(
  root: string,
  dirName: "textbooks" | "lecture_notes",
  idField: "book_id" | "note_meta_id",
): T[] {
  const dir = path.join(root, dirName);
  try {
    return readdirSync(dir, { withFileTypes: true })
      .filter((entry) => entry.isDirectory())
      .flatMap((entry) => {
        const full = path.join(dir, entry.name, "meta.json");
        try {
          const parsed = JSON.parse(readFileSync(full, "utf8")) as Record<string, unknown>;
          if (typeof parsed.title !== "string") return [];
          const id = typeof parsed[idField] === "string" ? parsed[idField] : entry.name;
          return [{ ...parsed, [idField]: id } as T];
        } catch (err) {
          if ((err as NodeJS.ErrnoException).code === "ENOENT") return [];
          throw err;
        }
      });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") return [];
    throw err;
  }
}

/**
 * Returns registered source materials from graph papers plus book registries.
 */
export function registeredSources(graph: Graph): RegisteredSources {
  return {
    papers: nodesByType<Paper>(graph, "paper"),
    // AUDIT-SHARED: appears study-pipeline-retired?
    textbooks: loadRegistryMeta<BookMeta>(graph.studyDir, "textbooks", "book_id"),
    // AUDIT-SHARED: appears study-pipeline-retired?
    lecture_notes: loadRegistryMeta<NoteMeta>(graph.studyDir, "lecture_notes", "note_meta_id"),
  };
}

// Re-exports for convenience.
export { nodeIdOf, nodeTypeOf } from "./kb_types.js";
export type {
  StudyNode,
  StudyTarget,
  Paper,
  Insight,
  Method,
  Assumption,
  Note,
  OpenQuestion,
  BankedTheorem,
  NodeTypeName,
  EdgeKind,
} from "./kb_types.js";
