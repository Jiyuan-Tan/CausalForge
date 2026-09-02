import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { randomUUID } from "node:crypto";
import path from "node:path";
import { GraphSchema, type FormalizationGraph } from "./types.js";

/**
 * Per-question graph artifact path, parallel to the state JSON naming. New runs
 * write the bare `graph.json`; pre-rename runs and un-migrated banked entries
 * carry the legacy `<qid>_<spec>_graph.json`, which is returned when it (and not
 * the bare name) exists.
 */
export function graphPath(formalizationDir: string, qid: string, specialization: string): string {
  const bare = path.join(formalizationDir, "graph.json");
  if (existsSync(bare)) return bare;
  const legacy = path.join(formalizationDir, `${qid}_${specialization}_graph.json`);
  if (existsSync(legacy)) return legacy;
  return bare;
}

export function createEmptyGraph(qid: string, specialization: string): FormalizationGraph {
  return { qid, specialization, nodes: [], edges: [] };
}

export async function loadGraph(p: string): Promise<FormalizationGraph> {
  const raw = await readFile(p, "utf8");
  const parsed: unknown = JSON.parse(raw);
  // The schema coerces the retired legacy status `derived` to `drift` (it was a FAIL that several
  // consumers read as a pass). Say so: the next save of this graph persists the coerced value, and
  // a tracked bank file changing status with no explanation is a surprise in `git diff`.
  // Any malformed shape falls through to GraphSchema.parse, whose error names the bad path — this
  // scan must never pre-empt that diagnostic with a TypeError.
  const nodes: { id?: string; review?: { status?: string } }[] =
    Array.isArray((parsed as { nodes?: unknown })?.nodes) ? (parsed as { nodes: [] }).nodes : [];
  const legacy = nodes.filter((n) => n?.review?.status === "derived").map((n) => n?.id ?? "?");
  if (legacy.length > 0) {
    console.warn(
      `[graph] ${p}: ${legacy.length} node(s) carry the retired status 'derived' → loaded as 'drift' ` +
        `(a faithfulness FAIL, never a pass); a later save will persist that: ${legacy.join(", ")}`,
    );
  }
  return GraphSchema.parse(parsed);
}

/** Atomic write: validate, write to a temp sibling, rename into place. */
export async function saveGraph(p: string, graph: FormalizationGraph): Promise<void> {
  const checked = GraphSchema.parse(graph);
  await mkdir(path.dirname(p), { recursive: true });
  const tmp = `${p}.${process.pid}.${randomUUID()}.tmp`; // why: parallel saves must not race one fixed tmp path.
  await writeFile(tmp, JSON.stringify(checked, null, 2) + "\n", "utf8");
  await rename(tmp, p);
}
