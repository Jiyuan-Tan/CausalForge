import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph, graphPath, loadGraph, saveGraph } from "../../src/graph/store.js";

let dir: string;
beforeEach(async () => {
  dir = await mkdtemp(path.join(tmpdir(), "graph-store-"));
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("store", () => {
  it("createEmptyGraph yields an empty, valid graph", () => {
    const g = createEmptyGraph("stat_demo", "v1");
    expect(g.qid).toBe("stat_demo");
    expect(g.nodes).toEqual([]);
    expect(g.edges).toEqual([]);
  });

  it("save then load round-trips", async () => {
    const g = createEmptyGraph("stat_demo", "v1");
    g.nodes.push({
      id: "t1",
      kind: "theorem",
      provenance: "from-note",
      nl: { statement: "x", tex_anchor: "tex:L1", frozen: true },
      lean: { decl_name: null, file: null },
      review: { status: "unreviewed", passed_hash: null },
      proof: { state: "sorry", sorry_count: 1 },
    });
    const p = graphPath(dir, "stat_demo", "v1");
    await saveGraph(p, g);
    const back = await loadGraph(p);
    expect(back).toEqual(g);
  });

  it("loadGraph throws on a schema-invalid file", async () => {
    const p = graphPath(dir, "stat_demo", "v1");
    await saveGraph(p, createEmptyGraph("stat_demo", "v1"));
    await readFile(p, "utf8"); // file exists
    await rm(p);
    const { writeFile } = await import("node:fs/promises");
    await writeFile(p, JSON.stringify({ qid: "x" }), "utf8");
    await expect(loadGraph(p)).rejects.toThrow();
  });
});
