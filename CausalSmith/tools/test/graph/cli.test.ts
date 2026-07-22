import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runCli } from "../../src/graph/cli.js";
import { loadGraph, graphPath } from "../../src/graph/store.js";

let dir: string;
beforeEach(async () => {
  dir = await mkdtemp(path.join(tmpdir(), "graph-cli-"));
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

const ARGS = (...a: string[]) => ["--dir", dir, "--qid", "q", "--spec", "v1", ...a];

describe("cli", () => {
  it("init creates an empty graph file", async () => {
    const code = await runCli(ARGS("init"));
    expect(code).toBe(0);
    const g = await loadGraph(graphPath(dir, "q", "v1"));
    expect(g.nodes).toEqual([]);
  });

  it("add-node then add-assumption persist to the graph", async () => {
    await runCli(ARGS("init"));
    await runCli(ARGS("add-node", "--id", "t1", "--kind", "theorem", "--provenance", "from-note", "--nl", "main", "--anchor", "tex:L1"));
    await runCli(ARGS("add-assumption", "--node", "t1", "--id", "a1", "--statement", "overlap", "--tier", "2", "--classification", "faithful-refinement", "--anchor", "tex:L5", "--provenance", "from-note"));
    const g = await loadGraph(graphPath(dir, "q", "v1"));
    expect(g.nodes.map((n) => n.id).sort()).toEqual(["a1", "t1"]);
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "a1", source: "declared" });
  });

  it("validate returns nonzero on an invalid graph", async () => {
    await runCli(ARGS("init"));
    await runCli(ARGS("add-node", "--id", "t1", "--kind", "theorem", "--provenance", "from-note", "--nl", "m", "--anchor", ""));
    const code = await runCli(ARGS("validate", "--json"));
    expect(code).toBe(1);
  });

  // An orchestrator ACCEPT-AS-IS adjudication recorded only in the decision log left
  // graph.json at `review.status: drift`, so the node re-entered the dirty frontier on
  // every later resume and drew a fresh reviewer dispatch each time. The verb persists
  // the verdict at the node's current statement hash.
  it("accept-review persists matched status and clears the node from the dirty frontier", async () => {
    const { mkdir, writeFile } = await import("node:fs/promises");
    const { dirtyFrontier } = await import("../../src/graph/diff.js");
    const { extractFromLean } = await import("../../src/graph/extractor.js");
    await runCli(ARGS("init"));
    await runCli(ARGS("add-node", "--id", "thm:t1", "--kind", "theorem", "--provenance", "from-note", "--nl", "main claim", "--anchor", "tex:L1"));
    const leanDir = path.join(dir, "lean");
    await mkdir(leanDir, { recursive: true });
    await writeFile(path.join(leanDir, "Basic.lean"), "-- @node: thm:t1\ntheorem t1 : True := by trivial\n", "utf8");

    const code = await runCli(ARGS("accept-review", "--id", "thm:t1", "--lean-dir", leanDir, "--note", "reviewer over-strict"));
    expect(code).toBe(0);

    const g = await loadGraph(graphPath(dir, "q", "v1"));
    const node = g.nodes.find((n) => n.id === "thm:t1")!;
    expect(node.review.status).toBe("matched");
    expect(node.review.note).toBe("reviewer over-strict");
    const { hashes } = await extractFromLean(g, leanDir);
    expect(node.review.passed_hash).toBe(hashes["thm:t1"]);
    expect(dirtyFrontier(g, hashes)).not.toContain("thm:t1");
  });

  it("accept-review fails loud on an unknown node id", async () => {
    await runCli(ARGS("init"));
    const code = await runCli(ARGS("accept-review", "--id", "thm:absent", "--lean-dir", dir));
    expect(code).toBe(70);
  });
});
