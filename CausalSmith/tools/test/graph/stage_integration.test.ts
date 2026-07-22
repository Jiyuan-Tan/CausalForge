import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { emitGraphFromStage1 } from "../../src/formalization/stage1.js";
import {
  hiddenDefinitionChangeTargets,
  linkGraphFromStage2,
  pendingSourceRewindDirtyNodeIds,
} from "../../src/formalization/stage2.js";
import type { StateJson } from "../../src/types.js";
import { createEmptyGraph, loadGraph, graphPath, saveGraph } from "../../src/graph/store.js";
import { addNode, markPassed } from "../../src/graph/mutate.js";
import type { HiddenStatementDef } from "../../src/formalization/crosswalk.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "stageint-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const MD = `### T-block: t1 — Rate theorem
**Statement.** the estimator attains the rate.
**\`.tex\` line range.** "L1-9"
`;

describe("F1 graph emission", () => {
  it("emitGraphFromStage1 writes a graph next to the .md", async () => {
    const mdPath = path.join(dir, "q_v1.md");
    await writeFile(mdPath, MD, "utf8");
    await emitGraphFromStage1({ qid: "q", spec: "v1", formalizationDir: dir, mdPath });
    const g = await loadGraph(graphPath(dir, "q", "v1"));
    expect(g.nodes.find((n) => n.id === "t1")?.kind).toBe("theorem");
  });

  it("is best-effort: a missing .md does not throw", async () => {
    await expect(
      emitGraphFromStage1({ qid: "q", spec: "v1", formalizationDir: dir, mdPath: path.join(dir, "nope.md") }),
    ).resolves.toBeUndefined();
  });
});

describe("F2 graph link + extract", () => {
  it("links annotated decls and refreshes proof state, advisory-only", async () => {
    const mdPath = path.join(dir, "q_v1.md");
    await writeFile(mdPath, MD, "utf8");
    await emitGraphFromStage1({ qid: "q", spec: "v1", formalizationDir: dir, mdPath });

    const leanDir = path.join(dir, "lean");
    await mkdir(leanDir, { recursive: true });
    // scaffold with NO annotation — seedAnnotations adds `-- @node: t1` from the t<n>_thm convention
    await writeFile(path.join(leanDir, "T1.lean"), "theorem t1_thm : True := by\n  sorry\n", "utf8");

    const result = await linkGraphFromStage2({ qid: "q", spec: "v1", formalizationDir: dir, leanDir });
    const t1 = result.graph!.nodes.find((n) => n.id === "t1")!;
    expect(t1.lean.decl_name).toBe("t1_thm");
    expect(t1.proof).toEqual({ state: "sorry", sorry_count: 1 });
    expect(Array.isArray(result.findings)).toBe(true);
  });

  it("is best-effort: a missing graph file yields {graph:null}", async () => {
    const leanDir = path.join(dir, "lean2");
    await mkdir(leanDir, { recursive: true });
    await expect(
      linkGraphFromStage2({ qid: "nope", spec: "v1", formalizationDir: dir, leanDir }),
    ).resolves.toMatchObject({ graph: null });
  });

  it("invalidates a cached theorem review when an inline semantic dependency changed", async () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, {
      id: "t1",
      kind: "theorem",
      provenance: "from-note",
      nl_statement: "the exact atlas exists",
      tex_anchor: "",
    });
    g = markPassed(g, "t1", "old-headline-hash");
    await saveGraph(graphPath(dir, "q", "v1"), g);

    const leanDir = path.join(dir, "typed-lean");
    await mkdir(leanDir, { recursive: true });
    await writeFile(
      path.join(leanDir, "TAtlas.lean"),
      "-- @node: t1\ntheorem t1_thm : True := by trivial\n",
      "utf8",
    );
    const result = await linkGraphFromStage2({
      qid: "q",
      spec: "v1",
      formalizationDir: dir,
      leanDir,
      invalidateReviewNodeIds: ["t1"],
    });
    expect(result.graph!.nodes.find((n) => n.id === "t1")!.review).toEqual({
      status: "unreviewed",
      passed_hash: null,
    });
  });
});

describe("F2 hidden semantic dependency invalidation", () => {
  const hidden = (name: string, contentHash: string, reachedFrom: string[]): HiddenStatementDef => ({
    name,
    file: "Handles.lean",
    line: 1,
    kind: "structure",
    flavor: "structure",
    reachedFrom,
    contentHash,
  });

  it("returns only headlines reached from changed/new/removed hidden definitions", () => {
    const before = [
      hidden("AtlasOutput", "old", ["thm:exact-atlas"]),
      hidden("StableOutput", "same", ["thm:stable"]),
      hidden("RemovedOutput", "gone", ["T-2"]),
    ];
    const after = [
      hidden("AtlasOutput", "new", ["thm:exact-atlas"]),
      hidden("StableOutput", "same", ["thm:stable"]),
      hidden("AddedOutput", "fresh", ["thm:new"]),
    ];
    expect(hiddenDefinitionChangeTargets(before, after)).toEqual([
      "t2",
      "thm:exact-atlas",
      "thm:new",
    ]);
  });

  it("consumes an applied source-rewind receipt as an explicit delta frontier", () => {
    const state = {
      flags: {
        source_rewind: {
          status: "applied",
          dirty_nodes: ["thm:atlas", "def:effective", "thm:atlas"],
        },
      },
    } as unknown as StateJson;
    expect(pendingSourceRewindDirtyNodeIds(state)).toEqual(["def:effective", "thm:atlas"]);
    state.flags.source_rewind!.status = "f2_revised";
    expect(pendingSourceRewindDirtyNodeIds(state)).toEqual([]);
  });
});
