import { describe, it, expect } from "vitest";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { buildProseEntries } from "../src/presentation/emit.js";
import type { CrosswalkEntry } from "../src/presentation/types.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const node = (
  id: string,
  obj_id: string,
  kind: FormalizationGraph["nodes"][number]["kind"],
  decl: string | null,
  status = "matched",
): FormalizationGraph["nodes"][number] => ({
  id,
  obj_id,
  kind,
  provenance: "from-note",
  nl: { statement: id, tex_anchor: "", frozen: true },
  lean: { decl_name: decl, file: decl ? "Basic.lean" : null },
  review: { status: status as never, passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});

const cw = (obj_id: string, decl: string): CrosswalkEntry => ({
  obj_id,
  kind: "definition",
  title: obj_id,
  tex: null,
  lean: { file: "Basic.lean", decl, decl_kind: "def", line: 0 },
  verdict: "equivalent",
});

describe("buildProseEntries", () => {
  it("builds a standalone drawer entry from a graph node's Lean decl", async () => {
    const dir = await mkdtemp(join(tmpdir(), "prose-"));
    await writeFile(join(dir, "Basic.lean"), "/-- iid -/\nstructure IsIIDSample : Prop\n", "utf8");
    const graph: FormalizationGraph = {
      qid: "q",
      specialization: "s",
      nodes: [node("ass:iid", "A-1", "assumption", "IsIIDSample")],
      edges: [],
    };
    const { entries, snippets } = await buildProseEntries({
      objIds: ["A-1"],
      graph,
      crosswalk: [cw("A-1", "IsIIDSample")],
      repoRoot: dir,
      leanSubdir: ".",
    });
    expect(entries).toHaveLength(1);
    expect(entries[0]).toMatchObject({ obj_id: "A-1", env: "prose", status: "matched" });
    expect(entries[0].lean?.decl).toBe("IsIIDSample");
    expect(snippets["A-1"].statement).toContain("IsIIDSample");
    await rm(dir, { recursive: true, force: true });
  });

  it("gives an NL-only fallback for a graph node with no Lean decl (e.g. a prose setup)", async () => {
    const dir = await mkdtemp(join(tmpdir(), "prose-"));
    const graph: FormalizationGraph = {
      qid: "q",
      specialization: "s",
      nodes: [node("S-1", "S-1", "setup", null, "unreviewed")],
      edges: [],
    };
    const { entries, snippets } = await buildProseEntries({
      objIds: ["S-1"],
      graph,
      crosswalk: [],
      repoRoot: dir,
      leanSubdir: ".",
    });
    expect(entries[0]).toMatchObject({ obj_id: "S-1", env: "prose", lean: null, status: "unreviewed" });
    expect(entries[0].fallback).toBeTruthy();
    expect(snippets["S-1"]).toBeUndefined();
    expect(entries[0].paper_label).toBe("Setup S-1");
    await rm(dir, { recursive: true, force: true });
  });

  it("skips unknown obj-ids (validated separately at P4)", async () => {
    const graph: FormalizationGraph = { qid: "q", specialization: "s", nodes: [], edges: [] };
    const { entries } = await buildProseEntries({
      objIds: ["Z-9"],
      graph,
      crosswalk: [],
      repoRoot: "/nowhere",
      leanSubdir: ".",
    });
    expect(entries).toEqual([]);
  });
});
