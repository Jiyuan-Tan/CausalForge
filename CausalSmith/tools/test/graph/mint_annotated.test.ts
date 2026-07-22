import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode } from "../../src/graph/mutate.js";
import { mintAnnotatedNodes } from "../../src/graph/hidden.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "mint-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

// A from-note theorem t1 (already a node) whose proof introduced two tagged helpers
// (a lemma + a build-inline def) that are NOT yet graph nodes.
const LEAN = `import Mathlib

-- @node: t1
theorem t1_thm : True := by trivial

-- @node: smoothedInverseWeightLaw_klDiv_le
private lemma smoothedInverseWeightLaw_klDiv_le : True := by trivial

-- @node: smoothInverseWeightProfile
noncomputable def smoothInverseWeightProfile : Nat := 0
`;

describe("mintAnnotatedNodes", () => {
  it("mints agent-introduced nodes for tagged helpers absent from the graph (lemma vs definition by keyword)", async () => {
    await writeFile(path.join(dir, "T2.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });

    g = await mintAnnotatedNodes(g, dir);

    const lemma = g.nodes.find((n) => n.id === "smoothedInverseWeightLaw_klDiv_le");
    const def = g.nodes.find((n) => n.id === "smoothInverseWeightProfile");
    expect(lemma).toBeDefined();
    expect(lemma!.kind).toBe("lemma");
    expect(lemma!.provenance).toBe("agent-introduced");
    expect(lemma!.nl.frozen).toBe(false); // never relabelled from-note
    expect(lemma!.lean.decl_name).toBe("smoothedInverseWeightLaw_klDiv_le");
    expect(def!.kind).toBe("definition");
    expect(def!.provenance).toBe("agent-introduced");
  });

  it("leaves the existing from-note node untouched", async () => {
    await writeFile(path.join(dir, "T2.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = await mintAnnotatedNodes(g, dir);
    const t1 = g.nodes.find((n) => n.id === "t1")!;
    expect(t1.provenance).toBe("from-note");
    expect(t1.kind).toBe("theorem");
  });

  it("is idempotent: a second run mints nothing new", async () => {
    await writeFile(path.join(dir, "T2.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = await mintAnnotatedNodes(g, dir);
    const after1 = g.nodes.length;
    g = await mintAnnotatedNodes(g, dir);
    expect(g.nodes.length).toBe(after1);
  });
});
