import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode } from "../../src/graph/mutate.js";
import { extractFromLean } from "../../src/graph/extractor.js";
import { mintHiddenDefNodes } from "../../src/graph/hidden.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "hidden-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

// t1's CONCLUSION names `rateBound` (an ℝ-valued build-inline quantity with no
// node/annotation) — surfaced by findHiddenStatementDefs (a direct-hypothesis def
// would instead be excluded as already covered by the H.1 matrix).
const LEAN = `
def rateBound : ℝ := 1

-- @node: t1
theorem t1_thm : rateBound = 1 := by sorry
`;

describe("mintHiddenDefNodes", () => {
  it("mints an auto definition node for a build-inline def reached from a statement", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    ({ graph: g } = await extractFromLean(g, dir));
    g = await mintHiddenDefNodes(g, dir);
    const aux = g.nodes.find((n) => n.lean.decl_name === "rateBound");
    expect(aux?.kind).toBe("definition");
    expect(aux?.provenance).toBe("agent-introduced");
    expect(aux?.id).toBe("aux_rateBound");
  });

  it("is idempotent", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    ({ graph: g } = await extractFromLean(g, dir));
    g = await mintHiddenDefNodes(g, dir);
    const n1 = g.nodes.length;
    g = await mintHiddenDefNodes(g, dir);
    expect(g.nodes.length).toBe(n1);
  });
});
