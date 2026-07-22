import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge } from "../../src/graph/mutate.js";
import { extractFromLean, extractLeanCommentText, topLevelAssignIndex } from "../../src/graph/extractor.js";

let dir: string;
beforeEach(async () => {
  dir = await mkdtemp(path.join(tmpdir(), "graph-ex-"));
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

const LEAN = `
-- @node: p1
def overlapBound (x : ℝ) : Prop := 0 < x

-- @node: t1
theorem t1_main (h : overlapBound 1) : True := by
  sorry
`;

describe("Lean lexical helpers", () => {
  it("finds only the declaration-level assignment, ignoring comments, strings, binders, and lets", () => {
    const src = 'def f (x : Nat := 1) : Nat := let y := 2; y + x -- := fake\n';
    expect(src.slice(topLevelAssignIndex(src), topLevelAssignIndex(src) + 2)).toBe(":=");
    expect(topLevelAssignIndex('theorem t : (let x := 1; x = 1) := by trivial')).toBeGreaterThan(20);
  });

  it("extracts genuine comment tags but masks string-literal lookalikes", () => {
    const comments = extractLeanCommentText('def x := "-- @realizes Fake" -- @realizes Real\n');
    expect(comments).toContain("@realizes Real");
    expect(comments).not.toContain("@realizes Fake");
  });
});

describe("extractFromLean", () => {
  it("links annotated decls and refreshes proof state", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "overlap bound", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });

    const { graph, hashes, unlinked } = await extractFromLean(g, dir);

    const t1 = graph.nodes.find((n) => n.id === "t1")!;
    expect(t1.lean).toEqual({ decl_name: "t1_main", file: "T1.lean" });
    expect(t1.proof).toEqual({ state: "sorry", sorry_count: 1 });
    expect(hashes["t1"]).toMatch(/^[0-9a-f]{40}$/);
    expect(graph.edges).toContainEqual({ kind: "statement-uses", from: "t1", to: "p1", source: "extracted" });
    expect(unlinked).toEqual([]);
  });

  // A scratch COPY of a real file under the paper tmp/ workspace (agents are told to put
  // Lean probes there) duplicates its `-- @node:` tags; extraction must ignore tmp/ or the
  // duplicate makes every graph refresh fail the node as unlinked.
  it("ignores the paper tmp/ workspace (a scratch copy must not duplicate @node tags)", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    const scratch = path.join(dir, "tmp");
    await (await import("node:fs/promises")).mkdir(scratch, { recursive: true });
    await writeFile(path.join(scratch, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "overlap bound", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });

    const { graph, unlinked } = await extractFromLean(g, dir);
    expect(unlinked).toEqual([]);
    expect(graph.nodes.find((n) => n.id === "t1")!.lean).toEqual({ decl_name: "t1_main", file: "T1.lean" });
  });

  it("reports annotated decls with no matching graph node as unlinked", async () => {
    await writeFile(path.join(dir, "T1.lean"), "-- @node: ghost\ntheorem ghost_thm : True := trivial\n", "utf8");
    const g = createEmptyGraph("q", "v1");
    const { unlinked } = await extractFromLean(g, dir);
    expect(unlinked).toEqual([{ id: "ghost", decl_name: "ghost_thm", file: "T1.lean" }]);
  });

  it("refuses to relink an undelivered theorem and clears its stale proof anchor", async () => {
    await writeFile(
      path.join(dir, "T1.lean"),
      "-- @node: t1\ntheorem staleAtlas : True := by sorry\n",
      "utf8",
    );
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "atlas", tex_anchor: "" });
    g = {
      ...g,
      nodes: g.nodes.map((n) => ({
        ...n,
        lean: { decl_name: "staleAtlas", file: "T1.lean" },
        proof: { state: "sorry", sorry_count: 1 },
        delivery: { status: "undelivered", role: "secondary", reason: "citation overflow" },
      })),
    };
    const { graph, unlinked } = await extractFromLean(g, dir);
    expect(graph.nodes[0].lean).toEqual({ decl_name: null, file: null });
    expect(graph.nodes[0].proof).toEqual({ state: "sorry", sorry_count: 0 });
    expect(graph.nodes[0].review.status).toBe("unreviewed");
    expect(unlinked).toEqual([{ id: "t1", decl_name: "staleAtlas", file: "T1.lean" }]);
  });

  it("rejects duplicate annotations for one graph node instead of linking first-wins", async () => {
    await writeFile(
      path.join(dir, "T1.lean"),
      [
        "-- @node: t1",
        "def t1Primary : Prop := True",
        "",
        "-- @node: t1",
        "def t1Companion : Prop := True",
      ].join("\n"),
      "utf8",
    );
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, {
      id: "t1",
      kind: "definition",
      provenance: "from-note",
      nl_statement: "one canonical declaration",
      tex_anchor: "",
    });

    const { graph, hashes, unlinked } = await extractFromLean(g, dir);

    expect(graph).toEqual(g);
    expect(hashes).toEqual({});
    expect(unlinked).toEqual([
      { id: "t1", decl_name: "t1Primary", file: "T1.lean" },
      { id: "t1", decl_name: "t1Companion", file: "T1.lean" },
    ]);
  });

  it("ignores an indented in-body duplicate and keeps the column-zero canonical anchor", async () => {
    await writeFile(
      path.join(dir, "T1.lean"),
      [
        "-- @node: p1",
        "def primary : Prop :=",
        "  -- @node: p1",
        "  True",
        "",
        "lemma companion : True := by trivial",
      ].join("\n"),
      "utf8",
    );
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, {
      id: "p1",
      kind: "definition",
      provenance: "from-note",
      nl_statement: "one canonical declaration",
      tex_anchor: "",
    });

    const { graph, hashes, unlinked } = await extractFromLean(g, dir);

    expect(graph.nodes[0].lean.decl_name).toBe("primary");
    expect(hashes.p1).toMatch(/^[0-9a-f]{40}$/);
    expect(unlinked).toEqual([]);
  });

  it("overwrites prior extracted edges but preserves declared edges", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "ob", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "p1", source: "declared" });
    g = addEdge(g, { kind: "statement-uses", from: "t1", to: "p1", source: "extracted" }); // stale, rebuilt
    const { graph } = await extractFromLean(g, dir);
    expect(graph.edges.filter((e) => e.source === "declared")).toHaveLength(1);
    expect(graph.edges.filter((e) => e.kind === "statement-uses")).toHaveLength(1);
  });

  it("keeps statement-uses edges for binders AFTER an inline `:=` in the signature", async () => {
    // Regression: a hypothesis containing a `let g … :=` (or a binder default `(x : T := d)`)
    // used to truncate the statement at that FIRST `:=`, silently dropping every later binder's
    // edge — e.g. `(hvc : PolicyClassVC …)` after a `let` in an earlier hypothesis.
    await writeFile(
      path.join(dir, "T1.lean"),
      [
        "-- @node: pvc",
        "def PolicyClassVC (s : Set ℝ) : Prop := True",
        "",
        "-- @node: t1",
        "theorem t1_main",
        "    (hbig : ∀ n : ℕ,",
        "      let g : ℝ → ℝ := fun x => x",
        "      g 0 = 0)",
        "    (hvc : PolicyClassVC ∅) : True := by",
        "  trivial",
      ].join("\n"),
      "utf8",
    );
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "pvc", kind: "assumption", provenance: "from-note", nl_statement: "vc", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    const { graph } = await extractFromLean(g, dir);
    // the `let g := …` no longer truncates: the trailing `(hvc : PolicyClassVC …)` binder is seen.
    expect(graph.edges).toContainEqual({ kind: "statement-uses", from: "t1", to: "pvc", source: "extracted" });
    // and the proof state still reflects the real proof body (no `sorry` here), not the inline `:=`.
    expect(graph.nodes.find((n) => n.id === "t1")!.proof).toEqual({ state: "complete", sorry_count: 0 });
  });

  it("maps an assumption's uniform variant `<Pred>Unif` in a signature to the base assumption node", async () => {
    // A lemma takes the CLASS-UNIFORM companion `VCLocalizedEnvelopeUnif` (∃ uniform consts, ∀ law P,
    // …) as a signature hypothesis. That binder is the assumption `VCLocalizedEnvelope` stated
    // uniformly, so it must draw a statement-uses edge to the assumption node — otherwise the rendered
    // lemma silently omits the hypothesis. (Real incident: Lemma 9 `crude_localized_master_bound`.)
    await writeFile(
      path.join(dir, "T1.lean"),
      [
        "-- @node: env",
        "def VCLocalizedEnvelope (P : ℝ) (s : Set ℝ) : Prop := True",
        "",
        "-- @node: t1",
        "theorem t1_main (h : VCLocalizedEnvelopeUnif (∅ : Set ℝ)) : True := by",
        "  trivial",
      ].join("\n"),
      "utf8",
    );
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "env", kind: "assumption", provenance: "from-note", nl_statement: "vc envelope", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    const { graph } = await extractFromLean(g, dir);
    expect(graph.edges).toContainEqual({ kind: "statement-uses", from: "t1", to: "env", source: "extracted" });
  });

  it("does NOT invent a `<Pred>Unif` edge for a non-assumption node", async () => {
    // The alias is scoped to assumptions (uniform-over-class conditions); a `def`/lemma companion
    // named `FooUnif` must not silently link to an unrelated `Foo` definition node.
    await writeFile(
      path.join(dir, "T1.lean"),
      [
        "-- @node: d",
        "def Foo (x : ℝ) : Prop := True",
        "",
        "-- @node: t1",
        "theorem t1_main (h : FooUnif 1) : True := by trivial",
      ].join("\n"),
      "utf8",
    );
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "d", kind: "definition", provenance: "from-note", nl_statement: "foo", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    const { graph } = await extractFromLean(g, dir);
    expect(graph.edges.some((e) => e.kind === "statement-uses" && e.from === "t1" && e.to === "d")).toBe(false);
  });

  it("draws a statement-uses edge to a library-backed node (preset decl_name, no annotation)", async () => {
    await writeFile(path.join(dir, "T1.lean"), "-- @node: t1\ntheorem t1_main (h : HolderWith 1 2 f) : True := by sorry\n", "utf8");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = addNode(g, { id: "hclass", kind: "definition", provenance: "library", nl_statement: "Hölder class", tex_anchor: "" });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "hclass" ? { ...n, lean: { decl_name: "HolderWith", file: null } } : n)) };

    const { graph } = await extractFromLean(g, dir);
    expect(graph.edges).toContainEqual({ kind: "statement-uses", from: "t1", to: "hclass", source: "extracted" });
  });
});
