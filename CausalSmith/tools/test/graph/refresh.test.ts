import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { refreshGraphForGate, applyVerdictsToGraph } from "../../src/graph/refresh.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode } from "../../src/graph/mutate.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "refresh-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const MD = `### T-block: t1 — Rate theorem
**Statement.** the rate bound holds.
`;
const LEAN = `
def rateBound : ℝ := 1

-- @node: t1
theorem t1_thm : rateBound = 1 := by sorry
`;

async function scaffold() {
  await writeFile(path.join(dir, "q_v1.md"), MD, "utf8");
  const leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "T1.lean"), LEAN, "utf8");
  return leanDir;
}

describe("refreshGraphForGate", () => {
  it("builds from .md (no graph yet), extracts, mints hidden defs, returns skeleton+dirty+coverage", async () => {
    const leanDir = await scaffold();
    const r = await refreshGraphForGate({ formalizationDir: dir, qid: "q", spec: "v1", leanDir, mdPath: path.join(dir, "q_v1.md") });
    expect(r.graph).not.toBeNull();
    const t1 = r.graph!.nodes.find((n) => n.id === "t1")!;
    expect(t1.lean.decl_name).toBe("t1_thm");
    expect(r.graph!.nodes.some((n) => n.id === "aux_rateBound")).toBe(true);
    expect(r.skeleton.some((row) => row.obj_id === "T-1")).toBe(true);
    expect(r.dirty).toContain("t1");
    expect(r.coverage).not.toBeNull();
  });

  it("returns {graph:null} when neither graph JSON nor .md exists", async () => {
    const leanDir = path.join(dir, "lean2");
    await mkdir(leanDir, { recursive: true });
    const r = await refreshGraphForGate({ formalizationDir: dir, qid: "none", spec: "v1", leanDir });
    expect(r.graph).toBeNull();
    expect(r.skeleton).toEqual([]);
  });

  it("hard-fails refresh when two declarations reuse one @node id", async () => {
    const leanDir = await scaffold();
    await writeFile(
      path.join(leanDir, "T1.lean"),
      [
        "-- @node: t1",
        "theorem t1_thm : True := by trivial",
        "",
        "-- @node: t1",
        "theorem t1_companion : True := by trivial",
      ].join("\n"),
      "utf8",
    );

    const r = await refreshGraphForGate({
      formalizationDir: dir,
      qid: "q",
      spec: "v1",
      leanDir,
      mdPath: path.join(dir, "q_v1.md"),
    });

    expect(r.graph).toBeNull();
    expect(r.error).toMatch(/unlinked Lean @node annotations/);
    expect(r.error).toContain("t1->t1_thm@T1.lean");
    expect(r.error).toContain("t1->t1_companion@T1.lean");
  });
});

const cw = (obj_id: string, verdict: string) =>
  ({ obj_id, kind: "theorem", title: "", tex: { label: "", line_range: "" }, lean: null, verdict }) as any;

describe("applyVerdictsToGraph", () => {
  it("maps verdicts → node status (exact/equivalent→matched, drift family→drift, unmatched→skip)", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addNode(g, { id: "p2", kind: "definition", provenance: "from-note", nl_statement: "d", tex_anchor: "" });
    g = addNode(g, { id: "l3", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = applyVerdictsToGraph(g, [cw("T-1", "equivalent"), cw("P-2", "weaker-in-Lean"), cw("L-3", "unmatched")], { t1: "h1" });
    expect(g.nodes.find((n) => n.id === "t1")!.review).toEqual({ status: "matched", passed_hash: "h1" });
    expect(g.nodes.find((n) => n.id === "p2")!.review.status).toBe("drift");
    expect(g.nodes.find((n) => n.id === "l3")!.review.status).toBe("unreviewed"); // unmatched → skipped
  });

  it("derivedObjIds override matched→derived", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = applyVerdictsToGraph(g, [cw("L-1", "exact")], {}, new Set(["L-1"]));
    expect(g.nodes[0].review.status).toBe("derived");
  });

  it("prefers an exact case-sensitive uncolonized graph id over legacy normalization", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "hP_pointwise_witness", kind: "assumption", provenance: "agent-introduced", nl_statement: "witness", tex_anchor: "" });
    g = addNode(g, { id: "hp_pointwise_witness", kind: "assumption", provenance: "from-note", nl_statement: "legacy collision", tex_anchor: "" });

    g = applyVerdictsToGraph(g, [cw("hP_pointwise_witness", "equivalent")], { hP_pointwise_witness: "exact-hash" });

    expect(g.nodes.find((n) => n.id === "hP_pointwise_witness")!.review).toEqual({ status: "matched", passed_hash: "exact-hash" });
    expect(g.nodes.find((n) => n.id === "hp_pointwise_witness")!.review.status).toBe("unreviewed");
  });

  it("preserves colon ids and unambiguous legacy from-note aliases", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "thm:case-sensitive", kind: "theorem", provenance: "from-note", nl_statement: "core theorem", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "legacy theorem", tex_anchor: "" });

    g = applyVerdictsToGraph(g, [cw("thm:case-sensitive", "exact"), cw("T-1", "equivalent")], {
      "thm:case-sensitive": "core-hash",
      t1: "legacy-hash",
    });

    expect(g.nodes.find((n) => n.id === "thm:case-sensitive")!.review.passed_hash).toBe("core-hash");
    expect(g.nodes.find((n) => n.id === "t1")!.review.passed_hash).toBe("legacy-hash");
  });

  it("fails closed for ambiguous or missing reviewed targets", () => {
    let ambiguous = createEmptyGraph("q", "v1");
    ambiguous = addNode(ambiguous, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "legacy", tex_anchor: "" });
    ambiguous = addNode(ambiguous, { id: "ass:other", kind: "assumption", provenance: "from-note", nl_statement: "core", tex_anchor: "" });
    ambiguous = {
      ...ambiguous,
      nodes: ambiguous.nodes.map((n) => n.id === "ass:other" ? { ...n, obj_id: "A-1" } : n),
    };

    expect(() => applyVerdictsToGraph(ambiguous, [cw("A-1", "equivalent")], {}))
      .toThrow('review verdict target resolution failed for "A-1": ambiguous aliases: a1, ass:other');
    expect(() => applyVerdictsToGraph(createEmptyGraph("q", "v1"), [cw("missing_Target", "equivalent")], {}))
      .toThrow('review verdict target resolution failed for "missing_Target": no graph node or unambiguous legacy/from-note alias');
  });

  it("persists a real sym-prefixed graph node but skips an explicitly synthetic symbol row", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "sym:r_star", kind: "definition", provenance: "from-note", nl_statement: "radius", tex_anchor: "" });
    const owners = new Map<string, string | null>([
      ["sym:r_star", "sym:r_star"],
      ["sym:synthetic", null],
    ]);

    g = applyVerdictsToGraph(
      g,
      [cw("sym:r_star", "equivalent"), cw("sym:synthetic", "equivalent")],
      { "sym:r_star": "real-sym-hash" },
      new Set(),
      owners,
    );

    expect(g.nodes[0].review).toEqual({ status: "matched", passed_hash: "real-sym-hash" });
    expect(g.nodes).toHaveLength(1);
  });

  it("validates the whole verdict batch before applying any row", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "theorem", tex_anchor: "" });
    const owners = new Map<string, string | null>([
      ["T-1", "t1"],
      ["missing", "does-not-exist"],
    ]);

    expect(() => applyVerdictsToGraph(
      g,
      [cw("T-1", "equivalent"), cw("missing", "equivalent")],
      { t1: "h1" },
      new Set(),
      owners,
    )).toThrow('review verdict target resolution failed for "missing": bound graph node "does-not-exist" is missing');
    expect(g.nodes[0].review.status).toBe("unreviewed");
  });
});
