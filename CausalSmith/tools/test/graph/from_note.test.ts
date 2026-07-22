import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "fromnote-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

// Real causalsmith note syntax: bold P/L headers, `### T-block: tN`, plus the new A/S blocks.
const MD = `# Plan

**S-1 (Weak-overlap ATE under the PO system).** potential-outcome model with tail-decaying overlap.
**required modules.** Causalean.PO, Causalean.Identification
**\`.tex\` line range.** "L1-5"

**A-2 (Overlap + bounded outcome bundle).** overlap holds and the outcome is bounded.
**\`.tex\` line range.** "L6-9"

**P-3 (Boundary-completed mu).** the completed outcome regression.

**P-4 (Hölder smoothness class).** the β-Hölder class the nuisance lives in.
**reuse.** MeasureTheory.HolderWith

### T-block: t1 — Main rate theorem
**Statement.** The cross-fit estimator attains the O_p(rho_n) rate.
**\`.tex\` line range.** "L10-40"
`;

describe("buildGraphFromMd", () => {
  it("emits setup (S), assumption (A), definition (P), theorem (T) nodes with the right provenance + anchors", async () => {
    const p = path.join(dir, "plan.md");
    await writeFile(p, MD, "utf8");
    const g = await buildGraphFromMd("stat_demo", "v1", p);

    const s1 = g.nodes.find((n) => n.id === "s1")!;
    expect(s1.kind).toBe("setup");
    expect(s1.setup?.required_modules).toEqual(["Causalean.PO", "Causalean.Identification"]);

    const a2 = g.nodes.find((n) => n.id === "a2")!;
    expect(a2.kind).toBe("assumption");
    expect(a2.provenance).toBe("from-note");
    expect(a2.nl.tex_anchor).toBe("L6-9");

    const t1 = g.nodes.find((n) => n.id === "t1")!;
    expect(t1.kind).toBe("theorem");
    expect(t1.provenance).toBe("from-note");
    expect(t1.nl.frozen).toBe(true);
    expect(t1.nl.statement).toContain("cross-fit estimator");
    expect(t1.nl.tex_anchor).toBe("L10-40");

    expect(g.nodes.find((n) => n.id === "p3")?.kind).toBe("definition");

    // P-4 has a reuse target ⇒ still a from-note paper object (frozen), with the
    // reused external decl recorded on `lean` (the library-ness lives there, not
    // in provenance — see from_note.ts).
    const p4 = g.nodes.find((n) => n.id === "p4")!;
    expect(p4.provenance).toBe("from-note");
    expect(p4.nl.frozen).toBe(true);
    expect(p4.lean).toEqual({ decl_name: "MeasureTheory.HolderWith", file: null });

    // every theorem is bound to the S-block setup
    expect(g.edges).toContainEqual({ kind: "setup-of", from: "s1", to: "t1", source: "declared" });
  });

  it("extracts F1-authored dependency edges from the .md hypothesis/dep annotations", async () => {
    const md = `# Plan

**A-2 (Overlap bundle).** overlap holds.

**P-3 (Estimand).** the target estimand.

### T-block: t1 — Main theorem
**Statement.** the rate holds.
**Load-bearing hypotheses.**
- H1 (overlap, .tex ≈ 10–12, A-2): the overlap assumption.
- H2 (estimand, .tex ≈ 13, P-3): rests on the estimand def.
`;
    const p = path.join(dir, "plan.md");
    await writeFile(p, md, "utf8");
    const g = await buildGraphFromMd("q", "v1", p);
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "a2", source: "declared" });
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "p3", source: "declared" });
  });

  it("does not drop P/A blocks whose title contains a closing paren (math titles)", async () => {
    // Regression: titles like `ℋ^β(L)` / `Bern(p)` previously truncated the header
    // regex at the first `)`, dropping the block (and its edges) from the graph.
    const md = `# Plan

**A-2 (Tail bound \`ℙ(e≤t)\`).** the overlap tail.

**P-7 (Higher-order Hölder ball \`ℋ^β(L)\`).** the smoothness class.

### T-block: t1 — Main theorem
**Statement.** rests on A-2 and the class P-7.
`;
    const p = path.join(dir, "plan.md");
    await writeFile(p, md, "utf8");
    const g = await buildGraphFromMd("q", "v1", p);
    expect(g.nodes.find((n) => n.id === "p7")?.kind).toBe("definition");
    expect(g.nodes.find((n) => n.id === "a2")?.kind).toBe("assumption");
  });

  it("stops A/S blocks before a following T-block header", async () => {
    const md = `# Plan

**A-1 (Overlap).** overlap holds.

### T-block: t1 — Main theorem
**Statement.** result.
**\`.tex\` line range.** "L10-20"
`;
    const p = path.join(dir, "plan.md");
    await writeFile(p, md, "utf8");
    const g = await buildGraphFromMd("q", "v1", p);
    expect(g.nodes.find((n) => n.id === "a1")?.nl.tex_anchor).toBe("");
    expect(g.nodes.find((n) => n.id === "t1")?.nl.tex_anchor).toBe("L10-20");
  });

  it("does NOT create dependency edges from a T-block's drift-watch (dropped) section", async () => {
    // Regression: refs named in "Hypotheses dropped … (drift-watch)" are NOT
    // load-bearing, so they must not become proof-uses edges.
    const md = `# Plan

**A-2 (Overlap tail).** the tail.

**A-6 (Lower-class smoothness).** lower-theorem only.

### T-block: t1 — Upper bound
**Statement.** rests on A-2.
**Load-bearing hypotheses.**
- H1 (tail, .tex ≈ 10, A-2): the overlap tail.
**Hypotheses dropped from t1 (drift-watch).**
- A-6 (.tex 20): converse-class condition; not load-bearing for t1.
`;
    const p = path.join(dir, "plan.md");
    await writeFile(p, md, "utf8");
    const g = await buildGraphFromMd("q", "v1", p);
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "a2", source: "declared" });
    expect(g.edges.some((e) => e.kind === "proof-uses" && e.from === "t1" && e.to === "a6")).toBe(false);
  });

  it("derives proof-uses ONLY from structured dependency annotations, not prose mentions", async () => {
    const md = `# Plan

**A-2 (Tail).** the tail.

**A-3 (Boundary).** the boundary.

**P-1 (Clip).** the clip.

**P-5 (Score).** the score.
**Depends on:** P-1.

### T-block: t1 — Main theorem
**Statement.** the rate holds; unlike A-3 this is the converse-free bound.
**Load-bearing hypotheses.**
- H1 (tail, .tex ≈ 10, A-2): the tail.
**Intuition.** contrast with A-3 throughout.
`;
    const p = path.join(dir, "plan.md");
    await writeFile(p, md, "utf8");
    const g = await buildGraphFromMd("q", "v1", p);
    // Load-bearing H1 → edge to a2; P-5 "Depends on: P-1" → edge to p1.
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "a2", source: "declared" });
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "p5", to: "p1", source: "declared" });
    // A-3 appears only in t1's Statement/Intuition prose → must NOT become an edge.
    expect(g.edges.some((e) => e.kind === "proof-uses" && e.from === "t1" && e.to === "a3")).toBe(false);
  });

  it("synthesizes a fallback setup node when the note has no S-block", async () => {
    const p = path.join(dir, "plan.md");
    await writeFile(p, "### T-block: t1 — Only a theorem\n**Statement.** x.\n", "utf8");
    const g = await buildGraphFromMd("q", "v1", p);
    expect(g.nodes.find((n) => n.id === "setup")?.kind).toBe("setup");
    expect(g.edges).toContainEqual({ kind: "setup-of", from: "setup", to: "t1", source: "declared" });
  });

  it("is best-effort on a missing file (empty graph, no throw)", async () => {
    const g = await buildGraphFromMd("q", "v1", path.join(dir, "nope.md"));
    expect(g.nodes).toEqual([]);
  });
});
