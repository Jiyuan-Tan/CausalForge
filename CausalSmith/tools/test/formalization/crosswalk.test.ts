import { mkdtemp, mkdir, rm, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import {
  buildCrosswalkSkeleton,
  buildCompleteCrosswalkFromGraph,
  findHiddenStatementDefs,
  findStatementSemanticDefs,
  persistCrosswalk,
  renderCrosswalkMd,
} from "../../src/formalization/crosswalk.js";
import type { FormalizationGraph } from "../../src/graph/types.js";

// A Basic.lean mirroring the stat_ate_overlap_decay shape: a P-10 class def
// annotated with its block id in a `/-! ## P-10 — … -/` section comment, plus a
// helper def with NO block id (must be skipped), and a T-1 theorem (matched by
// name `t1_thm`). The section comment deliberately omits A4/A5/A6 clauses.
const BASIC = `import Mathlib

/-- A helper with no block id — must be skipped by the crosswalk. -/
noncomputable def overlapDen (x : Real) : Real := x + 1

/-! ## P-10 — Triangular-array weak-overlap class (build-inline)

Encodes A1, A2 and a boundary condition; A4/A5/A6 deferred to theorem hyps. -/
noncomputable def triangularClass (k b : Real) (n : Nat) : Set Real :=
  {x | 0 ≤ x}

/-- **L-7.** A lemma — excluded from the crosswalk. -/
lemma l7_aux : True := by sorry

theorem t1_thm (n : Nat) : n + 0 = n := by simp
`;

// The F1 .md with P-10 (definition) and T-1 (theorem) blocks. P-10 carries a
// quoted .tex line range label (durable anchor).
const MD = `# Note

### P-10. Triangular-array weak-overlap class \`𝒫\`.
- **Signature.** Laws satisfying A1, A2, A3, A4, A5 and A6 at λ_n★.
- **.tex line range.** Definition "Triangular-array weak-overlap class".

### L-7. A lemma block — excluded.
- **.tex line range.** tex:600.

### T-1. Corrected upper bound.
- **.tex line range.** tex:741.
`;

let dir: string;
let leanDir: string;
let mdPath: string;

beforeEach(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "crosswalk-"));
  leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "Basic.lean"), BASIC, "utf8");
  mdPath = path.join(dir, "note.md");
  await writeFile(mdPath, MD, "utf8");
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("buildCrosswalkSkeleton", () => {
  it("matches P-10 → triangularClass and T-1 → t1_thm with correct anchors", async () => {
    const sk = await buildCrosswalkSkeleton(leanDir, mdPath);
    const p10 = sk.find((e) => e.obj_id === "P-10");
    const t1 = sk.find((e) => e.obj_id === "T-1");
    expect(p10).toBeDefined();
    expect(p10!.kind).toBe("definition");
    expect(p10!.lean).toMatchObject({ file: "Basic.lean", decl: "triangularClass", decl_kind: "def" });
    expect(p10!.tex.label).toBe("Triangular-array weak-overlap class");
    expect(p10!.verdict).toBe("unmatched");
    expect(t1).toBeDefined();
    expect(t1!.kind).toBe("theorem");
    expect(t1!.lean).toMatchObject({ decl: "t1_thm", decl_kind: "theorem" });
  });

  it("excludes lemmas and obj-id-less helper defs", async () => {
    const sk = await buildCrosswalkSkeleton(leanDir, mdPath);
    const ids = sk.map((e) => e.obj_id);
    expect(ids).not.toContain("L-7"); // lemma block + lemma decl excluded
    // overlapDen has no block id → never appears as a Lean-only entry
    expect(sk.some((e) => e.lean?.decl === "overlapDen")).toBe(false);
  });

  it("BFS is not truncated by a named-argument `:=` in a hypothesis binder", async () => {
    // A theorem whose hypothesis uses Lean named-argument syntax `(𝒳 := 𝒳)`
    // BEFORE referencing the class def. A raw `indexOf(":=")` would cut the
    // statement at the named arg and never reach `hiddenClass` (and everything
    // it transitively reaches) — the bug that made the AUX hidden-def audit
    // silently cover almost nothing for `t2_thm`.
    const lean = `import Mathlib

/-- A build-inline membership predicate with no obj_id. -/
def hiddenInner (g : Real) : Prop := 0 ≤ g

/-- The class def, named in the CONCLUSION after the hypothesis named-arg. -/
def hiddenClass (k : Real) : Prop := hiddenInner k

/-- A wrapper that takes a named argument. -/
def wrap (p : Prop) : Prop := p

/-- **T-1.** -/
theorem t1_thm (n : Nat) (h : wrap (p := True)) : hiddenClass 0 := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    const names = hidden.map((h) => h.name);
    // The conclusion `hiddenClass 0` sits AFTER the `(p := True)` named-arg. A raw
    // first-`:=` cut would drop it (and its transitively-reached `hiddenInner`);
    // the depth-0 cut reaches both.
    expect(names).toContain("hiddenClass");
    expect(names).toContain("hiddenInner");
  });

  it("treats a typed-core @node theorem as a hidden-definition reachability seed", async () => {
    const lean = `import Mathlib

def atlasSemantics : Prop := True

structure AtlasPayload where
  exact : atlasSemantics

-- @node: thm:exact-real-atlas
theorem exactRealAtlas : Nonempty AtlasPayload := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    const payload = hidden.find((h) => h.name === "AtlasPayload");
    const semantics = hidden.find((h) => h.name === "atlasSemantics");
    expect(payload?.reachedFrom).toEqual(["thm:exact-real-atlas"]);
    expect(semantics?.reachedFrom).toEqual(["thm:exact-real-atlas"]);
    expect(payload?.contentHash).toMatch(/^[0-9a-f]{40}$/);
  });

  it("tracks deep computational statement dependencies without surfacing them as F2.5 AUX rows", async () => {
    const lean = `import Mathlib

def cadRealRootsAt (x : Real) : Set Real := {z | z = x}
def RealClosedFieldCADInterface : Prop := (cadRealRootsAt 0).Finite

-- @node: def:real-atlas-handle
def realAtlasHandleOutput : Prop := RealClosedFieldCADInterface

-- @node: thm:exact-real-atlas
theorem exactRealAtlas (hCAD : realAtlasHandleOutput) : True := by trivial
`;
    await writeFile(path.join(leanDir, "CAD.lean"), lean, "utf8");
    const semantic = await findStatementSemanticDefs(leanDir);
    expect(semantic.find((d) => d.name === "cadRealRootsAt")?.reachedFrom).toEqual([
      "thm:exact-real-atlas",
    ]);
    const hidden = await findHiddenStatementDefs(leanDir);
    expect(hidden.some((d) => d.name === "cadRealRootsAt")).toBe(false);
  });

  it("binds T-1 to the canonical t1_thm, not an earlier same-prefixed shadow/helper", async () => {
    // Mirrors the stat_ate_overlap_decay layout: an archived `_deterministic_shadow`
    // and a private `t1_thm_random_aggregate_from_pieces` helper both precede the
    // real `t1_thm` in the file and all share the `t1_` name prefix. The skeleton
    // must skip the shadow (no obj_id) and prefer the canonical headline over the
    // earlier helper — otherwise the paper would verify the wrong T-1 decl.
    const lean = `import Mathlib

/-- Deprecated deterministic-CF shadow of **T-1**. Kept for provenance. -/
theorem t1_thm_deterministic_shadow (n : Nat) : n = n := by rfl

/-- Private rate-aggregation helper for the random headline. -/
theorem t1_thm_random_aggregate_from_pieces (n : Nat) : n + 0 = n := by simp

/-- **T-1 (faithful random cross-fit headline).** -/
theorem t1_thm (n : Nat) : 0 + n = n := by simp
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const md = `# Note

### T-1. Upper bound.
- **.tex line range.** tex:741.
`;
    await writeFile(mdPath, md, "utf8");
    const sk = await buildCrosswalkSkeleton(leanDir, mdPath);
    const t1 = sk.find((e) => e.obj_id === "T-1");
    expect(t1!.lean).toMatchObject({ decl: "t1_thm" });
    // the shadow never claims an obj_id at all
    expect(sk.some((e) => e.lean?.decl === "t1_thm_deterministic_shadow")).toBe(false);
  });
});

describe("buildCompleteCrosswalkFromGraph", () => {
  it("downgrades unresolved local anchors instead of writing line:null", async () => {
    const g: FormalizationGraph = {
      qid: "q",
      specialization: "s",
      nodes: [{
        id: "p1",
        obj_id: "P-1",
        kind: "definition",
        provenance: "from-note",
        nl: { statement: "S", tex_anchor: "", frozen: true },
        lean: { decl_name: "MissingDecl", file: "Basic.lean" },
        review: { status: "unreviewed", passed_hash: null },
        proof: { state: "sorry", sorry_count: 0 },
      }],
      edges: [],
    };
    const rows = await buildCompleteCrosswalkFromGraph(g, leanDir);
    expect(rows[0].lean).toBeNull();
  });
});

// A scaffold mirroring the policy-regret laundering shape:
//  - `lawClass` (Prop, ∃ real constants): reached only TRANSITIVELY via the
//    conclusion def `witnessRisk`, NO obj_id → the uniform-constant trap.
//  - `witnessRisk` (Prop): named directly in the CONCLUSION → surfaced.
//  - `hypClass` (Prop): named directly as a HYPOTHESIS → covered by H.1, must NOT
//    re-surface; but its body references `hiddenSub`, reached transitively under a
//    hypothesis (a hidden over-strengthening) → `hiddenSub` MUST surface.
//  - `bundleStruct` (structure): an assumption-bundle reached from the conclusion.
//  - `scoreVal` (ℝ computational) and `unreachedClass` (Prop, reached by nobody):
//    must stay hidden.
const LAUNDER = `import Mathlib

/-- Build-inline membership predicate — NO block id, ∃ over real constants. -/
def lawClass (P : Nat) : Prop := ∃ Co co : ℝ, 0 < Co ∧ 0 < co ∧ Co + co = (P : ℝ)

/-- An ℝ-valued helper reached only via another def's body — NOT in a conclusion. -/
def helperVal (P : Nat) : ℝ := (P : ℝ)

/-- Converse conclusion predicate referencing the membership predicate. -/
def witnessRisk (P : Nat) (rate : ℝ) : Prop := lawClass P ∧ rate ≤ helperVal P

/-- A predicate hidden UNDER a hypothesis predicate (reached transitively). -/
def hiddenSub (P : Nat) : Prop := P ≠ 0

/-- A hypothesis predicate named directly in the theorem — covered by the H.1 matrix. -/
def hypClass (P : Nat) : Prop := hiddenSub P ∧ P ≤ P

/-- An assumption-bundle structure reached from the conclusion. -/
structure bundleStruct (P : Nat) : Prop where
  fieldA : P = P

/-- An ℝ-valued quantity named DIRECTLY in the conclusion — its formula is checked. -/
def scoreVal (P : Nat) : ℝ := (P : ℝ)

/-- A Prop ∃-real class reached by NO theorem — must stay hidden. -/
def unreachedClass : Prop := ∃ K : ℝ, 0 < K

theorem t2_thm (P : Nat) (h : hypClass P) :
    ∃ rate : ℝ, witnessRisk P rate ∧ scoreVal P = scoreVal P ∧ bundleStruct P := by sorry
`;

const LAUNDER_MD = `# Note

### T-2. Converse witness bound.
- **.tex line range.** tex:200.
`;

describe("hidden-statement-def augmentation (laundering surface)", () => {
  let ldir: string;
  let lmd: string;
  beforeEach(async () => {
    const d = await mkdtemp(path.join(os.tmpdir(), "crosswalk-launder-"));
    ldir = path.join(d, "lean");
    await mkdir(ldir, { recursive: true });
    await writeFile(path.join(ldir, "Basic.lean"), LAUNDER, "utf8");
    lmd = path.join(d, "note.md");
    await writeFile(lmd, LAUNDER_MD, "utf8");
  });

  it("surfaces a transitively-reached ∃-real-constant def with the uniform-constant flavor", async () => {
    const sk = await buildCrosswalkSkeleton(ldir, lmd);
    const aux = sk.find((e) => e.obj_id === "AUX-lawClass");
    expect(aux).toBeDefined();
    expect(aux!.kind).toBe("definition");
    expect(aux!.lean).toMatchObject({ decl: "lawClass", decl_kind: "def" });
    expect(aux!.verdict).toBe("unmatched");
    expect(aux!.title).toContain("T-2"); // records the reaching T-block
    expect(aux!.title).toContain("uniform-constant"); // const-existential flavor
  });

  it("surfaces a reached Prop conclusion def with the inline-predicate flavor", async () => {
    const sk = await buildCrosswalkSkeleton(ldir, lmd);
    const aux = sk.find((e) => e.obj_id === "AUX-witnessRisk");
    expect(aux).toBeDefined();
    expect(aux!.title).toContain("faithfully encodes"); // generic inline-predicate flavor
  });

  it("surfaces a predicate hidden TRANSITIVELY under a hypothesis, but not the direct hypothesis itself", async () => {
    const sk = await buildCrosswalkSkeleton(ldir, lmd);
    // hiddenSub is reached only via hypClass's body → must surface (hidden over-strengthening risk)
    expect(sk.some((e) => e.lean?.decl === "hiddenSub")).toBe(true);
    // hypClass is named directly as a hypothesis → already in the H.1 matrix → must NOT re-surface
    expect(sk.some((e) => e.lean?.decl === "hypClass")).toBe(false);
  });

  it("surfaces a reached assumption-bundle structure with the structure flavor", async () => {
    const sk = await buildCrosswalkSkeleton(ldir, lmd);
    const aux = sk.find((e) => e.obj_id === "AUX-bundleStruct");
    expect(aux).toBeDefined();
    expect(aux!.lean).toMatchObject({ decl: "bundleStruct", decl_kind: "structure" });
    expect(aux!.title).toContain("assumption-bundle");
  });

  it("surfaces a conclusion-named ℝ quantity with the formula flavor", async () => {
    const sk = await buildCrosswalkSkeleton(ldir, lmd);
    const aux = sk.find((e) => e.obj_id === "AUX-scoreVal");
    expect(aux).toBeDefined();
    expect(aux!.lean).toMatchObject({ decl: "scoreVal", decl_kind: "def" });
    expect(aux!.title).toContain("formula"); // ℝ-quantity flavor
  });

  it("does NOT surface ℝ helpers reached only off-conclusion, or unreached defs", async () => {
    const sk = await buildCrosswalkSkeleton(ldir, lmd);
    expect(sk.some((e) => e.lean?.decl === "helperVal")).toBe(false); // ℝ-valued, not in a conclusion
    expect(sk.some((e) => e.lean?.decl === "unreachedClass")).toBe(false); // reached by no theorem
  });
});

describe("persistCrosswalk + renderCrosswalkMd", () => {
  it("writes JSON + MD and the MD shows the P-10 row", async () => {
    const sk = await buildCrosswalkSkeleton(leanDir, mdPath);
    const merged = sk.map((e) => (e.obj_id === "P-10" ? { ...e, verdict: "weaker-in-Lean" as const, note: "n" } : e));
    const jsonPath = path.join(dir, "cw.json");
    const md = path.join(dir, "cw.md");
    await persistCrosswalk(jsonPath, md, merged);
    const parsed = JSON.parse(await readFile(jsonPath, "utf8"));
    expect(parsed.find((e: { obj_id: string }) => e.obj_id === "P-10").verdict).toBe("weaker-in-Lean");
    const rendered = renderCrosswalkMd(merged);
    expect(rendered).toContain("P-10");
    expect(rendered).toContain("triangularClass");
    expect(rendered).toContain("weaker-in-Lean");
  });
});
