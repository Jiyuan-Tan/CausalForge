import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, readFile, rm, symlink } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  parseLatexRefinement,
  resolveLeanDeclaration,
  requiresIndividualStatementAudit,
  runStatementAudit,
} from "../src/presentation/audit.js";
import { FormalLayerSource } from "../src/presentation/formal_layer.js";
import type { StageIO } from "../src/presentation/pipeline.js";

/**
 * Mechanical-layer test for the P1 statement equivalence audit (runStatementAudit). It sources the
 * frozen env body from formal_layer.json, resolves the Lean via the crosswalk decl (a tiny real Lean
 * file), audits with a STUB codex, refines drift, and persists the best body back to formal_layer.json.
 * Covers the faithful path (no change, [] returned) and the residual-drift path (best attempt persisted,
 * one problem returned). The faithful-REFINE graph-write path is exercised by the proof-audit test's
 * shared refine kernel; here we avoid the full GraphSchema fixture by keeping drift unreconciled.
 */

const BODY = "The claim holds.";
let mode: "faithful" | "drift" = "faithful";

const stubRunCodex = async ({ prompt }: { prompt: string }) => {
  if (prompt.includes("refined_body")) {
    return { stdout: JSON.stringify({ refined_body: "The refined claim holds under (h : True).", changed: true, note: "added hypothesis" }), stderr: "" };
  }
  const verdict = mode === "drift" ? "drift" : "faithful";
  return { stdout: JSON.stringify({ obj_id: "thm1", verdict, detail: verdict === "drift" ? "omits the hypothesis h" : "" }), stderr: "" };
};

let dir: string;

function makeIO(): StageIO {
  return {
    outDir: dir,
    ctx: {
      repoRoot: dir,
      qid: "q",
      spec: "v1",
      deps: { runCodex: stubRunCodex, runClaude: async () => "", dryRun: false },
    },
    bank: {
      leanSubdir: "Lean",
      noteMd: "",
      graph: { nodes: [], edges: [] },
      crosswalk: [
        { obj_id: "thm1", kind: "theorem", title: "T", tex: null, lean: { file: "X.lean", decl: "thm1", decl_kind: "theorem", line: 1 }, verdict: "ok" },
      ],
    },
    state: { notes: [] },
  } as unknown as StageIO;
}

beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "stmtaudit-"));
  await mkdir(join(dir, "Lean"), { recursive: true });
  await writeFile(join(dir, "Lean", "X.lean"), "theorem thm1 (h : True) : True := trivial\n", "utf8");
  await writeFile(join(dir, "outline.md"), "# Title\n**Test.**\n\n# Notation\n- \\(x\\): a thing\n\n# Sections\n## section: Body\n", "utf8");
  const block = {
    obj_id: "thm1",
    alias: "T-1",
    kind: "theorem" as const,
    env: "theoremv" as const,
    title: null,
    body: BODY,
    ref_set: [],
    lean: { decl: "thm1", file: "X.lean" },
    status: "ok",
    provenance: "from-note",
  };
  await writeFile(
    join(dir, "formal_layer.json"),
    JSON.stringify(FormalLayerSource.parse({ commit: null, blocks: [block] }), null, 2) + "\n",
    "utf8",
  );
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("runStatementAudit (P1 statement equivalence)", () => {
  it("relocates a re-exported declaration through the authoritative library index", async () => {
    await mkdir(join(dir, "doc"), { recursive: true });
    await mkdir(join(dir, "Causalean", "Stat"), { recursive: true });
    await writeFile(join(dir, "Lean", "X.lean"), "import Causalean.Stat.Real\nnamespace Paper.Namespace\nexport Causalean.Stat (target_decl)\nend Paper.Namespace\n", "utf8");
    await writeFile(join(dir, "Causalean", "Stat", "Real.lean"), "namespace Causalean.Stat\nlemma target_decl : True := trivial\nend Causalean.Stat\n", "utf8");
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({
      entries: [{ name: "Causalean.Stat.target_decl", file: "Causalean/Stat/Real.lean", line: 2 }],
    }), "utf8");
    const resolved = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.Namespace.target_decl", line: 2,
    });
    expect(resolved).toMatchObject({
      file: "Causalean/Stat/Real.lean", decl: "Causalean.Stat.target_decl",
      line: 2, relocated: true, resolution: "library-index",
    });
    expect(resolved.snippet).toContain("lemma target_decl : True");
  });

  it("does not mistake a same-leaf local helper for an explicitly re-exported declaration", async () => {
    await mkdir(join(dir, "doc"), { recursive: true });
    await mkdir(join(dir, "Causalean", "Stat"), { recursive: true });
    await writeFile(
      join(dir, "Lean", "X.lean"),
      "import Causalean.Stat.Real\nlemma target_decl : False := by contradiction\nnamespace Paper.Namespace\nexport Causalean.Stat (target_decl)\nend Paper.Namespace\n",
      "utf8",
    );
    await writeFile(join(dir, "Causalean", "Stat", "Real.lean"), "namespace Causalean.Stat\nlemma target_decl : True := trivial\nend Causalean.Stat\n", "utf8");
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({
      entries: [{ name: "Causalean.Stat.target_decl", file: "Causalean/Stat/Real.lean", line: 2 }],
    }), "utf8");
    const resolved = await resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.Namespace.target_decl", line: 2,
    });
    expect(resolved).toMatchObject({
      file: "Causalean/Stat/Real.lean", decl: "Causalean.Stat.target_decl", resolution: "library-index",
    });
    expect(resolved.snippet).toContain(": True");
    expect(resolved.snippet).not.toContain(": False");
  });

  it("fails closed when a re-export target is ambiguous or missing", async () => {
    await mkdir(join(dir, "doc"), { recursive: true });
    await mkdir(join(dir, "Causalean", "A"), { recursive: true });
    await mkdir(join(dir, "Causalean", "B"), { recursive: true });
    await writeFile(join(dir, "Lean", "X.lean"), "-- thin barrel\n", "utf8");
    await writeFile(join(dir, "Lean", "X.lean"), "import A.One\nnamespace Paper\nexport Exact.Ns (target_decl)\nend Paper\n", "utf8");
    await writeFile(join(dir, "Causalean", "A", "One.lean"), "namespace Exact.Ns\nlemma target_decl : True := trivial\nend Exact.Ns\n", "utf8");
    await writeFile(join(dir, "Causalean", "B", "Two.lean"), "namespace Exact.Ns\nlemma target_decl : True := trivial\nend Exact.Ns\n", "utf8");
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({ entries: [
      { name: "Exact.Ns.target_decl", file: "Causalean/A/One.lean", line: 2 },
      { name: "Exact.Ns.target_decl", file: "Causalean/B/Two.lean", line: 2 },
    ] }), "utf8");
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.target_decl", line: 1,
    })).rejects.toThrow(/ambiguous/);
    await writeFile(join(dir, "doc", "library_index.json"), JSON.stringify({ entries: [] }), "utf8");
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Paper.missing_decl", line: 1,
    })).rejects.toThrow(/no unique authoritative source/);
  });

  it("resolves the real PRESENT sibling topology and canonicalizes workspace-relative paths", async () => {
    const workspace = await mkdtemp(join(tmpdir(), "present-siblings-"));
    try {
      const packageRoot = join(workspace, "CausalSmith");
      await mkdir(join(packageRoot, "Run", "Helpers"), { recursive: true });
      await mkdir(join(workspace, "Causalean", "Stat"), { recursive: true });
      await mkdir(join(workspace, "doc"), { recursive: true });
      await writeFile(join(packageRoot, "Run", "Helpers", "Barrel.lean"), String.raw`
import Causalean.Stat.Real
/- export Wrong.Ns (target_decl) -/
namespace Paper.Ns
export
  Causalean.Stat
  ( target_decl )
end Paper.Ns
`, "utf8");
      await writeFile(join(workspace, "Causalean", "Stat", "Real.lean"), "namespace Causalean.Stat\nlemma target_decl : True := trivial\nend Causalean.Stat\n", "utf8");
      await writeFile(join(workspace, "doc", "library_index.json"), JSON.stringify({ entries: [
        { name: "Causalean.Stat.target_decl", file: "Causalean/Stat/Real.lean", line: 2 },
      ] }), "utf8");
      const hit = await resolveLeanDeclaration(packageRoot, "Run", {
        file: "Helpers/Barrel.lean", decl: "Paper.Ns.target_decl", line: 1,
      });
      expect(hit).toMatchObject({
        file: "Causalean/Stat/Real.lean", decl: "Causalean.Stat.target_decl", resolution: "library-index",
      });
    } finally { await rm(workspace, { recursive: true, force: true }); }
  });

  it("authenticates the alias namespace in a DirectProduct-style barrel", async () => {
    const workspace = await mkdtemp(join(tmpdir(), "present-alias-auth-"));
    try {
      const packageRoot = join(workspace, "CausalSmith");
      await mkdir(join(packageRoot, "Run", "Helpers"), { recursive: true });
      await mkdir(join(workspace, "Causalean", "Stat"), { recursive: true });
      await mkdir(join(workspace, "doc"), { recursive: true });
      await writeFile(join(packageRoot, "Run", "Helpers", "DirectProduct.lean"), `import Causalean.Stat.Real
namespace CausalSmith.Stat.BddUniformLogPenalty
export Causalean.Stat (coordinatewise_overlap_direct_product)
end CausalSmith.Stat.BddUniformLogPenalty
`, "utf8");
      await writeFile(join(workspace, "Causalean", "Stat", "Real.lean"), `namespace Causalean.Stat
lemma coordinatewise_overlap_direct_product : True := trivial
end Causalean.Stat
`, "utf8");
      await writeFile(join(workspace, "doc", "library_index.json"), JSON.stringify({ entries: [{
        name: "Causalean.Stat.coordinatewise_overlap_direct_product",
        file: "Causalean/Stat/Real.lean", line: 2,
      }] }), "utf8");
      await expect(resolveLeanDeclaration(packageRoot, "Run", {
        file: "Helpers/DirectProduct.lean", decl: "Totally.Wrong.coordinatewise_overlap_direct_product", line: 3,
      })).rejects.toThrow(/alias namespace mismatch/);
      const hit = await resolveLeanDeclaration(packageRoot, "Run", {
        file: "Helpers/DirectProduct.lean",
        decl: "CausalSmith.Stat.BddUniformLogPenalty.coordinatewise_overlap_direct_product", line: 3,
      });
      expect(hit.decl).toBe("Causalean.Stat.coordinatewise_overlap_direct_product");
    } finally { await rm(workspace, { recursive: true, force: true }); }
  });

  it("rejects wrong namespaces, traversal, and symlink escapes", async () => {
    await writeFile(join(dir, "Lean", "X.lean"), "namespace Wrong.Ns\nlemma target_decl : True := trivial\nend Wrong.Ns\n", "utf8");
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "X.lean", decl: "Right.Ns.target_decl", line: 2,
    })).rejects.toThrow(/no exact declaration body/);
    await expect(resolveLeanDeclaration(dir, "Lean", {
      file: "../outside.lean", decl: "X.y", line: 1,
    })).rejects.toThrow(/traversing/);
    const outside = await mkdtemp(join(tmpdir(), "present-outside-"));
    try {
      await writeFile(join(outside, "Escape.lean"), "lemma escaped : True := trivial\n", "utf8");
      await symlink(join(outside, "Escape.lean"), join(dir, "Lean", "Escape.lean"));
      await expect(resolveLeanDeclaration(dir, "Lean", {
        file: "Escape.lean", decl: "escaped", line: 1,
      })).rejects.toThrow(/escapes workspace/);
    } finally { await rm(outside, { recursive: true, force: true }); }
  });

  it("rejects a recorded run-file symlink into the allowed sibling Causalean tree", async () => {
    const workspace = await mkdtemp(join(tmpdir(), "present-run-symlink-"));
    try {
      const packageRoot = join(workspace, "CausalSmith");
      await mkdir(join(packageRoot, "Run"), { recursive: true });
      await mkdir(join(workspace, "Causalean", "Stat"), { recursive: true });
      await writeFile(join(workspace, "Causalean", "Stat", "Escape.lean"),
        "namespace Causalean.Stat\nlemma escaped : True := trivial\nend Causalean.Stat\n", "utf8");
      await symlink(join(workspace, "Causalean", "Stat", "Escape.lean"), join(packageRoot, "Run", "Escape.lean"));
      await expect(resolveLeanDeclaration(packageRoot, "Run", {
        file: "Escape.lean", decl: "Causalean.Stat.escaped", line: 2,
      })).rejects.toThrow(/symlink escapes run root/);
    } finally { await rm(workspace, { recursive: true, force: true }); }
  });

  it("routes algorithmic and operation-count claims to individual audits", () => {
    expect(requiresIndividualStatementAudit("The estimator is computable in O(dM^4) operations.")).toBe(true);
    expect(requiresIndividualStatementAudit("The estimator equals the displayed clamped sum.")).toBe(false);
  });
  it("recovers a refinement whose JSON contains raw LaTeX escapes", () => {
    const raw = String.raw`{"refined_body":"For fixed \(T\), define \\[\Phi:=MA.\\]","changed":true,"note":"tightened"}`.replaceAll('\\"', '"');
    expect(parseLatexRefinement(raw, "refined_body")).toEqual({
      body: "For fixed \\(T\\), define \\[\\Phi:=MA.\\]",
      changed: true,
      note: "tightened",
    });
  });

  it("returns no problems and caches a faithful verdict when the body matches Lean", async () => {
    mode = "faithful";
    const problems = await runStatementAudit(makeIO());
    expect(problems).toEqual([]);
    const cache = JSON.parse(await readFile(join(dir, "equivalence_cache.json"), "utf8"));
    expect(cache.thm1.verdict).toBe("faithful");
    // formal_layer.json body is unchanged (no refinement).
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layer.blocks[0].body).toBe(BODY);
  });

  it("fails instead of silently treating a formal bank object as note-only", async () => {
    const io = makeIO();
    io.bank.crosswalk[0].lean = null;
    io.bank.crosswalk[0].kind = "assumption";
    (io.ctx.deps as any).runCodex = async ({ prompt }: { prompt: string }) => {
      if (prompt.includes("components")) return { stdout: JSON.stringify({ components: [] }), stderr: "" };
      return { stdout: JSON.stringify({ obj_id: "thm1", verdict: "faithful" }), stderr: "" };
    };
    await expect(runStatementAudit(io)).rejects.toThrow(/neither a resolved Lean declaration nor nonempty resolved components/);
  });

  it("refines, persists the best body to formal_layer.json, and returns one problem on residual drift", async () => {
    mode = "drift";
    const problems = await runStatementAudit(makeIO());
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "equivalence" });
    expect(problems[0].detail).toContain("thm1");

    // The refiner's best attempt is persisted (body + re-hashed) even though it never reconciled.
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layer.blocks[0].body).toBe("The refined claim holds under (h : True).");
    expect(layer.blocks[0].body).toBe("The refined claim holds under (h : True).");

    // The derived .tex view is re-emitted and a drift report is written.
    const tex = await readFile(join(dir, "formal_layer.tex"), "utf8");
    expect(tex).toContain("The refined claim holds under (h : True).");
    const drift = await readFile(join(dir, "logs", "graph_nl_drift.md"), "utf8");
    expect(drift).toContain("thm1");
    // Still-drifting body is cached as drift (re-audited on a rerun, not skipped).
    const cache = JSON.parse(await readFile(join(dir, "equivalence_cache.json"), "utf8"));
    expect(cache.thm1.verdict).toBe("drift");
  });
});
