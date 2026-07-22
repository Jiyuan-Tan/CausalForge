import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  parseLatexRefinement,
  requiresIndividualStatementAudit,
  runStatementAudit,
} from "../src/presentation/audit.js";
import { FormalLayerSource, hashBody } from "../src/presentation/formal_layer.js";
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
    body_hash: hashBody(BODY),
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

  it("refines, persists the best body to formal_layer.json, and returns one problem on residual drift", async () => {
    mode = "drift";
    const problems = await runStatementAudit(makeIO());
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "equivalence" });
    expect(problems[0].detail).toContain("thm1");

    // The refiner's best attempt is persisted (body + re-hashed) even though it never reconciled.
    const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layer.blocks[0].body).toBe("The refined claim holds under (h : True).");
    expect(layer.blocks[0].body_hash).toBe(hashBody("The refined claim holds under (h : True)."));

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
