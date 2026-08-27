import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { proofAuditCacheKey, proofAuditSemanticNotation, runProofAudit } from "../src/presentation/audit.js";
import type { StageIO } from "../src/presentation/pipeline.js";

/**
 * Mechanical-layer test for the P2 proof equivalence audit (runProofAudit). Drives the full
 * audit → refine → persist → halt machinery with a STUB codex: the verdict is keyed on whether the
 * proof body already says "REFINED", so the loop is exercised statelessly (no real Lean / codex).
 *   • thm_ok  — audit faithful first time              → unchanged, no problem
 *   • thm_fix — unfaithful, then faithful after refine  → file rewritten, no problem
 *   • thm_bad — unfaithful even after refine            → best attempt persisted, one problem
 */

import { canonicalizeProofTitle } from "../src/presentation/stages/p2_draft.js";

describe("canonicalizeProofTitle", () => {
  it("rewrites free-form, prefixless, and missing titles to the canonical attributable form", () => {
    const canon = "\\begin{proof}[Proof of \\cref{obj:lem:x}]body\\end{proof}";
    expect(canonicalizeProofTitle("lem:x", "\\begin{proof}body\\end{proof}")).toBe(canon);
    expect(canonicalizeProofTitle("lem:x", "\\begin{proof}[Free-form title]body\\end{proof}")).toBe(canon);
    expect(canonicalizeProofTitle("lem:x", "\\begin{proof}[Proof of \\cref{lem:x}]body\\end{proof}")).toBe(canon);
    expect(canonicalizeProofTitle("lem:x", canon)).toBe(canon); // idempotent
  });
});

function proofBody(id: string, refined = false): string {
  // Refined proofs are persisted with the CANONICAL title (the refiner may rewrite
  // or drop it, making the proof unattributable and invisible to the placement lint).
  const title = refined ? `[Proof of \\cref{obj:${id}}]` : "";
  return `\\begin{proof}${title}${refined ? "REFINED" : "draft"} proof of ${id}\\end{proof}`;
}

// Stub runCodex: routes by the prompt's output-format marker (refine prompt asks for "refined_proof";
// audit prompt asks for "verdict"), and identifies the target by the obj_id embedded in the prompt.
const stubRunCodex = async ({ prompt }: { prompt: string }) => {
  const id = ["thm_ok", "thm_fix", "thm_bad"].find((x) => prompt.includes(x))!;
  if (prompt.includes("refined_proof")) {
    return { stdout: JSON.stringify({ refined_proof: proofBody(id, true), changed: true, note: "tightened" }), stderr: "" };
  }
  // audit: thm_bad is always unfaithful; thm_fix is unfaithful until its body is the REFINED one.
  const faithful = id === "thm_ok" || (id === "thm_fix" && prompt.includes("REFINED"));
  return {
    stdout: JSON.stringify({ theorem: id, verdict: faithful ? "faithful" : "unfaithful", issues: faithful ? [] : ["step 2 mismatch"] }),
    stderr: "",
  };
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
    bank: { leanSubdir: "Lean" },
    state: { notes: [] },
  } as unknown as StageIO;
}

const targets = [
  { obj_id: "thm_ok", isMain: true, lean: { file: "X.lean", decl: "thm_ok" } },
  { obj_id: "thm_fix", isMain: true, lean: { file: "X.lean", decl: "thm_fix" } },
  { obj_id: "thm_bad", isMain: false, lean: { file: "X.lean", decl: "thm_bad" } },
];

beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "proofaudit-"));
  await mkdir(join(dir, "proofs"), { recursive: true });
  await mkdir(join(dir, "Lean"), { recursive: true });
  await writeFile(join(dir, "Lean", "X.lean"), targets.map((t) => `theorem ${t.obj_id} : True := by\n  trivial`).join("\n\n"), "utf8");
  await writeFile(join(dir, "outline.md"), "# Title\n**Test.**\n\n# Notation\n- \\(x\\): a thing\n\n# Sections\n## section: Body\n", "utf8");
  for (const t of targets) await writeFile(join(dir, "proofs", `${t.obj_id}.tex`), proofBody(t.obj_id) + "\n", "utf8");
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("runProofAudit (P2 proof equivalence)", () => {
  it("returns a refined map for every proof and one problem for the residual-unfaithful proof", async () => {
    const { refined, problems } = await runProofAudit(makeIO(), targets);

    // Every target appears in the refined map.
    expect([...refined.keys()].sort()).toEqual(["thm_bad", "thm_fix", "thm_ok"]);

    // Only thm_bad remains unfaithful → exactly one proof-audit problem.
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "proof-audit" });
    expect(problems[0].detail).toContain("thm_bad");
  });

  it("leaves a faithful proof untouched and rewrites a refined one on disk", async () => {
    const { refined } = await runProofAudit(makeIO(), targets);

    // thm_ok was faithful first pass → disk untouched; the returned map carries the
    // canonically-titled view (what P2 assembly uses).
    expect(refined.get("thm_ok")).toBe(canonicalizeProofTitle("thm_ok", proofBody("thm_ok")));
    expect(await readFile(join(dir, "proofs", "thm_ok.tex"), "utf8")).toBe(proofBody("thm_ok") + "\n");

    // thm_fix was refined → both the returned body and the persisted file carry the REFINED proof.
    expect(refined.get("thm_fix")).toBe(proofBody("thm_fix", true));
    expect(await readFile(join(dir, "proofs", "thm_fix.tex"), "utf8")).toBe(proofBody("thm_fix", true) + "\n");
  });

  it("persists the best attempt for the unfaithful proof and writes a drift report", async () => {
    await runProofAudit(makeIO(), targets);
    // thm_bad's best (REFINED) attempt is persisted even though it never reconciled.
    expect(await readFile(join(dir, "proofs", "thm_bad.tex"), "utf8")).toBe(proofBody("thm_bad", true) + "\n");
    const drift = await readFile(join(dir, "logs", "graph_nl_drift.md"), "utf8");
    expect(drift).toContain("thm_bad (proof)");
  });

  it("records a faithful/unfaithful verdict cache and a review line per proof", async () => {
    await runProofAudit(makeIO(), targets);
    const cache = JSON.parse(await readFile(join(dir, "proof_audit_cache.json"), "utf8"));
    expect(cache.thm_ok.verdict).toBe("faithful");
    const reviews = (await readFile(join(dir, "logs", "reviews.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    const refineLines = reviews.filter((r) => r.kind === "proof-refine");
    expect(refineLines.map((r) => r.obj_id).sort()).toEqual(["thm_bad", "thm_fix", "thm_ok"]);
  });
});

describe("proof-audit semantic notation fingerprint", () => {
  const row = (label: string, symbol: string, meaning: string, home: string) =>
    `| ${label} | ${symbol} | ${meaning} | ${home} |`;
  const table = (rows: string[]) => [
    "metadata: deliberately excluded from proof semantics",
    "| note symbol | paper notation | defining property in one phrase | home |",
    "|---|---|---|---|",
    ...rows,
  ].join("\n");
  const key = (notationTable: string) => proofAuditCacheKey({
    proofTex: "proof", leanPointer: "pointer", leanProofCacheSource: "source", notationTable, auditPromptFp: "fp", targetStatement: "stmt",
  });

  it("is invariant to notation row order, home ownership, and non-table placement metadata", () => {
    const a = table([
      row("radius", "\\(w=A\\Delta^{1/q}\\)", "hypercube radius", "lem:old"),
      row("mass", "\\(m_n\\)", "common cell mass", "lem:packing"),
    ]);
    const b = table([
      row("mass", "\\(m_n\\)", "common cell mass", "thm:new-home"),
      row("radius", "\\(w=A\\Delta^{1/q}\\)", "hypercube radius", "thm:new-home"),
    ]).replace("metadata: deliberately excluded", "env_overrides: changed placement");
    expect(proofAuditSemanticNotation(a)).toBe(proofAuditSemanticNotation(b));
    expect(key(a)).toBe(key(b));
  });

  it("changes when exact symbol spelling or parameterization changes", () => {
    const base = table([row("radius", "\\(w=A\\Delta^{1/q}\\)", "hypercube radius", "lem:x")]);
    const spelling = table([row("radius", "\\(w_n=A\\Delta^{1/q}\\)", "hypercube radius", "lem:x")]);
    const parameters = table([row("radius", "\\(w=A\\Delta^{1/p}\\)", "hypercube radius", "lem:x")]);
    expect(key(spelling)).not.toBe(key(base));
    expect(key(parameters)).not.toBe(key(base));
  });

  it("changes when a symbol's reader-facing meaning changes", () => {
    const base = table([row("radius", "\\(w\\)", "hypercube radius", "lem:x")]);
    const changed = table([row("radius", "\\(w\\)", "cell probability", "lem:x")]);
    expect(key(changed)).not.toBe(key(base));
    expect(key(table([]))).not.toBe(key(base));
    expect(key(table([
      row("radius", "\\(w\\)", "hypercube radius", "lem:x"),
      row("mass", "\\(m\\)", "cell probability", "lem:x"),
    ]))).not.toBe(key(base));
  });

});

import { missingRealizedCitations } from "../src/presentation/audit.js";

describe("missingRealizedCitations (deterministic missing-citation check)", () => {
  const citables = [
    { objId: "lem:ambient-sample-marginal", decl: "CausalSmith.Stat.X.finProductLaw_eq_map" },
    { objId: "lem:pilot-sandwich", decl: "CausalSmith.Stat.X.pilot_sandwich" },
  ];

  it("flags a directly invoked realized decl the proof never crefs", () => {
    const lean = "theorem t : True := by\n  rw [productLaw, ← finProductLaw_eq_map (obsLaw P) n]\n  trivial";
    const tex = "\\begin{proof}[Proof of \\cref{obj:thm:t}] Direct argument. \\end{proof}";
    expect(missingRealizedCitations(lean, tex, citables, "thm:t")).toEqual([citables[0]]);
  });

  it("is satisfied by an existing \\cref and ignores the result's own env", () => {
    const lean = "theorem t := by exact finProductLaw_eq_map.trans (pilot_sandwich h)";
    const tex = "By \\cref{obj:lem:ambient-sample-marginal} and \\cref{obj:lem:pilot-sandwich}, done.";
    expect(missingRealizedCitations(lean, tex, citables, "thm:t")).toEqual([]);
    // A lemma auditing its own proof never demands a self-citation.
    expect(
      missingRealizedCitations("lemma l := finProductLaw_eq_map", "no crefs", citables, "lem:ambient-sample-marginal"),
    ).toEqual([]);
  });

  it("matches whole identifiers only, and stays silent without a Lean source", () => {
    // `finProductLaw_eq_map'` and `myfinProductLaw_eq_map` are different declarations.
    const lean = "theorem t := by exact finProductLaw_eq_map' (myfinProductLaw_eq_map h)";
    expect(missingRealizedCitations(lean, "no crefs", citables, "thm:t")).toEqual([]);
    expect(missingRealizedCitations("", "no crefs", citables, "thm:t")).toEqual([]);
  });
});

import { droppedLeanRoutes } from "../src/presentation/audit.js";

describe("droppedLeanRoutes multi-marker lines", () => {
  it("parses several % lean: markers on one line as separate routes, so a well-formed rewrite is not discarded", () => {
    const before = "Step 1. % lean: feasibleMaximizer_mem % lean: feasibleMaximizer_value\n";
    const after = "Step 1a. % lean: feasibleMaximizer_mem\nStep 1b. % lean: feasibleMaximizer_value\n";
    expect(droppedLeanRoutes(before, after)).toEqual([]);
    // A genuinely dropped route on a multi-marker line is still caught.
    expect(droppedLeanRoutes(before, "Step 1. % lean: feasibleMaximizer_mem\n")).toEqual([
      "feasibleMaximizer_value",
    ]);
  });
});

describe("proof-audit adjudication channel (flip verdict, keep key — the documented operator flow)", () => {
  // Integration regression for 32fe2964: the deterministic missing-citation hint used to
  // override a cached faithful verdict on EVERY hit, so the skill-documented adjudication
  // channel was silently defeated and the halt was unescapable (observed live 2026-08-26,
  // ~2.5h of cycles). Fixture: thm_adj's Lean proof invokes the citable lemma decl
  // `help_bound`; its paper proof does not cite \cref{obj:lem_help}, so the hint fires on
  // every pass.
  it("honors an adjudicated faithful verdict on an unchanged proof: no dispatch, hint suppressed with a note", async () => {
    await writeFile(
      join(dir, "Lean", "Y.lean"),
      ["theorem help_bound : True := by trivial", "", "theorem thm_adj : True := by", "  have h := help_bound", "  trivial", ""].join("\n"),
      "utf8",
    );
    const proofBody = "\\begin{proof}[Proof of \\cref{obj:thm_adj}]No citation here.\\end{proof}";
    await writeFile(join(dir, "proofs", "thm_adj.tex"), proofBody + "\n", "utf8");
    await writeFile(
      join(dir, "formal_layer.json"),
      JSON.stringify({
        blocks: [
          { obj_id: "thm_adj", env: "theoremv", title: null, body: "Target statement." },
          { obj_id: "lem_help", env: "lemmav", title: null, body: "Helper statement." },
        ],
      }),
      "utf8",
    );
    let codexCalls = 0;
    const countingCodex = async ({ prompt }: { prompt: string }) => {
      codexCalls++;
      if (prompt.includes("refined_proof")) {
        return { stdout: JSON.stringify({ refined_proof: proofBody, changed: false, note: "" }), stderr: "" };
      }
      return { stdout: JSON.stringify({ theorem: "thm_adj", verdict: "unfaithful", issues: ["codex disagrees"] }), stderr: "" };
    };
    const adjIO = () =>
      ({
        outDir: dir,
        ctx: { repoRoot: dir, qid: "q", spec: "v1", deps: { runCodex: countingCodex, runClaude: async () => "", dryRun: false } },
        bank: { leanSubdir: "Lean", graph: { nodes: [{ id: "lem_help", lean: { decl_name: "help_bound" } }] } },
        state: { notes: [] },
      }) as unknown as StageIO;
    const adjTargets = [{ obj_id: "thm_adj", isMain: true, lean: { file: "Y.lean", decl: "thm_adj" } }];

    // Pass 1: codex judges unfaithful and the refine loop does not converge → one problem,
    // cached codex verdict `unfaithful`.
    const r1 = await runProofAudit(adjIO(), adjTargets);
    expect(r1.problems.length).toBeGreaterThan(0);
    const cachePath = join(dir, "proof_audit_cache.json");
    const cache = JSON.parse(await readFile(cachePath, "utf8"));
    expect(cache.thm_adj.verdict).toBe("unfaithful");
    expect(codexCalls).toBeGreaterThan(0);

    // Operator adjudication exactly as the skill prescribes: flip `verdict`, keep `key`.
    cache.thm_adj.verdict = "faithful";
    await writeFile(cachePath, JSON.stringify(cache), "utf8");

    // Pass 2, inputs unchanged: the key must be STABLE across runs, the hit must be honored
    // with ZERO model dispatches even though the missing-citation hint still fires, and the
    // suppression must be recorded — never silent.
    codexCalls = 0;
    const io2 = adjIO();
    const r2 = await runProofAudit(io2, adjTargets);
    expect(r2.problems).toEqual([]);
    expect(codexCalls).toBe(0);
    expect((io2 as unknown as { state: { notes: string[] } }).state.notes.join("\n")).toMatch(
      /thm_adj.*missing-citation hint\(s\) suppressed by its cached faithful verdict/,
    );
  });
});
