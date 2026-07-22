import { afterAll, beforeAll, describe, it, expect } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addAssumption, setLean } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";
import { runReviewer, gradeReviewerOutput, parseJsonObject } from "../../src/formalization/proof_reviewer.js";
import { planPath } from "../../src/paths.js";
import { auditCitedReview } from "../../src/formalization/delivery_audit.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";

function fixture() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = addAssumption(g, { node: "t1", id: "a2", statement: "the hard rate bound", tier: 2, classification: "regularity-bookkeeping", anchor: "", provenance: "agent-introduced" });
  g = setLean(g, "a2", "a2_assumption", "T1.lean");
  return g;
}

const codexStub = (out: object) => ({
  runCodex: async () => ({ stdout: JSON.stringify(out), stderr: "" }),
});
// repoRoot is set to a real writable tmpdir in beforeAll below: the reviewer now
// dispatches through the framework boundary (dispatchAgent/dispatchClaudeAgent),
// which appends a dispatch/dispatch-complete pair to <repoRoot>/.../pipeline.jsonl
// before/after each call — an unwritable fake root like "/repo" trips EACCES on that mkdir.
let ctx = { repoRoot: "/repo", qid: "q", specialization: "v1" };
const minimalCore = (symbols: unknown[] = []) => ({
  qid: "q",
  specialization: "v1",
  symbols,
  assumptions: [],
  definitions: [],
  statements: [],
  target_estimand: "test estimand",
  bibliography: [],
});
let sharedCoreRoot = "";
let sharedCorePath = "";
const sharedPromptPath = join(process.cwd(), "src/formalization/prompts/F4/proof_reviewer.txt");

beforeAll(async () => {
  sharedCoreRoot = await mkdtemp(join(tmpdir(), "proof-reviewer-core-"));
  sharedCorePath = join(sharedCoreRoot, "core.json");
  await writeFile(sharedCorePath, JSON.stringify(minimalCore()));
  await writeFile(join(sharedCoreRoot, "T1.lean"), [
    "theorem t1_thm : True := by trivial",
    "def a2_assumption : Prop := True",
    "lemma l1_lemma : True := by trivial",
    "def d1_def : Prop := True",
  ].join("\n"));
  ctx = { repoRoot: sharedCoreRoot, qid: "q", specialization: "v1" };
});

afterAll(async () => {
  await rm(sharedCoreRoot, { recursive: true, force: true });
});

describe("runReviewer", () => {
  it("writes matched/drift back and reports a content-gate as blocking", async () => {
    const g = fixture();
    const r = await runReviewer({
      ctx,
      deps: codexStub({
        status: "flagged",
        statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "ok" }],
        assumption_verdicts: [{ obj_id: "A-2", verdict: "content-gate", note: "this is the crux, assumed" }],
        substrate_gates: [],
        escalate: null,
      }),
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: ["t1", "a2"],
      hashes: { t1: "h1", a2: "h2" },
      mode: "delta",
      corePath: sharedCorePath,
      promptPath: sharedPromptPath,
      leanDir: sharedCoreRoot,
    });
    expect(r.graph.nodes.find((n) => n.id === "t1")!.review.status).toBe("matched");
    expect(r.graph.nodes.find((n) => n.id === "a2")!.review.status).toBe("drift"); // content-gate → drift
    expect(r.ok).toBe(false);
    expect(r.blocking).toContain("A-2");
  });

  it("ok when everything matched/faithful", async () => {
    const g = fixture();
    const r = await runReviewer({
      ctx,
      deps: codexStub({
        status: "ok",
        statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "" }],
        assumption_verdicts: [{ obj_id: "A-2", verdict: "regularity-bookkeeping", note: "" }],
        substrate_gates: [],
        escalate: null,
      }),
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: ["t1", "a2"],
      hashes: { t1: "h1", a2: "h2" },
      mode: "delta",
      corePath: sharedCorePath,
      promptPath: sharedPromptPath,
      leanDir: sharedCoreRoot,
    });
    expect(r.ok).toBe(true);
    expect(r.graph.nodes.find((n) => n.id === "a2")!.review.status).toBe("matched");
  });

  it("dispatches ONE focused codex call per target (P3-style per-item fan-out, not one batched call)", async () => {
    const g = fixture();
    const seen: string[] = [];
    const r = await runReviewer({
      ctx,
      deps: {
        runCodex: async ({ prompt }) => {
          // Per-item dispatch: each call must carry EXACTLY one target block (its `### <obj_id> (` header) —
          // never both. A single batched call (the old behavior) would contain both T-1 and A-2.
          const hasT1 = prompt.includes("### T-1 (");
          const hasA2 = prompt.includes("### A-2 (");
          expect([hasT1, hasA2].filter(Boolean)).toHaveLength(1);
          const id = hasT1 ? "T-1" : "A-2";
          seen.push(id);
          const out =
            id === "A-2"
              ? { statement_verdicts: [], assumption_verdicts: [{ obj_id: "A-2", verdict: "content-gate", note: "crux" }], escalate: null }
              : { statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "ok" }], assumption_verdicts: [], escalate: null };
          return { stdout: JSON.stringify(out), stderr: "" };
        },
      },
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: ["t1", "a2"],
      hashes: { t1: "h1", a2: "h2" },
      mode: "delta",
      corePath: sharedCorePath,
      promptPath: sharedPromptPath,
      leanDir: sharedCoreRoot,
    });
    expect(seen.sort()).toEqual(["A-2", "T-1"]); // exactly one call per target
    expect(r.graph.nodes.find((n) => n.id === "t1")!.review.status).toBe("matched");
    expect(r.graph.nodes.find((n) => n.id === "a2")!.review.status).toBe("drift");
    expect(r.blocking).toContain("A-2");
  });

  it("uses both reviewers for every F4 target, including routine lemmas", async () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "headline claim", tex_anchor: "" });
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "routine lemma", tex_anchor: "" });
    g = addNode(g, { id: "d1", kind: "definition", provenance: "from-note", nl_statement: "model-class definition", tex_anchor: "" });
    g = setLean(g, "t1", "t1_thm", "T1.lean");
    g = setLean(g, "l1", "l1_lemma", "T1.lean");
    g = setLean(g, "d1", "d1_def", "T1.lean");
    const claudePrompts: string[] = [];
    const matched = (prompt: string) => {
      const objId = prompt.match(/### ([^\s(]+) \(/)?.[1];
      return { stdout: JSON.stringify({ status: "ok", statement_verdicts: objId ? [{ obj_id: objId, verdict: "matched", note: "ok" }] : [], assumption_verdicts: [], substrate_gates: [], escalate: null }), stderr: "" };
    };

    await runReviewer({
      ctx,
      deps: {
        runCodex: async ({ prompt }) => matched(prompt),
        runClaude: async ({ prompt }) => {
          claudePrompts.push(prompt);
          return matched(prompt).stdout;
        },
      },
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: ["t1", "l1", "d1"],
      hashes: { t1: "h1", l1: "h2", d1: "h3" },
      mode: "convergence",
      corePath: sharedCorePath,
      promptPath: sharedPromptPath,
      leanDir: sharedCoreRoot,
    });

    expect(claudePrompts).toHaveLength(3);
    expect(claudePrompts.some((p) => p.includes("headline claim"))).toBe(true);
    expect(claudePrompts.some((p) => p.includes("model-class definition"))).toBe(true);
    expect(claudePrompts.some((p) => p.includes("routine lemma"))).toBe(true);
  });

  it("makes both F4 reviewers independently audit an undelivered node and fails if either rejects its secondary role", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-undelivered-"));
    const corePath = join(root, "core.json");
    await writeFile(corePath, JSON.stringify({
      qid: "q",
      specialization: "v1",
      tldr: "The headline is theorem t1; the atlas is not advertised as a principal result.",
      honest_scope: "The exact atlas is a secondary diagnostic and no delivered theorem uses it.",
      project_justification: { gap: "missing atlas audit", niche: "secondary diagnostic", fill: "Recover the causal arrow generically." },
      symbols: [],
      assumptions: [],
      definitions: [],
      // proof_tex is required for `proved`: a proved node with no proof renders as an
      // established result with nothing establishing it. Immaterial to what this test
      // exercises (F4 reviewers auditing an UNDELIVERED node's secondary role), but the
      // fixture must be a core the schema accepts.
      statements: [{ id: "thm:atlas", kind: "theorem", statement: "exact real atlas", depends_on: [], status: "proved", proof_tex: "Proof of the atlas." }],
      target_estimand: "causal arrow",
      bibliography: [],
    }));
    const localCtx = { repoRoot: root, qid: "q", specialization: "v1" };
    const pp = planPath(root, "q", "v1");
    await mkdir(join(pp, ".."), { recursive: true });
    await writeFile(pp, JSON.stringify({
      qid: "q",
      specialization: "v1",
      env: [],
      nodes: {
        "thm:atlas": {
          lean_kind: "theorem",
          lean_name: "exactRealAtlas",
          disposition: "define-local",
          delivery_role: "secondary",
          delivery_status: "undelivered",
          delivery_reason: "citation instantiation overflow",
        },
      },
      citations: [],
      feasibility: "formalizable-now",
    }));
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "thm:atlas", kind: "theorem", provenance: "from-note", nl_statement: "exact real atlas", tex_anchor: "" });
    g = {
      ...g,
      nodes: g.nodes.map((n) => n.id === "thm:atlas" ? {
        ...n,
        delivery: { status: "undelivered" as const, role: "secondary" as const, reason: "citation instantiation overflow" },
      } : n),
    };
    const prompts: string[] = [];

    try {
      const r = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async ({ prompt }) => {
            prompts.push(prompt);
            return { stdout: JSON.stringify({
              status: "ok",
              statement_verdicts: [{ obj_id: "thm:atlas", verdict: "matched", note: "secondary and unconsumed" }],
              assumption_verdicts: [], substrate_gates: [], escalate: null,
            }), stderr: "" };
          },
          runClaude: async ({ prompt }) => {
            prompts.push(prompt);
            return JSON.stringify({
              status: "flagged",
              statement_verdicts: [{ obj_id: "thm:atlas", verdict: "drift", note: "the core actually advertises it as headline" }],
              assumption_verdicts: [], substrate_gates: [],
              escalate: { kind: "delivery-role-conflict", obj_id: "thm:atlas", reason: "headline omission" },
            });
          },
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["thm:atlas"],
        hashes: {},
        mode: "convergence",
        corePath: corePath,
        promptPath: sharedPromptPath,
      });

      expect(prompts).toHaveLength(2);
      for (const prompt of prompts) {
        expect(prompt).toContain("undelivered-delivery-role audit");
        expect(prompt).toContain("DO NOT trust as the verdict");
        expect(prompt).toContain("DELIVERED REVERSE USES-CLOSURE");
        expect(prompt).toContain("The headline is theorem t1");
        expect(prompt).toContain("Recover the causal arrow generically");
      }
      expect(r.ok).toBe(false);
      expect(r.blocking).toContain("thm:atlas");
      expect(r.escalate?.kind).toBe("delivery-role-conflict");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("fails closed when either F4 peer omits the source-and-locator row for a delivered cited node", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-cited-"));
    const localCtx = { repoRoot: root, qid: "q", specialization: "v1" };
    const pp = planPath(root, "q", "v1");
    await mkdir(join(pp, ".."), { recursive: true });
    await writeFile(pp, JSON.stringify({
      qid: "q",
      specialization: "v1",
      env: [],
      nodes: {
        "gate:source": {
          lean_kind: "assumption",
          lean_name: "sourceInterface",
          disposition: "define-local",
          gate: true,
          gate_class: "cited",
          source: "cite:source",
        },
      },
      citations: [{
        id: "cite:source", title: "Source", authors: "A", year: 2020,
        locator: "Theorem 2", verbatim_statement: "For every x, P x.",
      }],
      feasibility: "formalizable-now",
    }));
    await writeFile(join(root, "Basic.lean"), "def sourceInterface : Prop := True\n");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "gate:source", kind: "gate", provenance: "from-note", nl_statement: "source interface", tex_anchor: "" });
    g = setLean(g, "gate:source", "sourceInterface", "Basic.lean");
    g.nodes[0].gate = { gate_class: "cited", source: "cite:source" };
    const faithful = [{ obj_id: "gate:source", verdict: "faithful-refinement", note: "matches" }];

    try {
      const result = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async () => ({ stdout: JSON.stringify({
            status: "ok",
            statement_verdicts: [], assumption_verdicts: faithful,
            substrate_gates: [{
              name: "sourceInterface", gate_class: "cited",
              source: { cite_id: "cite:source", locator: "Theorem 2" },
              check_status: "cited-verified-attested",
            }],
            escalate: null,
          }), stderr: "" }),
          runClaude: async () => JSON.stringify({
            status: "ok", statement_verdicts: [], assumption_verdicts: faithful,
            substrate_gates: [], escalate: null,
          }),
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["gate:source"],
        hashes: { "gate:source": "h" },
        mode: "convergence",
        leanDir: root,
        corePath: sharedCorePath,
        promptPath: sharedPromptPath,
      });

      expect(result.ok).toBe(false);
      expect(result.blocking).toContain("gate:source");
      expect(result.citedReviewReceipts).toHaveLength(2);
      expect(result.citedReviewReceipts?.find((receipt) => receipt.reviewer === "codex")?.check_status).toBe("cited-verified-attested");
      expect(result.citedReviewReceipts?.find((receipt) => receipt.reviewer === "claude")?.check_status).toBe("missing");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("binds successful cited receipts to the post-verdict graph accepted by F5", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-cited-current-"));
    const localCtx = { repoRoot: root, qid: "q", specialization: "v1" };
    const pp = planPath(root, "q", "v1");
    await mkdir(join(pp, ".."), { recursive: true });
    const planJson = {
      qid: "q", specialization: "v1", env: [],
      nodes: {
        "gate:source": {
          lean_kind: "assumption", lean_name: "sourceInterface", disposition: "define-local",
          gate: true, gate_class: "cited", source: "cite:source",
        },
      },
      citations: [{
        id: "cite:source", title: "Source", authors: "A", year: 2020,
        locator: "Theorem 2", verbatim_statement: "For every x, P x.",
      }],
      feasibility: "formalizable-now",
    };
    await writeFile(pp, JSON.stringify(planJson));
    await writeFile(join(root, "Basic.lean"), "def sourceInterface : Prop := True\n");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "gate:source", kind: "gate", provenance: "from-note", nl_statement: "source interface", tex_anchor: "" });
    g = setLean(g, "gate:source", "sourceInterface", "Basic.lean");
    g.nodes[0].gate = { gate_class: "cited", source: "cite:source" };
    const peerOutput = JSON.stringify({
      status: "ok",
      statement_verdicts: [],
      assumption_verdicts: [{ obj_id: "gate:source", verdict: "faithful-refinement", note: "matches" }],
      substrate_gates: [{
        name: "sourceInterface", gate_class: "cited",
        source: { cite_id: "cite:source", locator: "Theorem 2" },
        check_status: "cited-verified-attested",
      }],
      escalate: null,
    });

    try {
      const result = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async () => ({ stdout: peerOutput, stderr: "" }),
          runClaude: async () => peerOutput,
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["gate:source"],
        hashes: { "gate:source": "current-hash" },
        mode: "convergence",
        leanDir: root,
        corePath: sharedCorePath,
        promptPath: sharedPromptPath,
      });
      expect(result.ok).toBe(true);
      expect(result.graph.nodes[0].review.passed_hash).toBe("current-hash");
      const parsedPlan = PlanSchema.parse(JSON.parse(await readFile(pp, "utf8")));
      expect(auditCitedReview({
        plan: parsedPlan,
        graph: result.graph,
        receipts: result.citedReviewReceipts,
      })).toEqual([]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("requires both reviewers for an F4 symbol/tagging check", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-symbol-"));
    const corePath = join(root, "core.json");
    await writeFile(corePath, JSON.stringify(minimalCore([{ name: "sigma", type: "scale", space: "[0,∞)" }])));
    let codexCalls = 0;
    let claudeCalls = 0;

    try {
      await runReviewer({
        ctx,
        deps: {
          runCodex: async () => {
            codexCalls++;
            return { stdout: JSON.stringify({ status: "ok", statement_verdicts: [], assumption_verdicts: [], substrate_gates: [], escalate: null }), stderr: "" };
          },
          runClaude: async () => {
            claudeCalls++;
            return JSON.stringify({ status: "ok", statement_verdicts: [], assumption_verdicts: [], substrate_gates: [], escalate: null });
          },
        },
        graph: createEmptyGraph("q", "v1"),
        skeleton: [],
        dirty: [],
        hashes: {},
        mode: "convergence",
        corePath: corePath,
        leanDir: root,
        promptPath: sharedPromptPath,
      });
    } finally {
      await rm(root, { recursive: true, force: true });
    }

    expect(codexCalls).toBe(1);
    expect(claudeCalls).toBe(1);
  });
});

describe("gradeReviewerOutput — tolerates the schema codex actually emits", () => {
  it("rejects an ASSUMPTION verdict of `drift` (the A-2 bug: assumRejected missed drift)", () => {
    const g = gradeReviewerOutput({
      assumption_verdicts: [{ obj_id: "A-2", verdict: "drift", note: "carrier floor smuggled in" }],
    } as never);
    expect(g.blocking).toContain("A-2");
  });

  it("rejects `partial` and `derived`; accepts faithful/regularity/equivalent", () => {
    const g = gradeReviewerOutput({
      assumption_verdicts: [
        { obj_id: "A-1", verdict: "derived" }, // over-claim → reject
        { obj_id: "A-3", verdict: "partial" }, // not fully equivalent → reject
        { obj_id: "A-4", verdict: "faithful-refinement" }, // accept
        { obj_id: "A-5", verdict: "regularity-bookkeeping" }, // accept
        { obj_id: "A-6", verdict: "substrate-gate" }, // accept (visible debt)
      ],
    } as never);
    expect(new Set(g.blocking)).toEqual(new Set(["A-1", "A-3"]));
  });

  // A reviewer rejects equivalence in prose far more often than with a listed NEG token. Every
  // phrasing below contains a POSITIVE root ("match"), so a positive-token scan that runs without
  // first testing failure/negation cues grades an explicit rejection as a pass.
  it.each([
    "fails to match",
    "failed to match",
    "cannot match",
    "doesn't match",
    "does not match",
    "no match",
    "lacks a match",
    "unable to match",
  ])("rejects the prose rejection %j (contains a positive root)", (verdict) => {
    const g = gradeReviewerOutput({
      statement_verdicts: [{ obj_id: "T-1", verdict, note: "reviewer rejected equivalence" }],
    } as never);
    expect(g.blocking).toContain("T-1");
    expect(g.rows.find((r) => r.obj_id === "T-1")?.verdict).toBe("drift");
  });

  // HEDGED positives. A negation-cue check does not catch these: the verdict opens with a real
  // positive token and qualifies it instead of negating it. Every string below is either taken
  // verbatim from a persisted reviewer log in this repo or is a shape those logs emit.
  it.each([
    // stat_ate_overlap_decay_v1.log:2136 — flags "a substantive closure/gate issue"
    "mostly faithful with an important gate/strengthening caveat",
    "aligned_with_caveat", // emitted 12x across banked runs
    "largely faithful",
    "faithful with a caveat",
    "faithful modulo a definitional gap",
    "equivalent except for the boundary case",
    "faithful if the carrier assumption is added",
    "partially aligned",
  ])("rejects the hedged positive %j", (verdict) => {
    const g = gradeReviewerOutput({
      statement_verdicts: [{ obj_id: "T-1", verdict, note: "qualified approval" }],
    } as never);
    expect(g.blocking).toContain("T-1");
  });

  // Guard the other direction: the negation-cue check must not swallow genuine passes.
  it.each([
    "matched",
    "faithful",
    "faithful-refinement",
    "regularity-bookkeeping",
    "substrate-gate",
    "equivalent",
    "matched — no concerns",
  ])("still accepts the genuine ASSUMPTION pass %j", (verdict) => {
    const g = gradeReviewerOutput({
      assumption_verdicts: [{ obj_id: "A-1", verdict }],
    } as never);
    expect(g.blocking).not.toContain("A-1");
  });

  it("normalizes an `escalate` ARRAY of {target, reason} to null (let blocking drive F2, no halt)", () => {
    const g = gradeReviewerOutput({
      statement_verdicts: [{ obj_id: "T-2", verdict: "drift", note: "extra hyps" }],
      escalate: [
        { target: "T-2", reason: "extra witness hyps" },
        { target: "A-2", reason: "carrier floor" },
      ],
    } as never);
    expect(g.escalate).toBeNull(); // kind-less array → no halting escalation
    expect(g.blocking).toContain("T-2"); // the drift still routes
  });

  it("surfaces an escalate ARRAY item that DOES carry a real kind", () => {
    const g = gradeReviewerOutput({
      escalate: [{ kind: "note-wrong", obj_id: "T-1", reason: "tex disagrees" }],
    } as never);
    expect(g.escalate?.kind).toBe("note-wrong");
  });

  it("reads keyed-object verdicts + `observation` (singular) as the note", () => {
    const g = gradeReviewerOutput({
      // object keyed by id (not array), value carries `observation` not `note`
      statement_verdicts: { "T-1": { verdict: "equivalent", observation: "matches" } } as never,
    });
    const row = g.rows.find((r) => r.obj_id === "T-1");
    expect(row?.verdict).toBe("equivalent");
    expect(row?.note).toBe("matches");
  });

  it("parses bare-string verdicts (the 'A-1: faithful. …' array shape the reviewer emitted)", () => {
    const g = gradeReviewerOutput({
      statement_verdicts: [
        "L-1: faithful. uses the derived ConditionalExchangeability consequence — acceptable.",
        "L-10: drift. the NL is a generic Le Cam bridge; the Lean is a specialized rate theorem.",
        "L-11: partial drift. only tail-bias membership is proven by this anchor.",
      ] as never,
      assumption_verdicts: [
        "A-1: faithful. PotentialOutcomeConditionalExchangeability unfolds to a genuine CondIndepFun primitive.",
      ] as never,
    });
    const v = Object.fromEntries(g.rows.map((r) => [r.obj_id, r.verdict]));
    expect(v["L-1"]).toBe("equivalent"); // faithful → matched/equivalent
    expect(v["A-1"]).toBe("equivalent");
    expect(v["L-10"]).toBe("drift");
    expect(v["L-11"]).toBe("drift"); // "partial drift" → flagged
    expect(g.blocking.sort()).toEqual(["L-10", "L-11"]);
  });

  it("canonicalizes invented COMPOUND verdict tokens (factored_equivalent → pass, drift/conditionalized → fail)", () => {
    const g = gradeReviewerOutput({
      statement_verdicts: [
        { target: "L-3", verdict: "factored_equivalent", observation: "faithful as the algebraic core" },
        { obj_id: "L-1", verdict: "aligned", observations: ["consumes the derived ConditionalExchangeability"] },
        { obj_id: "T-2", verdict: "drift/conditionalized", note: "extra hyps" },
        { obj_id: "A-3", verdict: "mostly faithful with a caveat" },
        { obj_id: "P-9", verdict: "aligned, the Lean uses the derived consequence which is fine" },
      ],
    } as never);
    const v = Object.fromEntries(g.rows.map((r) => [r.obj_id, r.verdict]));
    expect(v["L-3"]).toBe("equivalent"); // factored_equivalent contains "equivalent" → pass
    expect(v["L-1"]).toBe("equivalent"); // "aligned" → pass
    expect(v["T-2"]).toBe("drift"); // contains "drift" → fail
    // A HEDGED positive is not a pass. This previously expected "equivalent" on the reading that
    // "mostly faithful" leads with a positive token; a live reviewer emitted
    // "mostly faithful with an important gate/strengthening caveat" whose own body then reported
    // "a substantive closure/gate issue" (stat_ate_overlap_decay_v1.log:2136), so the qualifier is
    // load-bearing and the verdict must route as drift.
    expect(v["A-3"]).toBe("drift");
    expect(v["P-9"]).toBe("equivalent"); // benign "derived" in explanation (word 6) must NOT flip to drift
    expect(g.blocking).toEqual(["T-2", "A-3"]); // A-3's hedged verdict now routes as a blocker
  });

  it("parseJsonObject strips fences and slices the object", () => {
    const out = parseJsonObject('noise ```json\n{"status":"ok","statement_verdicts":[]}\n``` trailer');
    expect(out.status).toBe("ok");
  });
});
