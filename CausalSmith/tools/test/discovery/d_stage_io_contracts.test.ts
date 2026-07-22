// D-stage mechanical I/O contracts.
//
// Every test here pins ONE rule: a plumbing fault must surface as a plumbing
// fault. The 2026-07-18 stat_cot_observational_efficiency run burned ~7h of
// stage time because five distinct mechanical faults were each rendered to the
// orchestrator as a MATHEMATICAL verdict ("below novelty floor", "the agent may
// be stuck", "solved nothing"), sending the D-orchestrator to repair maths that
// was never broken. These tests are the regression floor for that class.

import { describe, expect, it } from "vitest";
import { SolveUnitOutputSchema, partitionProofsByTarget } from "../../src/discovery/stages/d0_solve.js";
import { findingKeys, partitionReviewTargets } from "../../src/discovery/stages/d0.js";
import { checkProposalClosure, formatClosureViolation } from "../../src/discovery/core/coherence.js";
import { checkSymbolDeclarations } from "../../src/discovery/core/preflight.js";
import { combineVerdicts } from "../../src/discovery/core/review.js";
import { extractJsonObject } from "../../src/judgment.js";
import { CAP_GATES, CAP_GATE_FLAGS } from "../../src/cap_gates.js";
import { resolveNoteText } from "../../src/discovery/stages/d0_5_general.js";
import { overlayProvisionalProofs } from "../../src/discovery/core/paper_view.js";
import { wireStatementProofDependencies } from "../../src/discovery/core/dependencies.js";

describe("D0 solve output parsing is fail-loud on key drift", () => {
  it("rejects a camelCased top-level key instead of defaulting it to []", () => {
    // A model emitting `proposedCoreEdits` used to have it stripped as unknown,
    // then `proposed_core_edits` defaulted to [] — the round reported itself as
    // "solved nothing, proposed nothing" and the orchestrator re-solved blind.
    const raw = {
      proofs: [],
      proposedCoreEdits: [{ kind: "rebuild-reverse-dependencies", reason: "r" }],
    };
    const parsed = SolveUnitOutputSchema.safeParse(raw);
    expect(parsed.success).toBe(false);
    if (!parsed.success) {
      expect(JSON.stringify(parsed.error.issues)).toContain("proposedCoreEdits");
    }
  });

  it("still accepts a well-formed output with omitted optional arrays", () => {
    const parsed = SolveUnitOutputSchema.safeParse({ proofs: [{ id: "lem:a", proof_tex: "x" }] });
    expect(parsed.success).toBe(true);
    if (parsed.success) expect(parsed.data.proposed_core_edits).toEqual([]);
  });
});

describe("D0 proof attachment reports unmatched ids", () => {
  it("separates proofs whose id names no core statement", () => {
    // Previously `core.statements.find(...)` with no else: a hallucinated or
    // typo'd proofs[].id vanished, `solved` stayed flat, and the round warned
    // "zero new proofs — the agent may be stuck" (an id-mapping fault reported
    // as solver weakness).
    const { matched, unmatched } = partitionProofsByTarget(
      [
        { id: "lem:real", proof_tex: "p" },
        { id: "lem:typo", proof_tex: "p" },
      ],
      new Set(["lem:real"]),
    );
    expect(matched.map((p) => p.id)).toEqual(["lem:real"]);
    expect(unmatched).toEqual(["lem:typo"]);
  });

  it("reports every unmatched id, not just the first", () => {
    const { matched, unmatched } = partitionProofsByTarget(
      [
        { id: "lem:x", proof_tex: "p" },
        { id: "lem:y", proof_tex: "p" },
      ],
      new Set(["lem:other"]),
    );
    expect(matched).toEqual([]);
    expect(unmatched).toEqual(["lem:x", "lem:y"]);
  });
});

describe("D0.5 reviewer targets are not silently narrowed", () => {
  it("surfaces findings on assumption/definition nodes rather than dropping them", () => {
    // ReviewFindingSchema validates node_id against ALL core node ids (incl.
    // assumptions/definitions), but the required-target filter kept only
    // statements — so a finding on def:/ass: was structurally unenforceable and
    // reached D0 as prose only.
    const core = {
      statements: [{ id: "thm:a" }],
      assumptions: [{ id: "ass:b" }],
      definitions: [{ id: "def:c" }],
    };
    const p = partitionReviewTargets(["thm:a", "ass:b", "def:c", "lem:ghost"], core);
    expect(p.required).toEqual(["thm:a"]);
    expect(p.nonStatement).toEqual(["ass:b", "def:c"]);
    expect(p.unknown).toEqual(["lem:ghost"]);
  });
});

describe("findingKeys keeps distinct note-global findings distinct", () => {
  it("does not collapse several code-less, node-less findings to one key", () => {
    // Both convergence backstops consume this set. Collapsing N findings to the
    // single key "?@?" made a whack-a-mole round read as convergence.
    const keys = findingKeys([
      {
        findings: [
          { one_line: "the variance bound is asserted, not derived" },
          { one_line: "the dual selection is not shown measurable" },
          { one_line: "the cross term is dropped without justification" },
        ],
      },
    ]);
    expect(keys.size).toBe(3);
  });

  it("still treats a genuinely persisting note-global finding as the same key", () => {
    const one = findingKeys([{ findings: [{ one_line: "the variance bound is asserted" }] }]);
    const two = findingKeys([{ findings: [{ one_line: "the variance bound is asserted" }] }]);
    expect([...one]).toEqual([...two]);
  });

  it("keys on node+code when both are present", () => {
    const keys = findingKeys([
      { findings: [{ code: "G2", node_id: "thm:a", one_line: "x" }, { code: "G2", node_id: "thm:b", one_line: "y" }] },
    ]);
    expect(keys.size).toBe(2);
  });
});

describe("cross-store proposal closure", () => {
  const core = {
    statements: [{ id: "thm:main", depends_on: ["lem:helper"] }, { id: "lem:helper" }],
    assumptions: [],
    definitions: [],
  };

  it("flags a core node that the atomic base lacks and no proposal carries", () => {
    // This is the round 30-33 failure verbatim: lem:integrated-arm-path-
    // differentiation lived in core.json with a complete proof, was absent from
    // proto_core.json, and no proposal carried it — so `d0_apply_change --all`
    // would have produced a dangling dependency. It was caught only by
    // gpt-5.6-sol adjudication, three times, at maximum model cost.
    const res = checkProposalClosure({
      core,
      proto: { statements: [{ id: "thm:main" }], assumptions: [], definitions: [] },
      proposalIds: new Set<string>(),
    });
    expect(res.ok).toBe(false);
    expect(res.uncarried).toEqual(["lem:helper"]);
  });

  it("passes when a proposal carries the node", () => {
    const res = checkProposalClosure({
      core,
      proto: { statements: [{ id: "thm:main" }], assumptions: [], definitions: [] },
      proposalIds: new Set(["lem:helper"]),
    });
    expect(res.ok).toBe(true);
    expect(res.uncarried).toEqual([]);
  });

  it("reports proto nodes absent from core (drift in the other direction)", () => {
    const res = checkProposalClosure({
      core,
      proto: {
        statements: [{ id: "thm:main" }, { id: "lem:helper" }],
        assumptions: [{ id: "ass:stale" }],
        definitions: [],
      },
      proposalIds: new Set<string>(),
    });
    expect(res.protoOnly).toEqual(["ass:stale"]);
  });
});

describe("D0.5 sees this round's proofs, not the stale carried text", () => {
  const core = {
    statements: [
      { id: "lem:a", statement: "A", proof_tex: "OLD STALE PROOF" },
      { id: "thm:b", statement: "B", proof_tex: "kept" },
    ],
  };

  it("overlays a deferred same-round proof onto the rendered core", () => {
    // When a round proposes ANY structural change, fresh proofs are deferred to
    // proposed_proofs.json instead of being attached to core.json. D0.5 renders
    // from core.json alone — so the referee read the STALE proof and reported the
    // result as "merely asserted / incomplete". A plumbing artifact, delivered as
    // a mathematical defect.
    const { core: overlaid, applied } = overlayProvisionalProofs(core, [
      { id: "lem:a", proof_tex: "FRESH COMPLETE PROOF" },
    ]);
    expect(applied).toEqual(["lem:a"]);
    expect(overlaid.statements[0].proof_tex).toBe("FRESH COMPLETE PROOF");
    expect(overlaid.statements[1].proof_tex).toBe("kept");
  });

  it("does not mutate the caller's core", () => {
    overlayProvisionalProofs(core, [{ id: "lem:a", proof_tex: "FRESH" }]);
    expect(core.statements[0].proof_tex).toBe("OLD STALE PROOF");
  });

  it("reports a provisional proof naming no core statement rather than dropping it", () => {
    const { applied, unmatched } = overlayProvisionalProofs(core, [{ id: "lem:ghost", proof_tex: "p" }]);
    expect(applied).toEqual([]);
    expect(unmatched).toEqual(["lem:ghost"]);
  });
});

describe("reviewer target ids bind across emission styles", () => {
  const core = {
    statements: [{ id: "thm:observed-gradient" }, { id: "lem:helper" }],
    assumptions: [{ id: "ass:overlap" }],
    definitions: [],
  };

  it("resolves a BARE label to its prefixed core id", () => {
    // D0.5.G emitted `foo` after stripping `thm:`, so every flagged target missed
    // statementIds, required_core_targets stayed empty, exact-target enforcement never
    // armed, and each below-floor reroute became a WHOLE-PAPER re-solve.
    const p = partitionReviewTargets(["observed-gradient"], core);
    expect(p.required).toEqual(["thm:observed-gradient"]);
    expect(p.unknown).toEqual([]);
  });

  it("accepts the prefixed form unchanged", () => {
    expect(partitionReviewTargets(["thm:observed-gradient"], core).required).toEqual(["thm:observed-gradient"]);
  });

  it("refuses to guess when a bare label is ambiguous", () => {
    const ambiguous = { statements: [{ id: "thm:dual" }, { id: "lem:dual" }], assumptions: [], definitions: [] };
    const p = partitionReviewTargets(["dual"], ambiguous);
    expect(p.required).toEqual([]);
    expect(p.unknown).toEqual(["dual"]);
  });
});

describe("deterministic structural contracts replace model-discovered rules", () => {
  it("flags a free symbol absent from the symbol table (the round-36 G1 failure)", () => {
    const v = checkSymbolDeclarations({
      symbols: [{ name: "\\(\\lambda\\)" }],
      assumptions: [{ id: "ass:holder-propensity", free_symbols: ["\\(t_\\pi\\)", "\\(L_\\pi\\)", "\\(\\lambda\\)"] }],
      definitions: [],
    });
    expect(v).toHaveLength(1);
    expect(v[0].detail).toContain("t_\\pi");
    expect(v[0].detail).toContain("L_\\pi");
    expect(v[0].detail).not.toContain("lambda");
  });

  it("treats delimited and bare symbol declarations as the same symbol", () => {
    expect(
      checkSymbolDeclarations({
        symbols: [{ name: "t_\\pi" }],
        assumptions: [{ id: "ass:a", free_symbols: ["\\(t_\\pi\\)"] }],
      }),
    ).toEqual([]);
  });

  const replacementOutput = (proof: unknown = undefined) => ({
    proofs: [],
    proposed_core_edits: [{
      kind: "statement-replace",
      id: "thm:a",
      proposed: {
        id: "thm:a",
        kind: "theorem",
        statement: "A",
        depends_on: ["ass:x"],
        status: "proved",
        ...(proof === undefined ? {} : { proof_tex: proof }),
      },
      reason: "rewire its declared support",
      direction: "correct",
    }],
  });

  it("accepts a proved statement-replace without demanding its carried proof", () => {
    const parsed = SolveUnitOutputSchema.safeParse(replacementOutput());
    expect(parsed.success).toBe(true);
    if (parsed.success) {
      const edit = parsed.data.proposed_core_edits[0];
      expect(edit.kind).toBe("statement-replace");
      if (edit.kind === "statement-replace") expect(edit.proposed).not.toHaveProperty("proof_tex");
    }
  });

  it("rejects proof_tex on statement-replace instead of silently retaining it", () => {
    const parsed = SolveUnitOutputSchema.safeParse(replacementOutput("a full proof"));
    expect(parsed.success).toBe(false);
    if (!parsed.success) expect(JSON.stringify(parsed.error.issues)).toContain("proof_tex");
  });

  it("rejects even an empty proof_tex so the payload contract is absence, not content", () => {
    expect(SolveUnitOutputSchema.safeParse(replacementOutput("")).success).toBe(false);
  });

  it("rejects a null proof_tex rather than normalizing it into the payload", () => {
    expect(SolveUnitOutputSchema.safeParse(replacementOutput(null)).success).toBe(false);
  });

  it("accepts a cited statement-replace without inventing proof text", () => {
    const raw = replacementOutput();
    raw.proposed_core_edits[0].proposed.status = "cited";
    Object.assign(raw.proposed_core_edits[0].proposed, {
      depends_on: ["ass:x"],
      source: { cite: "R1983", locator: "Theorem 1" },
    });
    expect(SolveUnitOutputSchema.safeParse(raw).success).toBe(true);
  });

  it("keeps an assumption replacement's substantive condition", () => {
    const parsed = SolveUnitOutputSchema.parse({
      proofs: [],
      proposed_core_edits: [{
        kind: "assumption-replace",
        id: "ass:x",
        proposed: {
          id: "ass:x",
          condition: "the corrected long-form condition",
          free_symbols: [],
          novel: { flag: true, justification: "new setting" },
        },
        reason: "correct the condition",
        direction: "correct",
      }],
    });
    const edit = parsed.proposed_core_edits[0];
    expect(edit.kind).toBe("assumption-replace");
    if (edit.kind !== "assumption-replace") throw new Error("wrong edit kind");
    expect(edit.proposed).toHaveProperty(
      "condition",
      "the corrected long-form condition",
    );
  });

  it("accepts an explicit assumption deletion without a replacement payload", () => {
    const parsed = SolveUnitOutputSchema.parse({
      proofs: [],
      proposed_core_edits: [{
        kind: "assumption-delete",
        id: "ass:x",
        reason: "the repaired proof no longer uses this premise",
        direction: "delete-obsolete",
      }],
    });
    expect(parsed.proposed_core_edits).toEqual([expect.objectContaining({
      kind: "assumption-delete",
      id: "ass:x",
      direction: "delete-obsolete",
    })]);
  });

  it("keeps a definition replacement's substantive construction", () => {
    const parsed = SolveUnitOutputSchema.parse({
      proofs: [],
      proposed_core_edits: [{
        kind: "definition-replace",
        id: "def:x",
        proposed: {
          id: "def:x",
          name: "X",
          construction: "the corrected long-form construction",
          inputs: ["a"],
        },
        reason: "correct the formula",
        direction: "correct",
      }],
    });
    const edit = parsed.proposed_core_edits[0];
    expect(edit.kind).toBe("definition-replace");
    if (edit.kind !== "definition-replace") throw new Error("wrong edit kind");
    expect(edit.proposed).toHaveProperty(
      "construction",
      "the corrected long-form construction",
    );
  });
});

describe("closure violation message names the ids and the repair", () => {
  it("states the uncarried ids and does not read as a maths verdict", () => {
    const msg = formatClosureViolation({ ok: false, uncarried: ["lem:helper"], protoOnly: [] });
    expect(msg).toContain("lem:helper");
    expect(msg).toContain("closure violated");
    expect(msg).toMatch(/REPAIR:/);
    // The repair must point at the LIVE carrier (d0_working.json:proposals), never
    // at the retired per-kind mirror files — following the old text told the
    // operator to write a file whose reader now fails loud.
    expect(msg).not.toContain("proposed_proofs.json");
    expect(msg).toContain("d0_working.json");
  });
});

describe("an empty referee panel is not a pass", () => {
  it("throws rather than resolving no verdicts to pass", () => {
    // Fail-open guarded only by an invariant held in another module.
    expect(() => combineVerdicts([])).toThrow(/cannot resolve to a pass/i);
  });

  it("still combines a real panel normally", () => {
    const v = (referee: "math" | "decision", verdict: "pass" | "revise" | "fail") =>
      ({ referee, verdict, findings: [], cited_checks: [] }) as never;
    expect(combineVerdicts([v("math", "pass"), v("decision", "pass")])).toBe("pass");
    expect(combineVerdicts([v("math", "revise"), v("decision", "pass")])).toBe("revise");
    expect(combineVerdicts([v("math", "fail"), v("decision", "revise")])).toBe("fail");
  });
});

describe("the JSON extractor does not descend into a failed payload", () => {
  it("does not return a nested fragment when the real payload has a bad escape", () => {
    // `\s` is not a valid JSON escape, so the top-level object fails to parse. The old
    // walk advanced one character and returned the nested `source` object, which then
    // validated because stageOutputSchema is all-optional + passthrough.
    const out = String.raw`{"status":"completed","proof_tex":"\sum_{i}x","source":{"cite_id":"C1"}}`;
    let result: unknown = null;
    try {
      result = extractJsonObject(out);
    } catch {
      result = "threw";
    }
    expect(result).not.toEqual({ cite_id: "C1" });
  });

  it("does not return an inner object from truncated output", () => {
    let result: unknown = null;
    try {
      result = extractJsonObject('{"a":1,"b":{"c":2}');
    } catch {
      result = "threw";
    }
    expect(result).not.toEqual({ c: 2 });
  });

  it("still parses a clean payload", () => {
    expect(extractJsonObject('prose before {"status":"completed","n":1} prose after')).toEqual({
      status: "completed",
      n: 1,
    });
  });
});

describe("D0.5 cold referee never reviews an empty note", () => {
  it("throws when the assembled paper is empty rather than handing the referee nothing", async () => {
    // An empty note -> unparseable verdict -> parseGeneralReview fail-safes to
    // "incremental" -> reported as "BELOW NOVELTY FLOOR". An input failure presented as
    // a novelty judgment.
    await expect(resolveNoteText({ noteText: undefined, loadView: async () => "" })).rejects.toThrow(
      /plumbing failure, NOT a novelty verdict/,
    );
  });

  it("rejects a whitespace-only override", async () => {
    await expect(resolveNoteText({ noteText: "   \n  ", loadView: async () => "x" })).rejects.toThrow(/empty/i);
  });

  it("returns an explicit override unchanged, without assembling a view", async () => {
    let assembled = false;
    await expect(
      resolveNoteText({
        noteText: "\\section{Main}",
        loadView: async () => {
          assembled = true;
          return "other";
        },
      }),
    ).resolves.toBe("\\section{Main}");
    expect(assembled).toBe(false);
  });

  it("returns the assembled view when no override is given", async () => {
    await expect(resolveNoteText({ loadView: async () => "\\section{Assembled}" })).resolves.toBe(
      "\\section{Assembled}",
    );
  });
});

describe("prose-inferred dependency edges never break the graph", () => {
  const base = () => ({
    qid: "q", specialization: "v1", cluster: "stat", symbols: [], assumptions: [], definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "A", status: "proved", proof_tex: "as in lem:b, the dual holds", depends_on: [] },
      { id: "lem:b", kind: "lemma", statement: "B", status: "proved", proof_tex: "the dual of Lem:a gives this", depends_on: [] },
    ],
    bibliography: [],
  });

  it("does not introduce a cycle from mutual prose mentions", () => {
    // Widening this matcher to be case-insensitive made it discover strictly MORE
    // citations, so a pair of statements that merely mention each other in prose would
    // acquire a 2-cycle — which gate.ts reports as a G4 violation on a core that
    // previously passed. An inferred edge is never worth breaking the graph over.
    const core = base() as never;
    wireStatementProofDependencies(core);
    const [a, b] = (core as { statements: Array<{ depends_on?: string[] }> }).statements;
    const aDeps = a.depends_on ?? [];
    const bDeps = b.depends_on ?? [];
    expect(aDeps.includes("lem:b") && bDeps.includes("lem:a")).toBe(false);
  });

  it("still wires a plain one-directional citation", () => {
    const core = {
      qid: "q", specialization: "v1", cluster: "stat", symbols: [], assumptions: [], definitions: [],
      statements: [
        { id: "lem:a", kind: "lemma", statement: "A", status: "proved", proof_tex: "trivial", depends_on: [] },
        { id: "thm:main", kind: "theorem", statement: "M", status: "proved", proof_tex: "apply lem:a", depends_on: [] },
      ],
      bibliography: [],
    } as never;
    wireStatementProofDependencies(core);
    const stmts = (core as { statements: Array<{ id: string; depends_on?: string[] }> }).statements;
    expect(stmts[1].depends_on).toContain("lem:a");
  });
});

describe("D-phase loop budgets survive a resume", () => {
  it("registers a clearable cap gate that resets every D0 counter", () => {
    // D0_SOLVE_CAP / D0_REVISE_CAP were in-process `for` bounds with no persisted
    // counterpart, so every plain --resume granted a FRESH 15 solve rounds / 3 D0.5
    // rounds — unbounded re-sampling of a non-deterministic solver. consistency_heals
    // was worse: capped at 1 and stored in `design_decisions`, where no CapGate.clear
    // could reach it, so once tripped the only escape was hand-editing state.json.
    const gate = CAP_GATES.find((g) => g.flag === "d0_loop_cap_hit");
    expect(gate).toBeDefined();
    const flags = {
      d0_loop_cap_hit: "D0 solve cap exhausted",
      d0_loop_counters: { solve_rounds: 15, revise_rounds: 3, consistency_heals: 1 },
    } as never;
    gate!.clear(flags);
    const f = flags as unknown as {
      d0_loop_cap_hit?: string;
      d0_loop_counters: { solve_rounds: number; revise_rounds: number; consistency_heals: number };
    };
    expect(f.d0_loop_cap_hit).toBeUndefined();
    expect(f.d0_loop_counters).toEqual({ solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 });
  });

  it("resets the D-0.5 env-failure retry budget when its gate is cleared", () => {
    const gate = CAP_GATES.find((g) => g.flag === "stage_neg1_fallback");
    const flags = { stage_neg1_fallback: "blocked", neg1_env_failure_retries: 3 } as never;
    gate!.clear(flags);
    const f = flags as unknown as { stage_neg1_fallback: string | null; neg1_env_failure_retries: number };
    expect(f.stage_neg1_fallback).toBeNull();
    expect(f.neg1_env_failure_retries).toBe(0);
  });

  it("exposes every cap gate through the --clear-gate surface", () => {
    expect(CAP_GATE_FLAGS).toContain("d0_loop_cap_hit");
  });
});
