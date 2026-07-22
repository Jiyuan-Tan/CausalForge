import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { runProposalGate, type ProposalGateViolation } from "../../src/discovery/core/proposal_gate.js";
import type { Core } from "../../src/discovery/core/schema.js";

/** A minimal, well-formed proposal core: formal skeleton + the prose fields the
 * single-artifact design requires (tldr, project_justification, related_work,
 * per-statement justification/gap/consumer). The shape D-1.2 must emit. */
function protoCore(): Core {
  return {
    qid: "demo",
    target_estimand: "tau = E[Y(1) - Y(0)]",
    tldr: "We pin down the rate for tau under overlap.",
    project_justification: { gap: "no sharp rate known", niche: "rate indexed by overlap", fill: "matching bounds" },
    related_work: "Rosenbaum-Rubin (1983) introduce overlap; we sharpen the rate.",
    comparator_promise_table: [{
      comparator_bibkey: "Rosenbaum1983",
      comparator_claim: "Introduces overlap for observational causal effects.",
      matched_by: "Theorem 1",
      match_kind: "strict_tightening",
    }],
    symbols: [
      { name: "Y", type: "random variable" },
      { name: "tau", type: "real" },
    ],
    assumptions: [
      {
        id: "ass:overlap",
        kind: "support",
        condition: "0 < e(x) < 1 for all x",
        free_symbols: [],
        standard: { name: "overlap", cite: "Rosenbaum1983" },
      },
    ],
    definitions: [],
    statements: [
      {
        id: "thm:rate",
        kind: "conjecture",
        statement: "the minimax rate for tau is n^{-1/2}",
        depends_on: ["ass:overlap"],
        status: "to-prove",
        justification: "AIPW balances bias and variance to the stated rate.",
        gap: "no published rate for this regime",
        consumer: "practitioners get an honest rate",
      },
    ],
    bibliography: [{ key: "Rosenbaum1983" }],
  } as Core;
}

function clone(): Core {
  return JSON.parse(JSON.stringify(protoCore())) as Core;
}
function codes(vs: ProposalGateViolation[]): string[] {
  return vs.map((v) => v.code);
}

describe("D-1.2 proposal gate — golden proposal core (stat_ate_overlap_decay)", () => {
  it("the hand-derived core (formal + prose fields) passes every check", () => {
    const core = JSON.parse(
      readFileSync(new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url), "utf8"),
    ) as Core;
    const res = runProposalGate(core);
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
    // genuinely a proposal core: nothing proven, no D0 lemmas, prose present.
    expect(core.statements.every((s) => s.status === "to-prove")).toBe(true);
    expect(core.statements.every((s) => s.route === undefined && s.proof_tex === undefined)).toBe(true);
    expect(typeof core.tldr).toBe("string");
    expect(core.project_justification?.gap).toBeTruthy();
  });
});

describe("D-1.2 proposal gate — a well-formed proposal passes", () => {
  it("clean core → ok, no violations", () => {
    const res = runProposalGate(protoCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });
});

describe("D-1.2 proposal gate — GP1 standardness (non-empty tag content)", () => {
  it("empty novel.justification is rejected", () => {
    const core = clone();
    core.assumptions[0] = {
      id: "ass:novelcond",
      kind: "shape-restriction",
      condition: "the dose response is single-peaked in d",
      free_symbols: [],
      novel: { flag: true, justification: "   " },
    };
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("GP1");
  });
});

describe("D-1.2 proposal gate — GP2 all-to-prove (D-1 proves nothing)", () => {
  it("a statement marked status:proved is rejected", () => {
    const core = clone();
    core.statements[0].status = "proved";
    // Carry a proof so this isolates GP2 ("D-1 proves nothing"). Without one the node is
    // ALSO schema-invalid -- a proved statement must have a non-empty proof_tex -- and the
    // schema violation pre-empts the gate rule this test is about.
    core.statements[0].proof_tex = "A proof D-1 had no business writing.";
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("GP2");
  });

  it("a proved statement with NO proof is rejected as schema-invalid", () => {
    // The hollow-result case: renders as established with nothing establishing it, and
    // passes any discharge check that reads only `status`.
    const core = clone();
    core.statements[0].status = "proved";
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("schema");
  });

  it("a statement with a filled route is rejected", () => {
    const core = clone();
    core.statements[0].route = "reduce to Le Cam two-point";
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("GP2");
  });

  it("a statement with filled proof_tex is rejected", () => {
    const core = clone();
    core.statements[0].proof_tex = "\\begin{proof}...\\end{proof}";
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("GP2");
  });
});

describe("D-1.2 proposal gate — GP3 prose-field presence", () => {
  it("missing comparator_promise_table is rejected", () => {
    const core = clone();
    delete (core as Record<string, unknown>).comparator_promise_table;
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(res.violations.some((v) => v.code === "GP3" && /comparator_promise_table/.test(v.message))).toBe(true);
  });

  it("missing tldr is rejected", () => {
    const core = clone();
    delete (core as Record<string, unknown>).tldr;
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("GP3");
  });

  it("an incomplete project_justification (empty niche) is rejected", () => {
    const core = clone();
    core.project_justification = { gap: "g", niche: "  ", fill: "f" };
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(res.violations.some((v) => v.code === "GP3" && /niche/.test(v.message))).toBe(true);
  });

  it("a statement missing a prose field (consumer) is rejected, named by node id", () => {
    const core = clone();
    delete (core.statements[0] as Record<string, unknown>).consumer;
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(res.violations.some((v) => v.code === "GP3" && v.where === "thm:rate")).toBe(true);
  });
});

describe("D-1.2 proposal gate — the base G1–G7 gate still bites", () => {
  it("G3: an assumption asserting class membership (A6) bubbles through", () => {
    const core = clone();
    core.definitions.push({
      id: "def:class",
      name: "P_class",
      construction: "{Q : smooth(Q)}",
      by_member_properties: ["smooth"],
    });
    core.assumptions.push({
      id: "ass:member",
      kind: "smoothness",
      condition: "the resulting law belongs to P_class",
      free_symbols: [],
      standard: { name: "x", cite: "Rosenbaum1983" },
    });
    const res = runProposalGate(core);
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G3");
  });

  it("schema failure short-circuits before the GP checks", () => {
    const bad = clone() as unknown as Record<string, unknown>;
    delete bad.target_estimand; // required by the schema
    const res = runProposalGate(bad);
    expect(res.ok).toBe(false);
    expect(codes(res.violations as ProposalGateViolation[])).toContain("schema");
  });
});
