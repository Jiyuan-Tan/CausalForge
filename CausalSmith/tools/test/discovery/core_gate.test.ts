import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { runStructuralGate, type GateViolation } from "../../src/discovery/core/gate.js";
import type { Core } from "../../src/discovery/core/schema.js";

function loadFixture(): Core {
  const raw = readFileSync(
    new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url),
    "utf8",
  );
  return JSON.parse(raw) as Core;
}

function clone(): Core {
  return JSON.parse(JSON.stringify(loadFixture())) as Core;
}

function codes(vs: GateViolation[]): string[] {
  return vs.map((v) => v.code);
}

describe("D0 structural gate — golden fixture", () => {
  it("the hand-authored stat_ate_overlap_decay core passes every gate (post-PROVE)", () => {
    const res = runStructuralGate(loadFixture(), { requireDischarged: true });
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });
});

describe("D0 structural gate — schema generality (non-Stat cluster)", () => {
  it("a different cluster (ExactID backdoor-ATE identification) validates against the same schema", () => {
    const raw = readFileSync(
      new URL("../fixtures/exactid_backdoor_ate_core.json", import.meta.url),
      "utf8",
    );
    const core = JSON.parse(raw) as Core;
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
    // exercises the cross-cluster additions: an identifying functional (not a
    // rate) in `estimand_functional`, and no `sampling_model`.
    expect(core.estimand_functional).toContain("ψ(P)");
    expect(core.sampling_model).toBeUndefined();
  });
});

describe("D0 structural gate — A6-class breakage is rejected", () => {
  it("G3: an assumption that asserts class membership (the A6 bug) is rejected", () => {
    const core = clone();
    core.assumptions.push({
      id: "ass:lower-class",
      kind: "smoothness",
      condition:
        "whenever U ~ H_n with mu1 = g1, the resulting Bernoulli-outcome law belongs to \\(\\mathcal{P}_{\\kappa,\\beta}\\)",
      free_symbols: ["U", "H_n", "g1"],
      standard: { name: "lower-class compatibility", cite: "Tsybakov2009" },
    });
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G3");
  });

  it("G2: an omnibus assumption (derived-consequence prose) is rejected", () => {
    const core = clone();
    const a = core.assumptions.find((x) => x.id === "ass:smoothness")!;
    a.condition =
      "|b_lambda(x) − mu1(x)| ≤ C_β·λᵝ. Consequently the integrated bias |B_lambda| ≲ λ^{κ+β}.";
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G2");
  });

  it("G2: a single named mathematical condition may use the adjective standard", () => {
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:smoothness")!.condition =
      "The covariate space is standard Borel.";
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });

  it("G2: a where-used pointer inside the condition is rejected", () => {
    const core = clone();
    const a = core.assumptions.find((x) => x.id === "ass:tail")!;
    a.condition = a.condition + ", which is used by the achievability theorem";
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G2");
  });

  it("G1: an undeclared free symbol is rejected", () => {
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:tail")!.free_symbols.push("undeclared_symbol");
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G1");
  });

  it("G1: a comma-grouped free-symbol entry gets an atomic-splitting diagnostic", () => {
    const core = clone();
    const declared = core.symbols.slice(0, 2).map((s) => s.name);
    core.assumptions.find((x) => x.id === "ass:tail")!.free_symbols = [declared.join(",")];
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(res.violations.find((v) => v.code === "G1")?.message).toMatch(
      /exactly one declared symbol \(split comma-separated groups\)/,
    );
  });

  it("G5: a class carved by a witness/construction is rejected", () => {
    const core = clone();
    core.definitions.find((d) => d.id === "def:law-class")!.by_member_properties!.push(
      "every law realizable as the witness \\(P_n\\)",
    );
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G5");
  });

  it("G4: a dangling dependency is rejected", () => {
    const core = clone();
    core.statements.find((s) => s.id === "thm:lower")!.depends_on.push("thm:does-not-exist");
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G4");
  });

  it("G4: a dependency cycle is rejected", () => {
    const core = clone();
    // make lem:smoothness-l2 depend on a statement that (transitively) depends on it
    core.statements.find((s) => s.id === "lem:smoothness-l2")!.depends_on.push("thm:upper");
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G4");
  });

  it("G4: an undischarged node is rejected at the post-PROVE phase but allowed before", () => {
    const core = clone();
    core.statements.find((s) => s.id === "thm:upper")!.status = "to-prove";
    expect(runStructuralGate(core, { requireDischarged: true }).ok).toBe(false);
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G4");
    // at the CORE-authoring phase (statements not yet proven) this is fine
    expect(runStructuralGate(core, { requireDischarged: false }).ok).toBe(true);
  });

  it("G6: a standard citation absent from the bibliography is rejected", () => {
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:tail")!.standard = {
      name: "polynomial overlap decay",
      cite: "NoSuchPaper2099",
    };
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("G6");
  });

  it("schema: an assumption with neither standard nor novel is rejected", () => {
    const core = clone();
    delete (core.assumptions.find((x) => x.id === "ass:tail") as { standard?: unknown }).standard;
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain("schema");
  });
});
