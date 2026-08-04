import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { runStructuralGate, pruneDeadAssumptions, type GateViolation } from "../../src/discovery/core/gate.js";
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

describe("pruneDeadAssumptions — reachability agrees with the citation resolver", () => {
  it("keeps an assumption whose only prose citation uses a LaTeX-escaped hyphen", () => {
    // Regression (audit of the 2026-07-29 id-matching fix): `extractNodeRefs` learned to
    // normalize `ass:foo\text{-}bar`, but this reachability walk ran the raw regex and
    // lowercased the match, so it still saw the truncated `ass:foo`. The assumption then
    // lost its last inbound edge and was DELETED here, while `findDanglingCitations` — which
    // does use the extractor — resolved the very same reference. Both sides were wrong
    // together before; the half-applied fix made them disagree, which is worse.
    const core = clone();
    core.assumptions.push({
      id: "ass:escaped-only",
      kind: "regularity",
      condition: "\\(\\pi(a\\mid x)\\ge c\\) for every \\(a,x\\)",
      free_symbols: [],
      standard: { name: "strict positivity", cite: "Tsybakov2009" },
    } as (typeof core.assumptions)[number]);
    const target = core.statements.find((s) => s.id === "thm:upper")!;
    target.proof_tex = `${target.proof_tex ?? ""} By \\(\\mathrm{ass:escaped\\text{-}only}\\) the density is bounded below.`;

    const res = pruneDeadAssumptions(core);
    expect(res).not.toBeNull();
    expect(res!.pruned).not.toContain("ass:escaped-only");
    expect(res!.core.assumptions.map((a) => a.id)).toContain("ass:escaped-only");
  });

  it("still prunes an assumption that nothing cites at all (the guard is not vacuous)", () => {
    const core = clone();
    core.assumptions.push({
      id: "ass:cited-nowhere",
      kind: "regularity",
      condition: "\\(\\pi(a\\mid x)\\ge c\\) for every \\(a,x\\)",
      free_symbols: [],
      standard: { name: "strict positivity", cite: "Tsybakov2009" },
    } as (typeof core.assumptions)[number]);
    expect(pruneDeadAssumptions(core)!.pruned).toContain("ass:cited-nowhere");
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

  it.each(["\\]", "\\)", "\\end{equation}", "\\end{aligned}\n\\]"])(
    "G2: a single displayed relation may end with a period before terminal TeX closer %s",
    (closer) => {
      const core = clone();
      core.assumptions.find((x) => x.id === "ass:smoothness")!.condition =
        `For every \\(d\\in\\mathcal D\\),\n  S_d \\perp G.\n${closer}`;
      const res = runStructuralGate(core, { requireDischarged: true });
      expect(res.violations.filter((v) => v.code === "G2")).toEqual([]);
    },
  );

  it.each([
    "First condition. second condition.\n\\]",
    "First condition. Second condition.\n\\]",
    "First condition.\\] Second condition.\n\\]",
    "First condition.” Second condition.\n\\]",
    "First relation is $X=0.$ Second relation is\n\\[\nY=0.\n\\]",
  ])(
    "G2: a terminal TeX closer does not hide an earlier sentence boundary: %s",
    (condition) => {
      const core = clone();
      core.assumptions.find((x) => x.id === "ass:smoothness")!.condition = condition;
      expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G2");
    },
  );

  it("G2: prose after a period and TeX closer is still a second sentence", () => {
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:smoothness")!.condition =
      "For every \\(d\\in\\mathcal D\\),\n\\[\n  S_d \\perp G.\n\\]\nAnother relation is imposed.";
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(codes(res.violations)).toContain("G2");
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
    core.assumptions.find((x) => x.id === "ass:tail")!.free_symbols!.push("undeclared_symbol");
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

  it("G5: a SHORT construction name does not fire inside ordinary English words", () => {
    // Regression (stat_doseresponse_minimax_elbow, 2026-07-29): the witness-reference
    // test was an unanchored substring match, so a construction named `g` matched the
    // `g` inside "designated"/"satisfying" and reported a witness carve that was not
    // there. It cost ~5 solve rounds and forced a cosmetic rename of the construction.
    const core = clone();
    core.definitions.find((d) => d.id === "def:witness")!.name = "g";
    const cls = core.definitions.find((d) => d.id === "def:law-class")!;
    cls.construction = "the set of laws satisfying every designated member property";
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(codes(res.violations)).not.toContain("G5");

    // ...but a genuine standalone reference to that same construction still trips.
    cls.construction = "the set of laws realizable as g";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G5");

    // ...including a SUBSCRIPTED reference. `_` is LaTeX's subscript delimiter, not a
    // name character, so it must not act as a token boundary: with `_` in the guard
    // class, `g` stopped matching `g_n` and `Omega` stopped matching `\Omega_n` — real
    // witness carves that G5 previously caught. A false negative in a soundness
    // firewall is the costly direction.
    cls.construction = "the set of laws realizable as g_n for some n";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G5");
    core.definitions.find((d) => d.id === "def:witness")!.name = "Omega";
    cls.construction = "\\(\\{P\\in\\mathcal P(\\Omega_n):P\\text{ is admissible}\\}\\)";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G5");
  });

  it.each([
    "The density obeys \\[ p(x) \\le 0.5. \\]",
    "The errors \\(\\varepsilon_i\\) are i.i.d. \\(N(0,\\sigma^2)\\) across \\(i\\).",
    "\\(P\\) is absolutely continuous w.r.t. \\(\\mu\\).",
    "\\(m(X)=\\mu(X)\\) holds \\(P_X\\)-a.e. \\(X\\).",
    "Overlap holds as in Thm. 2.1 with margin \\(\\delta\\).",
  ])("G2: decimals and math abbreviations are not sentence boundaries: %s", (condition) => {
    // Regression: the split fired on `i.i.d. \(…` (the `\\` lookahead), and the
    // terminal-closer guard disabled itself on ANY earlier period — so a decimal
    // constant re-created the very `.\n\]` false positive it was patched for.
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:smoothness")!.condition = condition;
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).not.toContain("G2");
  });

  it("G2: a genuinely omnibus condition with an abbreviation is still caught", () => {
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:smoothness")!.condition =
      "The errors are i.i.d. across units. The propensity is bounded away from zero.";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G2");
  });

  it("G3: `\\in` does not fire inside `\\int`/`\\infty`, but `\\in \\mathcal{…}` is caught", () => {
    const core = clone();
    // Class names that would previously false-fire via TeX-command tails.
    core.definitions.find((d) => d.id === "def:law-class")!.name = "T";
    const a = core.assumptions.find((x) => x.id === "ass:smoothness")!;
    a.condition = "\\(\\int T(x)\\,dx = 1\\) for the kernel weight";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).not.toContain("G3");
    core.definitions.find((d) => d.id === "def:law-class")!.name = "F";
    a.condition = "\\(\\|f\\|_\\infty \\le C\\) uniformly";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).not.toContain("G3");
    // The idiomatic font-wrapped membership must STILL be caught for a plain name.
    core.definitions.find((d) => d.id === "def:law-class")!.name = "C";
    a.condition = "the law satisfies \\(P \\in \\mathcal{C}\\)";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G3");
  });

  it("G5: the measure differential `\\,d\\mu` is not a witness reference to construction d", () => {
    const core = clone();
    core.definitions.find((d) => d.id === "def:witness")!.name = "d";
    const cls = core.definitions.find((d) => d.id === "def:law-class")!;
    cls.construction = "\\(\\{P : \\int f(x)\\,d\\mu(x) < \\infty\\}\\)";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).not.toContain("G5");
    // …while a genuine standalone reference to `d` still trips.
    cls.construction = "the set of laws realizable as d";
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G5");
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
