import { describe, expect, it } from "vitest";
import {
  structureTheoremSource,
  structureRecordSource,
  structureAndLinkify,
  findProofStart,
  isChain,
  isBinderRow,
  type StmtLine,
  type StatementItem,
} from "../src/lib/leanStatement.js";
import type { Library } from "../src/lib/library.js";

const linesOf = (b: StmtLine[]) => b.map((l) => l.text);
const findBinder = (rows: StatementItem[], name: string) =>
  rows.filter(isBinderRow).find((r) => r.names === name)!;

// A minimal library whose one entry references an EXTERNAL `eval` (standing
// in for the real `Polynomial.eval`), so `linkifyStatement` has something to
// (mis)link a bare `eval` token to if bound-variable detection fails.
function fixtureLibWithExternalEval(): Library {
  return {
    commit: "test",
    toolchain: "test",
    modules: {},
    sidecars: {},
    entries: [
      {
        name: "Fixture.usesEval",
        kind: "def",
        module: "Fixture",
        file: "Fixture.lean",
        line: 1,
        statement: "",
        doc: null,
        refs: [],
        axioms: [],
        usesSorry: false,
        extRefs: [{ n: "eval", m: "Mathlib.Algebra.Polynomial.Eval" }],
      },
    ],
  };
}

describe("structureTheoremSource", () => {
  it("structures a zero-binder Unicode-named lemma", () => {
    const structured = structureTheoremSource(
      "lemma σ_X_le : S.σ_X ≤ (inferInstance : MeasurableSpace P.Ω)",
    );

    expect(structured).not.toBeNull();
    expect(structured!.rows).toEqual([]);
    expect(isChain(structured!.conclusion)).toBe(false);
  });

  it("splits the DR-Learner oracle theorem's telescope into one row per binder", () => {
    const source = `theorem oracle_inequality_drLearner_highProb_honest
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ n : ℕ, ‖τhat n ω - θ₀‖ ^ 2 ≤ 4 := by
  obtain ⟨b, hb⟩ := foo`;

    const structured = structureTheoremSource(source);
    expect(structured).not.toBeNull();
    const rows = structured!.rows;
    // anonymous instance binders (`[StandardBorelSpace P.Ω]`, sugar for
    // `[inst : StandardBorelSpace P.Ω]`) carry no name — the row's `body`
    // holds the instance type itself. The two trailing `[NormedAddCommGroup
    // Θ] [InnerProductSpace ℝ Θ]` constraints on `Θ` are NOT separate rows —
    // they merge into `Θ`'s own row as extra lines (see the next assertion).
    expect(rows.map((r) => r.names)).toEqual([
      "",
      "",
      "",
      "S",
      "hA",
      "Θ",
      "Θ_set",
      "Θ_convex",
      "θ₀",
      "θ₀_mem",
      "eval",
      "eval_meas",
      "M_Θ M_Y M_μ ε",
      "hM_Θ",
      "δ",
      "hδ",
      "hδ'",
    ]);
    expect((rows[0].body as StmtLine[]).map((l) => l.text)).toEqual(["StandardBorelSpace P.Ω"]);
    expect((rows[1].body as StmtLine[]).map((l) => l.text)).toEqual(["IsFiniteMeasure P.μ"]);
    expect((findBinder(rows, "Θ").body as StmtLine[]).map((l) => l.text)).toEqual([
      "Type*",
      "NormedAddCommGroup Θ",
      "InnerProductSpace ℝ Θ",
    ]);

    // implicit/instance binders are always "decl"
    expect(rows[0].chip).toBe("decl"); // [StandardBorelSpace P.Ω]
    expect(rows[5].chip).toBe("decl"); // (Θ : Type*)
    // h-prefixed explicit hypotheses are "hyp"
    expect(findBinder(rows, "hA")!.chip).toBe("hyp");
    expect(findBinder(rows, "hM_Θ")!.chip).toBe("hyp");
    expect(findBinder(rows, "hδ")!.chip).toBe("hyp");
    // non-h-prefixed but Prop-shaped (contains ∈/∀/=) hypotheses are still "hyp"
    expect(findBinder(rows, "θ₀_mem")!.chip).toBe("hyp"); // θ₀ ∈ Θ_set
    expect(findBinder(rows, "eval_meas")!.chip).toBe("hyp"); // ∀ θ, Measurable (eval θ)
    // plain data-valued binders are "decl"
    expect(findBinder(rows, "S")!.chip).toBe("decl");
    expect(findBinder(rows, "eval")!.chip).toBe("decl"); // Θ → γ → ℝ, no relation symbol
    expect(findBinder(rows, "θ₀")!.chip).toBe("decl");

    // conclusion parsed, not a chain (nested ∃/∀/∧, no top-level →)
    expect(isChain(structured!.conclusion)).toBe(false);
  });

  it("renders a ∀-headed →-chain hypothesis as a chain block, not a plain multi-line row", () => {
    const source = `theorem foo
    {δ : ℝ} (hδ : 0 < δ)
    (hδ_dom : ∀ n K : ℕ, 0 < (split.foldB n).card →
      Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K →
      2 * (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 *
          Real.sqrt
            (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / (split.foldB n).card)
        ≤ (criticalRadius (ψ (split.foldB n).card)) ^ 2) :
    True := by
  trivial`;

    const structured = structureTheoremSource(source);
    expect(structured).not.toBeNull();
    const row = findBinder(structured!.rows, "hδ_dom")!;
    expect(row).toBeDefined();
    expect(row.chip).toBe("hyp");
    expect(isChain(row.body)).toBe(true);
    if (isChain(row.body)) {
      expect(linesOf(row.body.header!)).toEqual(["∀ n K : ℕ"]);
      expect(row.body.premises.map(linesOf)).toEqual([
        ["0 < (split.foldB n).card"],
        ["Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K"],
      ]);
      // The LHS has no top-level ∧/relation/+ to split on (its own `+`s are
      // inside the `(M_Θ + …)` parens) — so it stays one line and scrolls
      // horizontally rather than breaking at an arbitrary point.
      expect(linesOf(row.body.conclusion)).toEqual([
        "2 * (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 * Real.sqrt (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / (split.foldB n).card)",
        "≤ (criticalRadius (ψ (split.foldB n).card)) ^ 2",
      ]);
    }

    // a plain hypothesis stays a plain (non-chain) row
    const hdelta = findBinder(structured!.rows, "hδ")!;
    expect(isChain(hdelta.body)).toBe(false);
  });

  it("does not mistake a plain function-type binder for a chain", () => {
    const source = `theorem foo
    (eval : Θ → γ → ℝ) (idx : ℕ → S.Θ_set) :
    True := by
  trivial`;
    const structured = structureTheoremSource(source);
    expect(structured).not.toBeNull();
    const evalRow = findBinder(structured!.rows, "eval")!;
    expect(isChain(evalRow.body)).toBe(false);
    expect(linesOf(evalRow.body as StmtLine[])).toEqual(["Θ → γ → ℝ"]);
    const idxRow = findBinder(structured!.rows, "idx")!;
    expect(isChain(idxRow.body)).toBe(false);
  });

  it("returns null for non-theorem/lemma or unparseable sources", () => {
    expect(structureTheoremSource("def foo (x : ℕ) : ℕ := x")).toBeNull();
    expect(structureTheoremSource("theorem foo (x : ℕ (unbalanced : ℕ := x")).toBeNull();
  });

  it("structures a zero-binder theorem", () => {
    const structured = structureTheoremSource("theorem foo : True := by trivial");
    expect(structured).not.toBeNull();
    expect(structured!.rows).toEqual([]);
    expect(isChain(structured!.conclusion)).toBe(false);
  });

  it("preserves a `-- section` comment interleaved between binder groups as its own divider row", () => {
    const source = `theorem foo
    (S : ℕ)
    -- Oracle-inequality ingredients specialised to the DR system.
    (hA : 0 < S)
    /- a block comment
       spanning multiple lines, incl. unbalanced-looking punctuation (see below -/
    (hB : S ≤ 1) :
    True := by
  trivial`;
    const structured = structureTheoremSource(source);
    expect(structured).not.toBeNull();
    expect(
      structured!.rows.map((r) => (isBinderRow(r) ? { kind: "binder", names: r.names } : r)),
    ).toEqual([
      { kind: "binder", names: "S" },
      { kind: "comment", text: "Oracle-inequality ingredients specialised to the DR system." },
      { kind: "binder", names: "hA" },
      { kind: "comment", text: "a block comment\n       spanning multiple lines, incl. unbalanced-looking punctuation (see below" },
      { kind: "binder", names: "hB" },
    ]);
  });

  it("breaks a deeply nested ∃/∀/∧ conclusion at meaningful points, not at every source linebreak", () => {
    // The real DRLearnerHonest.lean conclusion (oracle_inequality_drLearner_highProb_honest):
    // the human-authored source already wraps almost every operator onto its
    // own line to fit ~100 columns at deep nesting — reproducing those breaks
    // verbatim (the old depthQuantizeLines behaviour) fragmented into ~18
    // lines. This should instead derive its own breaks: one line per ∧
    // conjunct / quantifier header / relation side, and leave genuinely
    // irreducible arithmetic (no top-level ∧, relation, or +) as one
    // horizontally-scrollable line instead of chopping it further.
    const source = `theorem foo (h : True) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ n : ℕ, ∃ E : Set P.Ω, MeasurableSet E ∧
        P.μ E ≥ 1 - ENNReal.ofReal δ ∧
        ∀ ω ∈ E,
          ‖τhat n ω - θ₀‖ ^ 2
            ≤ (4 * (1 + σ) / σ ^ 2)
                * (Real.sqrt
                    (if (split.foldB n).card = 0 then
                      2 * b
                     else
                      2 * R n
                        + 2 * b *
                          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
              + (4 / σ) * ((2 * B / ε) *
                  ∑ a : Bool,
                    (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2
                      S.toBackdoorEstimationSystem.P_X).toReal *
                      (eLpNorm (fun x => h.e_fn x - S.e_val x) 2
                        S.toBackdoorEstimationSystem.P_X).toReal)
              + (4 / σ) * r_opt n := by
  trivial`;
    const structured = structureTheoremSource(source);
    expect(structured).not.toBeNull();
    const lines = linesOf(structured!.conclusion as StmtLine[]);
    expect(lines).toEqual([
      "∃ b : ℝ,",
      "0 ≤ b ∧",
      "∀ n : ℕ,",
      "∃ E : Set P.Ω,",
      "MeasurableSet E ∧",
      "P.μ E ≥ 1 - ENNReal.ofReal δ ∧",
      "∀ ω ∈ E,",
      "‖τhat n ω - θ₀‖ ^ 2",
      "≤ (4 * (1 + σ) / σ ^ 2) * (Real.sqrt (if (split.foldB n).card = 0 then 2 * b else 2 * R n + 2 * b * Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2",
      "+ (4 / σ) * ((2 * B / ε) * ∑ a : Bool, (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2 S.toBackdoorEstimationSystem.P_X).toReal * (eLpNorm (fun x => h.e_fn x - S.e_val x) 2 S.toBackdoorEstimationSystem.P_X).toReal)",
      "+ (4 / σ) * r_opt n",
    ]);
    // `‖τhat n ω - θ₀‖ ^ 2` staying intact above already proves the `-` inside
    // the ‖·‖ norm was NOT mistaken for a top-level sum split.
  });

  it("does not link a bare re-use of an earlier row's own binder name to an unrelated same-named decl", () => {
    // `eval` is bound in its own row (`(eval : Θ → γ → ℝ)`); a LATER row's
    // type re-uses it bare (`eval_meas : ∀ θ, Measurable (eval θ)`). Since a
    // row's name is never itself linkified, per-row linkification can lose
    // that binding and wrongly link the bare `eval` to an unrelated decl.
    const source = `theorem foo
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ)) :
    True := by
  trivial`;
    const lib = fixtureLibWithExternalEval();
    const structured = structureAndLinkify(source, lib, "", "theorem");
    expect(structured).not.toBeNull();
    const evalMeasRow = findBinder(structured!.rows, "eval_meas")!;
    const html = (evalMeasRow.body as StmtLine[])[0].html!;
    expect(html).not.toContain("<a");
    expect(html).toContain("eval");
  });
});

describe("structureRecordSource", () => {
  // Verbatim from Causalean/Estimation/ATE/Setup.lean:61-87 (docstring
  // already stripped, as ModuleNode.astro does before calling this).
  const backdoorEstimationSystem = `structure BackdoorEstimationSystem (P : POSystem) (γ : Type*)
    [MeasurableSpace γ] [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    extends POBackdoorSystem P γ where
  /-- Value-space outcome regression \`μ(a, x)\`. -/
  μ_val : Bool → γ → ℝ
  μ_meas : ∀ b, Measurable (μ_val b)
  /-- Value-space propensity \`e(x) ∈ (0, 1)\`. -/
  e_val : γ → ℝ
  e_meas : Measurable e_val
  e_pos : ∀ x, 0 < e_val x
  e_lt_one : ∀ x, e_val x < 1
  /-- The value-space outcome regression \`μ_val\` represents the **observable**
  adjustment functional \`adjustedCE d = E[Y·1_{D=d}|σX] / P[D=d|σX]\`, with NO
  identification assumptions: \`μ_val d (factualX ·) =ᵐ adjustedCE d\`. This is the
  ML/regression target (\`adjustedCE\` is the regression \`E[Y|D=d,X]\`, see
  \`regression_adjustment\`). The counterfactual reading
  \`μ[Y(d)|σX] =ᵐ μ_val d ∘ factualX\` is NOT assumed here — it is the *derived*
  lemma \`μ_compat\` below, which additionally requires \`Assumptions\` via
  back-door identification (\`cate_backdoor\`). -/
  μ_reg_compat : ∀ d : Bool,
    (fun ω => μ_val d (toPOBackdoorSystem.factualX ω))
      =ᵐ[P.μ] toPOBackdoorSystem.adjustedCE d
  /-- Propensity factors through \`factualX\`:
  \`propScore true =ᵐ e_val (factualX ·)\`. -/
  e_compat :
    toPOBackdoorSystem.propScore true
      =ᵐ[P.μ] (fun ω => e_val (toPOBackdoorSystem.factualX ω))`;

  it("splits BackdoorEstimationSystem's params/extends and fields into two separate sections", () => {
    const structured = structureRecordSource(backdoorEstimationSystem);
    expect(structured).not.toBeNull();

    // rows = the parameter telescope + extends clause; fields = the where-block
    expect(
      structured!.rows.map((r) => (isBinderRow(r) ? { kind: "binder", names: r.names } : { kind: "comment" })),
    ).toEqual([
      { kind: "binder", names: "P" },
      // [MeasurableSpace γ] merges into γ's own row (it names γ directly);
      // [StandardBorelSpace P.Ω]/[IsFiniteMeasure P.μ] don't — they mention
      // only the projections `P.Ω`/`P.μ`, never a bare `P` token.
      { kind: "binder", names: "γ" },
      { kind: "binder", names: "" }, // [StandardBorelSpace P.Ω]
      { kind: "binder", names: "" }, // [IsFiniteMeasure P.μ]
      { kind: "binder", names: "extends" },
    ]);
    expect(
      structured!.fields!.map((r) => (isBinderRow(r) ? { kind: "binder", names: r.names } : { kind: "comment" })),
    ).toEqual([
      { kind: "comment" }, // /-- Value-space outcome regression … -/
      { kind: "binder", names: "μ_val" },
      { kind: "binder", names: "μ_meas" },
      { kind: "comment" }, // /-- Value-space propensity … -/
      { kind: "binder", names: "e_val" },
      { kind: "binder", names: "e_meas" },
      { kind: "binder", names: "e_pos" },
      { kind: "binder", names: "e_lt_one" },
      { kind: "comment" }, // the long μ_reg_compat docstring
      { kind: "binder", names: "μ_reg_compat" },
      { kind: "comment" }, // /-- Propensity factors … -/
      { kind: "binder", names: "e_compat" },
    ]);
    const items = [...structured!.rows, ...structured!.fields!];

    // no conclusion for a structure
    expect(structured!.conclusion).toEqual([]);

    // γ's typeclass constraint reads as one row, three lines
    expect(linesOf(findBinder(items, "γ").body as StmtLine[])).toEqual(["Type*", "MeasurableSpace γ"]);

    // the extends clause is captured as its own row
    const extendsRow = findBinder(items, "extends");
    expect(linesOf(extendsRow.body as StmtLine[])).toEqual(["POBackdoorSystem P γ"]);
    expect(extendsRow.chip).toBe("decl");

    // value fields (no relation/quantifier in their type) are "decl" …
    expect(findBinder(items, "μ_val").chip).toBe("decl");
    expect(findBinder(items, "e_val").chip).toBe("decl");
    // … Prop-valued fields (measurability/positivity/compatibility) are "hyp"
    // even though NONE of them are h-prefixed — this is a structure-field
    // naming convention, distinct from the theorem hypothesis h-prefix one.
    expect(findBinder(items, "μ_meas").chip).toBe("hyp");
    expect(findBinder(items, "e_pos").chip).toBe("hyp");
    expect(findBinder(items, "e_lt_one").chip).toBe("hyp");
    expect(findBinder(items, "μ_reg_compat").chip).toBe("hyp");
    expect(findBinder(items, "e_compat").chip).toBe("hyp");

    // the field's own multi-line type is preserved as a real (non-chain) body
    expect(isChain(findBinder(items, "e_compat").body)).toBe(false);
  });

  it("captures each field's own docstring as the comment immediately before its row", () => {
    const structured = structureRecordSource(backdoorEstimationSystem);
    const items = structured!.fields!;
    const muValIdx = items.findIndex((r) => isBinderRow(r) && r.names === "μ_val");
    const before = items[muValIdx - 1];
    expect(before.kind).toBe("comment");
    expect((before as { text: string }).text).toContain("Value-space outcome regression");
  });

  it("returns null for a plain def (no `where` field list) or unrecognised structure syntax", () => {
    expect(structureRecordSource("def Foo (x : ℕ) : ℕ := x")).toBeNull();
    expect(structureRecordSource("structure Foo := ⟨1⟩")).toBeNull();
  });

  it("parses bracket-wrapped instance fields and merges them into the field they constrain", () => {
    // Verbatim from Causalean/PO/*.lean (docstring already stripped) —
    // POSystem has no parameter telescope at all (`structure POSystem
    // where` directly) and its fields mix bare `name : type` lines with
    // `[name : Class]` instance-style fields naming an earlier field.
    const source = `structure POSystem where
  V : Type*
  [decEqV : DecidableEq V]
  [fintypeV : Fintype V]
  X : V → Type*
  [measX : ∀ v, MeasurableSpace (X v)]
  Ω : Type*
  [measΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  /-- Derived world-evaluation map \`Eval^P_r\` -- def:po-operator. -/
  eval : Regime V X → Ω → ∀ v, X v
  measurable_eval : ∀ r, Measurable (eval r)`;

    const structured = structureRecordSource(source);
    expect(structured).not.toBeNull();
    // no parameter telescope at all (`structure POSystem where` directly) —
    // everything here is a field
    expect(structured!.rows).toEqual([]);
    const items = structured!.fields!;

    // V absorbs its two instance constraints as extra lines, not new rows
    expect(linesOf(findBinder(items, "V").body as StmtLine[])).toEqual([
      "Type*",
      "DecidableEq V",
      "Fintype V",
    ]);
    // X absorbs its (named) MeasurableSpace instance the same way
    expect(linesOf(findBinder(items, "X").body as StmtLine[])).toEqual([
      "V → Type*",
      "∀ v, MeasurableSpace (X v)",
    ]);
    expect(linesOf(findBinder(items, "Ω").body as StmtLine[])).toEqual(["Type*", "MeasurableSpace Ω"]);
    expect(linesOf(findBinder(items, "μ").body as StmtLine[])).toEqual([
      "Measure Ω",
      "IsProbabilityMeasure μ",
    ]);

    // the docstring marker `/--` doesn't leak a stray leading `-` into the
    // extracted comment text
    const evalIdx = items.findIndex((r) => isBinderRow(r) && r.names === "eval");
    const comment = items[evalIdx - 1];
    expect(comment.kind).toBe("comment");
    expect((comment as { text: string }).text).toBe("Derived world-evaluation map `Eval^P_r` -- def:po-operator.");

    // no top-level row is left over for the merged-away instance fields
    expect(items.map((r) => (isBinderRow(r) ? r.names : null)).filter((n) => n !== null)).toEqual([
      "V",
      "X",
      "Ω",
      "μ",
      "eval",
      "measurable_eval",
    ]);
  });

  it("parses a pure-wrapper structure with no `where` block and no new fields at all", () => {
    // Verbatim from Causalean/Estimation/CATE/CATEEstimationSystem
    // (docstring already stripped) — `extends Bar`, full stop, nothing after.
    const source = `structure CATEEstimationSystem (P : POSystem) (γ : Type*)
    [MeasurableSpace γ] [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    extends BackdoorEstimationSystem P γ`;
    const structured = structureRecordSource(source);
    expect(structured).not.toBeNull();
    expect(structured!.rows.map((r) => (isBinderRow(r) ? r.names : "<comment>"))).toEqual([
      "P",
      "γ", // absorbs [MeasurableSpace γ]
      "",
      "",
      "extends",
    ]);
    expect(linesOf(findBinder(structured!.rows, "extends").body as StmtLine[])).toEqual([
      "BackdoorEstimationSystem P γ",
    ]);
    // no fields — the params + extends row IS the whole useful content
    expect(structured!.fields).toEqual([]);
  });

  it("parses a predicate-bundle structure's explicit `: Prop` return-type annotation before `where`", () => {
    // Verbatim from Causalean/Estimation/OrthogonalLearning/…SampleSplitPluginERM
    // (docstring already stripped) — a `structure Name (params) : Prop where`
    // shape distinct from both the bare `where` (POSystem) and `extends …
    // where` (BackdoorEstimationSystem) forms.
    const source = `structure SampleSplitPluginERM
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (θhat : ℕ → Ω → Θ)
    (ghat : ℕ → Ω → G)
    (r_opt : ℕ → ℝ) : Prop where
  r_opt_nonneg : ∀ n, 0 ≤ r_opt n
  mem_Θ_set    : ∀ n ω, θhat n ω ∈ S.Θ_set
  /-- ε-minimizer form. -/
  approx_min   : ∀ n ω, ∀ θ' ∈ S.Θ_set,
    empRiskFoldB S S_iid split n ω (θhat n ω) (ghat n ω)
      ≤ empRiskFoldB S S_iid split n ω θ' (ghat n ω) + r_opt n`;

    const structured = structureRecordSource(source);
    expect(structured).not.toBeNull();
    expect(structured!.rows.map((r) => (isBinderRow(r) ? r.names : "<comment>"))).toEqual([
      "S",
      "S_iid",
      "split",
      "θhat",
      "ghat",
      "r_opt",
    ]);
    expect(
      structured!.fields!.map((r) => (isBinderRow(r) ? r.names : "<comment>")),
    ).toEqual(["r_opt_nonneg", "mem_Θ_set", "<comment>", "approx_min"]);
    expect(findBinder(structured!.fields!, "r_opt_nonneg").chip).toBe("hyp");
  });
});

// A conclusion bound through `let`s: the first depth-0 `:=` belongs to the
// `let beta` binder, NOT to the proof. Regression test for the library page
// rendering this lemma's CONCLUSION as the bare string "let beta".
const LET_CONCLUSION_SOURCE = `lemma finitePoissonObjective_snd_sign_of_nuisance_score
    {U I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [Fintype I] [DecidableEq I] [Nonempty I]
    (q m : I → ℝ) (A : (U × ℝ) →ₗ[ℝ] (I → ℝ)) (u₀ : U)
    (hq : ∀ i, 0 < q i) (hm : ∀ i, 0 < m i)
    (hA : Function.Injective A)
    (hNuisance : ∀ u : U,
      ∑ i, q i * A (u, 0) i * (m i - Real.exp (A (u₀, 0) i)) = 0) :
    let beta :=
      (maximizerOrZero (finitePoissonObjective q m A)).2
    let scalarScore :=
      ∑ i, q i * A (0, 1) i * (m i - Real.exp (A (u₀, 0) i))
    (beta < 0 ↔ scalarScore < 0) ∧
    (beta = 0 ↔ scalarScore = 0) ∧
    (0 < beta ↔ 0 < scalarScore) := by
  dsimp only`;

describe("findProofStart (let/have-bound conclusions)", () => {
  it("does not mistake a let binder's := for the proof marker", () => {
    const concl = "\n    let beta :=\n      f x\n    beta < 0 := by simp";
    const cut = findProofStart(concl);
    expect(concl.slice(0, cut).trim()).toBe("let beta :=\n      f x\n    beta < 0");
  });

  it("still finds the proof marker with no let binder", () => {
    const concl = " Q := by simp";
    expect(concl.slice(0, findProofStart(concl))).toBe(" Q");
  });

  it("still ignores a named argument (γ := γ) inside the signature", () => {
    const concl = " H_ε (γ := γ) ε := by simp";
    expect(concl.slice(0, findProofStart(concl))).toBe(" H_ε (γ := γ) ε");
  });
});

describe("structureTheoremSource (let-bound conclusion)", () => {
  it("renders the whole let-bound conclusion, not the bare `let beta` head", () => {
    const structured = structureTheoremSource(LET_CONCLUSION_SOURCE);
    expect(structured).not.toBeNull();
    const concl = linesOf(
      isChain(structured!.conclusion) ? structured!.conclusion.lines : structured!.conclusion,
    ).join("\n");
    expect(concl).toContain("0 < beta ↔ 0 < scalarScore");
    expect(concl).toContain("maximizerOrZero");
    expect(concl).not.toContain("dsimp only");
    expect(concl.trim()).not.toBe("let beta");
  });

  it("still lists the hypothesis binders", () => {
    const structured = structureTheoremSource(LET_CONCLUSION_SOURCE);
    expect(findBinder(structured!.rows, "hNuisance")).toBeTruthy();
  });
});

describe("findProofStart (equation-compiler decls)", () => {
  // `lemma f : T\n  | 0 => rfl\n  | n+1 => by have h := …` has NO proof `:=`.
  // The `have`s belong to its arms, so the binder skip must not eat them and
  // run on into the proof body; keep the pre-existing naive answer.
  const EQN = `lemma partialEvalMap_latent (M : SCM N Ω) (s : FixedValues M) :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      (M.partialEvalMap n hn s ℓ).1 = ℓ
  | 0, _ => rfl
  | k + 1, hn => by
      have ih := M.partialEvalMap_latent s ℓ k
      set prev := M.partialEvalMap k hn s ℓ
      simp [ih, prev]`;

  it("does not run past the arms into the proof body", () => {
    const sig = EQN.slice(0, findProofStart(EQN));
    expect(sig).not.toContain("set prev");
    expect(sig).not.toContain("simp [ih, prev]");
  });

  it("keeps a let-bound conclusion working (no top-level => before the :=)", () => {
    const concl = "\n    let beta :=\n      f x\n    beta < 0 := by simp";
    expect(concl.slice(0, findProofStart(concl)).trim()).toContain("beta < 0");
  });

  it("a fun-arrow inside brackets does not disable the binder skip", () => {
    const concl = "\n    let u := (fun k => k + 1)\n    u 0 = 1 := by simp";
    expect(concl.slice(0, findProofStart(concl)).trim()).toContain("u 0 = 1");
  });
});

describe("findProofStart (already-stripped signature)", () => {
  // The library card cuts the proof, then re-parses the signature to structure
  // the conclusion. That text has NO proof marker, so its trailing `let`s are
  // conclusion binders — reporting the first `let`'s := here rendered the whole
  // conclusion as the bare head "let beta".
  it("reports -1 when the text has no proof marker", () => {
    const sig = "lemma foo (h : P) :\n    let beta := f x\n    beta < 0 ∧ beta ≠ 1";
    expect(findProofStart(sig)).toBe(-1);
  });

  it("structures a stripped signature's full let-bound conclusion", () => {
    const sig = LET_CONCLUSION_SOURCE.slice(0, LET_CONCLUSION_SOURCE.indexOf(" := by"));
    const structured = structureTheoremSource(sig);
    const concl = linesOf(
      isChain(structured!.conclusion) ? structured!.conclusion.lines : structured!.conclusion,
    ).join("\n");
    expect(concl).toContain("0 < beta ↔ 0 < scalarScore");
    expect(concl.trim()).not.toBe("let beta");
  });
});
