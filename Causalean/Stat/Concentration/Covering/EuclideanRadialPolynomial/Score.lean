import Causalean.Stat.Concentration.Covering.EuclideanRadialPolynomial.Cover

/-!
# Bounded radial-polynomial score classes

This module assembles the moving-center radial basis into a bounded polynomial
and then into the residual score shape used by local-polynomial empirical
process arguments.  Coefficients range over the existing finite coefficient
box, all polynomial terms share one moving center, and a finite signed arm may
multiply the score.

The proofs are designed to reuse `HasPolynomialL2Cover.add`, `.mul`, `.neg`,
`.finSum`, the bounded finite-class certificate, and parameter pullback.  No
measure regularity beyond measurability is imposed, so the result remains
uniform for atomic probability measures.
-/

namespace Causalean.Stat.Concentration.EuclideanRadialPolynomial

open Causalean.Stat.Concentration
open scoped BigOperators

universe u v

/-- A bounded coefficient vector evaluated against all radial monomials from
degree zero through `p`, with one center shared by every term. -/
noncomputable def boundedRadialPolynomial
    (d p : ℕ) (q a b B : ℝ)
    (x : EuclideanPoint d) (β : CoeffBox (Fin (p + 1)) B)
    (z : EuclideanPoint d) : ℝ :=
  ∑ k : Fin (p + 1), β.1 k *
    radialAnnulusMonomial d q a b k.1 x z

/-- The parameter space for a shared center and a boxed radial-polynomial
coefficient vector. -/
abbrev RadialPolynomialParam (d p : ℕ) (B : ℝ) :=
  EuclideanPoint d × CoeffBox (Fin (p + 1)) B

/-- A shared-center bounded radial polynomial evaluated after a Euclidean
location map on a general observation space. -/
noncomputable def boundedRadialPolynomialOn
    {Ω : Type u} [MeasurableSpace Ω]
    (d p : ℕ) (loc : Ω → EuclideanPoint d) (q a b B : ℝ)
    (θ : RadialPolynomialParam d p B) (ω : Ω) : ℝ :=
  boundedRadialPolynomial d p q a b B θ.1 θ.2 (loc ω)

/-- The constant envelope of a boxed degree-`p` radial polynomial. -/
def radialPolynomialEnvelope (b : ℝ) (p : ℕ) (B : ℝ) : ℝ :=
  ((p + 1 : ℕ) : ℝ) * B * radialMonomialEnvelope b p

/-- Every boxed shared-center radial polynomial is bounded by the number of
basis functions times the coefficient bound times the monomial envelope. -/
theorem abs_boundedRadialPolynomial_le
    (d p : ℕ) {q a b B : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) (hB : 0 ≤ B)
    (x : EuclideanPoint d) (β : CoeffBox (Fin (p + 1)) B)
    (z : EuclideanPoint d) :
    |boundedRadialPolynomial d p q a b B x β z| ≤
      radialPolynomialEnvelope b p B := by
  classical
  calc
    |boundedRadialPolynomial d p q a b B x β z| ≤
        ∑ k : Fin (p + 1), |β.1 k * radialAnnulusMonomial d q a b k.1 x z| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (p + 1), |β.1 k| *
        |radialAnnulusMonomial d q a b k.1 x z| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul]
    _ ≤ ∑ _k : Fin (p + 1), B * radialMonomialEnvelope b p := by
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul (β.2 k)
          (abs_radialAnnulusMonomial_le d p k.1 hq ha hab
            (Nat.le_of_lt_succ k.2) x z)
          (abs_nonneg _) hB
    _ = radialPolynomialEnvelope b p B := by
      simp [radialPolynomialEnvelope]
      ring

/-
Assembly route for the shared-center polynomial certificate:

For each `k`, cover the product of the scalar coefficient coordinate and the
fixed-degree radial class.  Apply the existing finite-sum closure with
independent temporary centers and coefficient vectors.  Then pull the result
back to the diagonal map which repeats the actual center and coefficient
vector in every coordinate.  The public pullback theorem replaces external
cover centers by occupied diagonal representatives, so the resulting cover is
genuinely indexed by shared-center polynomials.
-/

/-- Boxed finite radial polynomials with one moving center shared by all
degrees have a uniform polynomial `L²` covering certificate. -/
theorem boundedRadialPolynomialOn_hasPolynomialL2Cover
    {Ω : Type u} [MeasurableSpace Ω]
    (d p : ℕ) (loc : Ω → EuclideanPoint d) {q a b B : ℝ}
    (hloc : Measurable loc)
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) (hB : 0 < B) :
    HasPolynomialL2Cover (boundedRadialPolynomialOn d p loc q a b B)
      (radialPolynomialEnvelope b p B) := by
  classical
  let M := radialMonomialEnvelope b p
  have hM : 0 < M := by
    dsimp [M, radialMonomialEnvelope]
    positivity
  letI : Nonempty (CoeffBox (Fin (p + 1)) B) :=
    ⟨⟨fun _ => 0, fun _ => by simpa using hB.le⟩⟩
  have hcoeff (k : Fin (p + 1)) :
      HasPolynomialL2Cover
        (fun β : CoeffBox (Fin (p + 1)) B => fun _ω : Ω => β.1 k) B := by
    have hbase := linearParameterClass_hasPolynomialL2Cover
      (𝒳 := Ω) (K := Fin 1) (B := B) (M := 1)
      (fun _ _ => (1 : ℝ)) hB (by norm_num)
      (fun _ => measurable_const) (fun _ _ => by norm_num)
    have hpull :=
      Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2Cover.pullback
        hbase
      (fun β : CoeffBox (Fin (p + 1)) B =>
        (⟨fun _ : Fin 1 => β.1 k, fun _ => β.2 k⟩ : CoeffBox (Fin 1) B))
    convert hpull using 1
    · funext β ω
      simp [linearParameterClass]
    · simp
  have hradial (k : Fin (p + 1)) :
      HasPolynomialL2Cover
        (fun x : EuclideanPoint d => fun ω =>
          radialAnnulusMonomial d q a b k.1 x (loc ω)) M := by
    have hfull := radialMonomialOn_hasPolynomialL2Cover d p loc hloc hq ha hab
    have hpull :=
      Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2Cover.pullback
        hfull (fun x : EuclideanPoint d => (x, k))
    exact hpull
  have hterm (k : Fin (p + 1)) :
      HasPolynomialL2Cover
        (fun t : CoeffBox (Fin (p + 1)) B × EuclideanPoint d => fun ω =>
          t.1.1 k * radialAnnulusMonomial d q a b k.1 t.2 (loc ω))
        (B * M) := by
    exact (hcoeff k).mul (hradial k)
  have hsum := HasPolynomialL2Cover.finSum hterm
  have hpull :=
    Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2Cover.pullback
      hsum (fun θ : RadialPolynomialParam d p B => fun k => (θ.2, θ.1))
  change HasPolynomialL2Cover
    (fun θ : RadialPolynomialParam d p B => fun ω =>
      ∑ k : Fin (p + 1), θ.2.1 k *
        radialAnnulusMonomial d q a b k.1 θ.1 (loc ω))
    (((p + 1 : ℕ) : ℝ) * B * M)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hpull

/-- The parameter space of a moving center, a boxed polynomial coefficient
vector, and one member of a finite signed-arm family. -/
abbrev RadialResidualScoreParam (d p : ℕ) (B : ℝ) (A : Type v) :=
  RadialPolynomialParam d p B × A

/-- A finite-arm residual score: a radial monomial multiplies a bounded
response minus a shared-center boxed radial polynomial. -/
noncomputable def radialResidualScore
    {Ω : Type u} [MeasurableSpace Ω] {A : Type v}
    (d p : ℕ) (loc : Ω → EuclideanPoint d)
    (arm : A → Ω → ℝ) (response : Ω → ℝ)
    (q a b B : ℝ) (j : Fin (p + 1))
    (θ : RadialResidualScoreParam d p B A) (ω : Ω) : ℝ :=
  arm θ.2 ω *
    radialAnnulusMonomial d q a b j.1 θ.1.1 (loc ω) *
      (response ω -
        boundedRadialPolynomial d p q a b B θ.1.1 θ.1.2 (loc ω))

/-- The constant envelope for a bounded finite-arm radial residual score. -/
def radialResidualScoreEnvelope
    (b : ℝ) (p : ℕ) (B R : ℝ) : ℝ :=
  radialMonomialEnvelope b p *
    (R + radialPolynomialEnvelope b p B)

/-
Assembly route for the score certificate:

Use the fixed-degree radial cover for the leading monomial, the preceding
shared-center polynomial cover, a one-member finite cover for the fixed
response, and the finite cover for signed arms.  Existing `neg`, `add`, and
`mul` lemmas assemble an independently indexed superclass.  Pull back along
the map which identifies the two temporary centers and fixes the response;
this retains internal score-class cover centers and the displayed envelope.
-/

/-- **Covering certificate for a bounded finite-arm residual score.** Given [a measurable Euclidean
location map](hyp:hloc), [a finite family of arms, each measurable](hyp:harmMeas) and [bounded in
absolute value by 1](hyp:harmBound), [a measurable response variable](hyp:hresponseMeas) that is
[bounded in absolute value by R](hyp:hresponseBound), together with [a positive bandwidth
q](hyp:hq), [a nonnegative annulus inner radius a](hyp:ha), [inner radius at most outer radius
b](hyp:hab), [a positive polynomial-coefficient bound B](hyp:hB), and [a positive response bound
R](hyp:hR), then [the score formed by multiplying an arm indicator, a radial monomial, and the
residual of the response against a boxed radial-polynomial fit carries a positive-envelope uniform
polynomial `L²(Q)` covering certificate — with envelope `radialResidualScoreEnvelope b p B R` —
over every probability measure Q, including atomic ones](goal). -/
theorem radialResidualScore_hasPolynomialL2Cover
    {Ω : Type u} [MeasurableSpace Ω]
    {A : Type v} [Fintype A]
    (d p : ℕ) (loc : Ω → EuclideanPoint d)
    (arm : A → Ω → ℝ) (response : Ω → ℝ)
    {q a b B R : ℝ} (j : Fin (p + 1))
    (hloc : Measurable loc)
    (harmMeas : ∀ s, Measurable (arm s))
    (harmBound : ∀ s ω, |arm s ω| ≤ 1)
    (hresponseMeas : Measurable response)
    (hresponseBound : ∀ ω, |response ω| ≤ R)
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b)
    (hB : 0 < B) (hR : 0 < R) :
    HasPolynomialL2Cover
      (radialResidualScore d p loc arm response q a b B j)
      (radialResidualScoreEnvelope b p B R) := by
  classical
  let M := radialMonomialEnvelope b p
  let P := radialPolynomialEnvelope b p B
  have hM : 0 < M := by
    dsimp [M, radialMonomialEnvelope]
    positivity
  have hP : 0 < P := by
    dsimp [P, radialPolynomialEnvelope]
    have hp1 : (0 : ℝ) < (p + 1 : ℕ) := by positivity
    positivity
  have hU : 0 < M * (R + P) := by positivity
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI : IsEmpty A := hA
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [radialResidualScoreEnvelope, M, P] using hU
      · intro θ
        exact isEmptyElim θ.2
      · intro θ
        exact isEmptyElim θ.2
      · refine ⟨1, 0, le_rfl, ?_⟩
        intro Q hQ ε hε hε1
        refine ⟨∅, ?_, ?_⟩
        · simp
        · intro θ
          exact isEmptyElim θ.2
  | inr hA =>
      letI : Nonempty A := hA
      letI : Nonempty (CoeffBox (Fin (p + 1)) B) :=
        ⟨⟨fun _ => 0, fun _ => by simpa using hB.le⟩⟩
      have harm : HasPolynomialL2Cover arm 1 :=
        finiteClass_hasPolynomialL2Cover arm (by norm_num) harmMeas harmBound
      have hleading : HasPolynomialL2Cover
          (fun x : EuclideanPoint d => fun ω =>
            radialAnnulusMonomial d q a b j.1 x (loc ω)) M := by
        have hfull := radialMonomialOn_hasPolynomialL2Cover d p loc hloc hq ha hab
        have hpull :=
          Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2Cover.pullback
            hfull (fun x : EuclideanPoint d => (x, j))
        exact hpull
      have hpoly := boundedRadialPolynomialOn_hasPolynomialL2Cover
        d p loc hloc hq ha hab hB
      have hresponse : HasPolynomialL2Cover
          (fun _ : Unit => response) R := by
        exact finiteClass_hasPolynomialL2Cover (fun _ : Unit => response)
          hR (fun _ => hresponseMeas) (fun _ => hresponseBound)
      have harmLeading := harm.mul hleading
      have hresidual := hresponse.add hpoly.neg
      have hsuper := harmLeading.mul hresidual
      have hpull :=
        Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2Cover.pullback
          hsuper
          (fun θ : RadialResidualScoreParam d p B A =>
            ((θ.2, θ.1.1), ((), θ.1)))
      change HasPolynomialL2Cover
        (radialResidualScore d p loc arm response q a b B j)
        (M * (R + P))
      simp only [one_mul] at hpull
      exact hpull

private structure RadialResidualCoverData
    (Ω : Type u) [MeasurableSpace Ω] (A : Type v) (d p : ℕ) where
  loc : Ω → EuclideanPoint d
  arm : A → Ω → ℝ
  response : Ω → ℝ
  q : ℝ
  a : ℝ
  b : ℝ
  B : ℝ
  R : ℝ
  loc_measurable : Measurable loc
  arm_measurable : ∀ s, Measurable (arm s)
  arm_bound : ∀ s ω, |arm s ω| ≤ 1
  response_measurable : Measurable response
  response_bound : ∀ ω, |response ω| ≤ R
  q_pos : 0 < q
  a_nonneg : 0 ≤ a
  ab : a ≤ b
  B_pos : 0 < B
  R_pos : 0 < R

/-- The radial residual-score construction admits entropy witnesses depending
only on the Euclidean dimension, polynomial degree, and finite arm type.  In
particular, the witnesses precede all location maps, arm functions, responses,
bandwidths, annuli, and envelope radii. -/
theorem radialResidualScore_hasUniformPolynomialL2CoverWith
    {Ω : Type u} [MeasurableSpace Ω]
    {A : Type v} [Fintype A] [Nonempty A]
    (d p : ℕ) :
    ∃ C : ℝ, ∃ n : ℕ,
      ∀ (loc : Ω → EuclideanPoint d) (arm : A → Ω → ℝ)
        (response : Ω → ℝ) {q a b B R : ℝ},
        Measurable loc →
        (∀ s, Measurable (arm s)) →
        (∀ s ω, |arm s ω| ≤ 1) →
        Measurable response →
        (∀ ω, |response ω| ≤ R) →
        0 < q → 0 ≤ a → a ≤ b → 0 < B → 0 < R →
        HasPolynomialL2CoverWith
          (fun θ : RadialResidualScoreParam d p B A × Fin (p + 1) =>
            radialResidualScore d p loc arm response q a b B θ.2 θ.1)
          (radialResidualScoreEnvelope b p B R) C n := by
  classical
  let S := RadialResidualCoverData Ω A d p
  let M : S → ℝ := fun s => radialMonomialEnvelope s.b p
  let P : S → ℝ := fun s => radialPolynomialEnvelope s.b p s.B
  have hcoeff (k : Fin (p + 1)) :
      HasUniformPolynomialL2CoverOver S
        (fun s (β : CoeffBox (Fin (p + 1)) s.B) (_ω : Ω) => β.1 k)
        (fun s => s.B) := by
    refine ⟨32, 24, fun s => ?_⟩
    letI : Nonempty (CoeffBox (Fin 1) s.B) :=
      ⟨⟨fun _ => 0, fun _ => by simpa using s.B_pos.le⟩⟩
    letI : Nonempty (CoeffBox (Fin (p + 1)) s.B) :=
      ⟨⟨fun _ => 0, fun _ => by simpa using s.B_pos.le⟩⟩
    have hbase := (linearParameterClass_hasPseudoDimAtMost
      (𝒳 := Ω) (K := Fin 1) (fun _ _ => (1 : ℝ)) s.B).hasPolynomialL2CoverWith
      (fun _ => measurable_const) (by simpa using s.B_pos)
      (fun θ ω => by
        simp [linearParameterClass]
        exact θ.2 0)
    have hpull := HasPolynomialL2CoverWith.pullback hbase
      (fun β : CoeffBox (Fin (p + 1)) s.B =>
        (⟨fun _ : Fin 1 => β.1 k, fun _ => β.2 k⟩ : CoeffBox (Fin 1) s.B))
    convert hpull using 1
    · funext β ω
      simp [linearParameterClass]
    · norm_num
    · simp
  have hradial :
      HasUniformPolynomialL2CoverOver S
        (fun s (x : EuclideanPoint d × Fin (p + 1)) ω =>
          radialAnnulusMonomial d s.q s.a s.b x.2.1 x.1 (s.loc ω))
        M := by
    refine ⟨16, 8 * (radialPseudoDimBound d p + 1), fun s => ?_⟩
    exact radialMonomialOn_hasPolynomialL2CoverWith d p s.loc s.loc_measurable
      s.q_pos s.a_nonneg s.ab
  have hradialDegree (k : Fin (p + 1)) :
      HasUniformPolynomialL2CoverOver S
        (fun s (x : EuclideanPoint d) ω =>
          radialAnnulusMonomial d s.q s.a s.b k.1 x (s.loc ω)) M := by
    exact Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasUniformPolynomialL2CoverOver.pullback
      hradial (fun _ => inferInstance) (fun _ x => (x, k))
  have hterm (k : Fin (p + 1)) :
      HasUniformPolynomialL2CoverOver S
        (fun s (t : CoeffBox (Fin (p + 1)) s.B × EuclideanPoint d) ω =>
          t.1.1 k * radialAnnulusMonomial d s.q s.a s.b k.1 t.2 (s.loc ω))
        (fun s => s.B * M s) :=
    (hcoeff k).mul (hradialDegree k)
  have hsum := HasUniformPolynomialL2CoverOver.finSum hterm
  have hpoly :
      HasUniformPolynomialL2CoverOver S
        (fun s (θ : RadialPolynomialParam d p s.B) ω =>
          boundedRadialPolynomial d p s.q s.a s.b s.B θ.1 θ.2 (s.loc ω)) P := by
    have hpull :=
      Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasUniformPolynomialL2CoverOver.pullback
        hsum (fun s => ⟨(0, ⟨fun _ => 0, fun _ => by simpa using s.B_pos.le⟩)⟩)
      (fun s (θ : RadialPolynomialParam d p s.B) k => (θ.2, θ.1))
    simpa only [boundedRadialPolynomial, P, M, radialPolynomialEnvelope,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_assoc] using hpull
  have harm :
      HasUniformPolynomialL2CoverOver S (fun s => s.arm) (fun _ => 1) := by
    refine ⟨max 1 (Fintype.card A : ℝ), 1, fun s => ?_⟩
    exact finiteClass_hasPolynomialL2CoverWith s.arm (by norm_num)
      s.arm_measurable s.arm_bound
  have hresponse :
      HasUniformPolynomialL2CoverOver S
        (fun s (_ : Unit) => s.response) (fun s => s.R) := by
    refine ⟨1, 1, fun s => ?_⟩
    simpa using finiteClass_hasPolynomialL2CoverWith
      (fun _ : Unit => s.response) s.R_pos
      (fun _ => s.response_measurable) (fun _ => s.response_bound)
  have harmLeading := harm.mul hradial
  have hresidual := hresponse.add hpoly.neg
  have hsuper := harmLeading.mul hresidual
  have hpull :=
    Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasUniformPolynomialL2CoverOver.pullback
      hsuper (fun s => ⟨((0, ⟨fun _ => 0, fun _ => by simpa using s.B_pos.le⟩),
        Classical.choice inferInstance), 0⟩)
      (fun s (θ : RadialResidualScoreParam d p s.B A × Fin (p + 1)) =>
        ((θ.1.2, (θ.1.1.1, θ.2)), ((), θ.1.1)))
  obtain ⟨C, n, hpull⟩ := hpull
  refine ⟨C, n, ?_⟩
  intro loc arm response q a b B R hloc harmMeas harmBound
    hresponseMeas hresponseBound hq ha hab hB hR
  let s : S :=
    { loc := loc
      arm := arm
      response := response
      q := q
      a := a
      b := b
      B := B
      R := R
      loc_measurable := hloc
      arm_measurable := harmMeas
      arm_bound := harmBound
      response_measurable := hresponseMeas
      response_bound := hresponseBound
      q_pos := hq
      a_nonneg := ha
      ab := hab
      B_pos := hB
      R_pos := hR }
  have hs := hpull s
  simp only [one_mul] at hs
  exact hs

end Causalean.Stat.Concentration.EuclideanRadialPolynomial
