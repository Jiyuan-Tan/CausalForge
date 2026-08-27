import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmSignedPrior
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Lifting a prior on positive nodes to a one-arm hard prior

This file performs the inverse-size tilt that reweights a prior on strictly
positive interpolation nodes and appends a zero atom, then reads off the cell
mass, propensity and treated outcome mean of the lifted one-arm configuration.
The tilt is chosen so that the observable moments of the lifted prior reduce to
rational tests of the original prior, which the signed interpolation weights
annihilate.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped ENNReal BigOperators

/-- The inverse-size tilt used to add a zero atom to a prior on positive nodes. -/
noncomputable def inverseTiltWeight {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) (a : ℝ) : Option ι → ℝ
  | none => 1 - ∑ i, (ω i).toReal * (a / x i)
  | some i => (ω i).toReal * (a / x i)

/-- All tilted weights are nonnegative provided the shift a is nonnegative and no
larger than any node.  Each positive node then receives a weight scaled by a
factor a/x in the unit interval, so the leftover mass assigned to the new zero
atom cannot go negative. -/
lemma inverseTiltWeight_nonneg {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hx : ∀ i, a ≤ x i) : ∀ z, 0 ≤ inverseTiltWeight ω x a z := by
  have hx0 (i : ι) : 0 ≤ x i := ha.trans (hx i)
  have hratio (i : ι) : 0 ≤ a / x i := div_nonneg ha (hx0 i)
  have hratio_one (i : ι) : a / x i ≤ 1 := by
    rcases (hx0 i).eq_or_lt with hzero | hpos
    · rw [← hzero]
      simp
    · exact (div_le_one₀ hpos).2 (hx i)
  intro z
  cases z with
  | some i => exact mul_nonneg ENNReal.toReal_nonneg (hratio i)
  | none =>
      have hωsum : ∑ i, (ω i).toReal = 1 := by
        letI : MeasurableSpace ι := ⊤
        simpa using (PMF.integral_eq_sum ω (fun _ : ι => (1 : ℝ))).symm
      have hsum : ∑ i, (ω i).toReal * (a / x i) ≤ ∑ i, (ω i).toReal := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_of_le_one_right ENNReal.toReal_nonneg (hratio_one i)
      unfold inverseTiltWeight
      linarith

/-- The tilted weights sum to one, since the zero atom is defined to absorb
exactly the mass the tilt removes from the positive nodes. -/
lemma inverseTiltWeight_sum {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) (a : ℝ) :
    ∑ z, inverseTiltWeight ω x a z = 1 := by
  rw [Fintype.sum_option]
  simp only [inverseTiltWeight]
  ring

/-- The probability prior after inverse-size tilting and adding a zero atom. -/
noncomputable def inverseTiltPMF {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) (a : ℝ)
    (hweight : ∀ z, 0 ≤ inverseTiltWeight ω x a z) : PMF (Option ι) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (inverseTiltWeight ω x a z)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hweight z), inverseTiltWeight_sum]
    simp

/-- The atom masses of the tilted prior, read as real numbers, are exactly the
tilted weights it was built from. -/
lemma inverseTiltPMF_toReal {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) (a : ℝ)
    (hweight : ∀ z, 0 ≤ inverseTiltWeight ω x a z) (z : Option ι) :
    (inverseTiltPMF ω x a hweight z).toReal = inverseTiltWeight ω x a z := by
  unfold inverseTiltPMF
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hweight z)]

/-- Expectation under the tilted prior for a test function vanishing at the new
zero atom. -/
lemma inverseTiltPMF_sum_of_none_eq_zero {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) (a : ℝ)
    (hweight : ∀ z, 0 ≤ inverseTiltWeight ω x a z)
    (g : Option ι → ℝ) (hg : g none = 0) :
    ∑ z, (inverseTiltPMF ω x a hweight z).toReal * g z =
      ∑ i, (ω i).toReal * (a / x i) * g (some i) := by
  simp_rw [inverseTiltPMF_toReal]
  rw [Fintype.sum_option, hg]
  simp [inverseTiltWeight]

/-- Cell mass in the lifted one-arm prior. -/
noncomputable def liftedCellMass {ι : Type*} (scale : ℝ) (x : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => scale * x i

/-- Propensity in the lifted one-arm prior. -/
noncomputable def liftedPropensity {ι : Type*}
    (epsilon a : ℝ) (x : ι → ℝ) : Option ι → ℝ
  | none => epsilon
  | some i => epsilon * (1 + a / x i)

/-- Treated outcome mean in the lifted one-arm prior. -/
noncomputable def liftedOutcomeMean {ι : Type*}
    (a : ℝ) (x : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => x i / (x i + a)

/-- At a positive node, the joint probability of the category and treatment in
the lifted configuration is scale·ε·(x + a): the inverse-size factor in the
propensity cancels the node in the cell mass and leaves an additive shift. -/
lemma lifted_arm_mass {ι : Type*} {scale epsilon a : ℝ} {x : ι → ℝ}
    (i : ι) (hxi : x i ≠ 0) :
    liftedCellMass scale x (some i) * liftedPropensity epsilon a x (some i) =
      scale * epsilon * (x i + a) := by
  simp only [liftedCellMass, liftedPropensity]
  field_simp

/-- At a positive node, the joint probability of the category, treatment and a
successful outcome in the lifted configuration is scale·ε·x — linear in the node,
so the observable treated-success intensities are affine in the node value. -/
lemma lifted_treated_success_mass {ι : Type*} {scale epsilon a : ℝ} {x : ι → ℝ}
    (i : ι) (hxi : x i ≠ 0) (hxia : x i + a ≠ 0) :
    liftedCellMass scale x (some i) * liftedPropensity epsilon a x (some i) *
        liftedOutcomeMean a x (some i) =
      scale * epsilon * x i := by
  rw [lifted_arm_mass i hxi]
  simp only [liftedOutcomeMean]
  field_simp

/-- The contribution of a positive node to the treated functional — its cell mass
times its treated outcome mean — is scale·x²/(x + a).  Unlike the observable
intensities this is a strictly convex function of the node, which is the source
of the separation between the two priors. -/
lemma lifted_functional_atom {ι : Type*} {scale a : ℝ} {x : ι → ℝ}
    (i : ι) (hxia : x i + a ≠ 0) :
    liftedCellMass scale x (some i) * liftedOutcomeMean a x (some i) =
      scale * x i ^ 2 / (x i + a) := by
  simp only [liftedCellMass, liftedOutcomeMean]
  field_simp

/-- One triple moment of the lifted `(p,pπ,pπμ)` atom. -/
noncomputable def liftedTripleMoment {ι : Type*}
    (scale epsilon a : ℝ) (x : ι → ℝ) (i j k : ℕ) (z : Option ι) : ℝ :=
  liftedCellMass scale x z ^ i *
    (liftedCellMass scale x z * liftedPropensity epsilon a x z) ^ j *
    (liftedCellMass scale x z * liftedPropensity epsilon a x z *
      liftedOutcomeMean a x z) ^ k

/-- The added zero atom contributes nothing to any observable moment of positive
total degree, because its lifted cell mass is zero; only the positive nodes are
seen by the moment-matching argument. -/
lemma liftedTripleMoment_none {ι : Type*} {scale epsilon a : ℝ} {x : ι → ℝ}
    {i j k : ℕ} (hdeg : 0 < i + j + k) :
    liftedTripleMoment scale epsilon a x i j k none = 0 := by
  unfold liftedTripleMoment
  simp only [liftedCellMass, liftedPropensity, liftedOutcomeMean]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hk : 0 < k := by omega
      simp [Nat.ne_of_gt hk]
    · simp [Nat.ne_of_gt hj]
  · simp [Nat.ne_of_gt hi]

/-- Exact algebra behind moment matching after inverse-size tilting. -/
lemma inverseTilt_liftedTripleMoment_sum {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) {a scale epsilon : ℝ}
    (hweight : ∀ z, 0 ≤ inverseTiltWeight ω x a z)
    (hx0 : ∀ r, x r ≠ 0) (hxa : ∀ r, x r + a ≠ 0)
    (i j k : ℕ) (hdeg : 0 < i + j + k) :
    ∑ z, (inverseTiltPMF ω x a hweight z).toReal *
        liftedTripleMoment scale epsilon a x i j k z =
      scale ^ (i + j + k) * epsilon ^ (j + k) * a *
        ∑ r, (ω r).toReal *
          (x r ^ (i + k) * (x r + a) ^ j / x r) := by
  rw [inverseTiltPMF_sum_of_none_eq_zero ω x a hweight
    (liftedTripleMoment scale epsilon a x i j k)
    (liftedTripleMoment_none hdeg)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold liftedTripleMoment
  simp only [liftedCellMass, liftedPropensity, liftedOutcomeMean]
  field_simp [hx0 r, hxa r]
  simp only [mul_pow]
  ring

/-- The raw node-barycentric signed vector annihilates every rational triple
moment produced by the inverse-size tilt within the interpolation degree. -/
lemma nodeBarycentric_tripleTest_sum_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hxinj : Function.Injective x) (hxpos : ∀ r, 0 < x r)
    (a : ℝ) (i j k : ℕ) (hdeg : i + j + k + 1 < Fintype.card ι) :
    ∑ r, (x r * barycentricWeight Finset.univ x r) *
        (x r ^ (i + k) * (x r + a) ^ j / x r) = 0 := by
  let P : Polynomial ℝ :=
    Polynomial.X ^ (i + k) * (Polynomial.X + Polynomial.C a) ^ j
  have hnat : P.natDegree + 1 < Fintype.card ι := by
    have hle : P.natDegree ≤ i + k + j := by
      dsimp [P]
      calc
        (Polynomial.X ^ (i + k) * (Polynomial.X + Polynomial.C a) ^ j).natDegree ≤
            (Polynomial.X ^ (i + k)).natDegree +
              ((Polynomial.X + Polynomial.C a) ^ j).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ (i + k) + j := by
          gcongr
          · simp
          · calc
              ((Polynomial.X + Polynomial.C a) ^ j).natDegree ≤
                  j * (Polynomial.X + Polynomial.C a).natDegree :=
                Polynomial.natDegree_pow_le
              _ ≤ j * 1 := by
                gcongr
                exact (Polynomial.natDegree_add_le _ _).trans (by simp)
              _ = j := by simp
    omega
  have hcancel := sum_barycentricWeight_mul_eval_eq_zero
    (s := Finset.univ) (x := x) (by
      intro r _ t _ hrt
      exact hxinj hrt) P (by simpa using hnat)
  rw [← hcancel]
  apply Finset.sum_congr rfl
  intro r _
  have hxr : x r ≠ 0 := ne_of_gt (hxpos r)
  simp only [P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_C]
  field_simp

/-- Consequently the two normalized Jordan priors have identical rational
triple tests throughout the matched degree range. -/
lemma jordanPMF_tripleTest_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hxinj : Function.Injective x) (hxpos : ∀ r, 0 < x r)
    (a : ℝ) (i j k : ℕ) (hdeg0 : 0 < i + j + k)
    (hdeg : i + j + k + 1 < Fintype.card ι)
    (hmass : 0 < positiveJordanMass
      (fun r => x r * barycentricWeight Finset.univ x r)) :
    let w := fun r => x r * barycentricWeight Finset.univ x r
    ∑ r, (positiveJordanPMF w hmass r).toReal *
        (x r ^ (i + k) * (x r + a) ^ j / x r) =
      ∑ r, (negativeJordanPMF w
        (by
          have hcard2 : 2 < Fintype.card ι := by omega
          have hzero : ∑ r, w r = 0 := by
            simpa [w] using sum_nodeBarycentricWeight_mul_zpow_eq_zero
              (s := Finset.univ) (x := x) (by
                intro r _ t _ hrt
                exact hxinj hrt)
              (fun r _ => hxpos r) (ell := 0) (by omega) (by simpa using hcard2)
          rw [← positiveJordanMass_eq_negativeJordanMass w hzero]
          exact hmass) r).toReal *
          (x r ^ (i + k) * (x r + a) ^ j / x r) := by
  dsimp only
  let w := fun r => x r * barycentricWeight Finset.univ x r
  have hcard2 : 2 < Fintype.card ι := by omega
  have hzero : ∑ r, w r = 0 := by
    simpa [w] using sum_nodeBarycentricWeight_mul_zpow_eq_zero
      (s := Finset.univ) (x := x) (by
        intro r _ t _ hrt
        exact hxinj hrt)
      (fun r _ => hxpos r) (ell := 0) (by omega) (by simpa using hcard2)
  apply positiveJordanPMF_sum_eq_negativeJordanPMF_sum_of_weighted_sum_eq_zero
    w (fun r => x r ^ (i + k) * (x r + a) ^ j / x r) hzero hmass
  simpa [w] using nodeBarycentric_tripleTest_sum_eq_zero
    x hxinj hxpos a i j k hdeg

/-- Equality of the rational tests on the original priors transports exactly to
equality of the corresponding lifted triple moments. -/
lemma inverseTilt_liftedTripleMoment_eq
    {ι : Type*} [Fintype ι]
    (ω₀ ω₁ : PMF ι) (x : ι → ℝ) {a scale epsilon : ℝ}
    (hweight₀ : ∀ z, 0 ≤ inverseTiltWeight ω₀ x a z)
    (hweight₁ : ∀ z, 0 ≤ inverseTiltWeight ω₁ x a z)
    (hx0 : ∀ r, x r ≠ 0) (hxa : ∀ r, x r + a ≠ 0)
    (i j k : ℕ) (hdeg0 : 0 < i + j + k)
    (htest :
      ∑ r, (ω₀ r).toReal * (x r ^ (i + k) * (x r + a) ^ j / x r) =
      ∑ r, (ω₁ r).toReal * (x r ^ (i + k) * (x r + a) ^ j / x r)) :
    ∑ z, (inverseTiltPMF ω₀ x a hweight₀ z).toReal *
        liftedTripleMoment scale epsilon a x i j k z =
      ∑ z, (inverseTiltPMF ω₁ x a hweight₁ z).toReal *
        liftedTripleMoment scale epsilon a x i j k z := by
  rw [inverseTilt_liftedTripleMoment_sum ω₀ x hweight₀ hx0 hxa i j k hdeg0,
    inverseTilt_liftedTripleMoment_sum ω₁ x hweight₁ hx0 hxa i j k hdeg0,
    htest]

/-- A family of matched rational tests yields all raw observable moments of
the inverse-tilted lifted priors, including the degree-zero normalization. -/
lemma inverseTilt_liftedRawMoment_eq
    {ι : Type*} [Fintype ι]
    (ω₀ ω₁ : PMF ι) (x : ι → ℝ) {a scale epsilon : ℝ}
    (hweight₀ : ∀ z, 0 ≤ inverseTiltWeight ω₀ x a z)
    (hweight₁ : ∀ z, 0 ≤ inverseTiltWeight ω₁ x a z)
    (hx0 : ∀ r, x r ≠ 0) (hxa : ∀ r, x r + a ≠ 0)
    (D : ℕ)
    (htest : ∀ i j k : ℕ, 0 < i + j + k → i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal * (x r ^ (i + k) * (x r + a) ^ j / x r) =
        ∑ r, (ω₁ r).toReal * (x r ^ (i + k) * (x r + a) ^ j / x r))
    (i j k : ℕ) (hdegree : i + j + k ≤ D) :
    ∑ z, (inverseTiltPMF ω₀ x a hweight₀ z).toReal *
        (liftedCellMass scale x z ^ i *
          (liftedCellMass scale x z * liftedPropensity epsilon a x z) ^ j *
          (liftedCellMass scale x z * liftedPropensity epsilon a x z *
            liftedOutcomeMean a x z) ^ k) =
      ∑ z, (inverseTiltPMF ω₁ x a hweight₁ z).toReal *
        (liftedCellMass scale x z ^ i *
          (liftedCellMass scale x z * liftedPropensity epsilon a x z) ^ j *
          (liftedCellMass scale x z * liftedPropensity epsilon a x z *
            liftedOutcomeMean a x z) ^ k) := by
  by_cases hzero : i + j + k = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst i
    subst j
    subst k
    simp only [pow_zero, mul_one]
    have hsum (ω : PMF ι) (hw : ∀ z, 0 ≤ inverseTiltWeight ω x a z) :
        ∑ z, (inverseTiltPMF ω x a hw z).toReal = 1 := by
      simp_rw [inverseTiltPMF_toReal]
      exact inverseTiltWeight_sum ω x a
    rw [hsum ω₀ hweight₀, hsum ω₁ hweight₁]
  · change ∑ z, (inverseTiltPMF ω₀ x a hweight₀ z).toReal *
        liftedTripleMoment scale epsilon a x i j k z =
      ∑ z, (inverseTiltPMF ω₁ x a hweight₁ z).toReal *
        liftedTripleMoment scale epsilon a x i j k z
    exact inverseTilt_liftedTripleMoment_eq ω₀ ω₁ x hweight₀ hweight₁ hx0 hxa
      i j k (Nat.pos_of_ne_zero hzero) (htest i j k (Nat.pos_of_ne_zero hzero) hdegree)

/-- The source construction's functional expectation becomes a rational test
of the original positive-node prior. -/
lemma inverseTilt_liftedFunctional_sum {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) {a scale : ℝ}
    (hweight : ∀ z, 0 ≤ inverseTiltWeight ω x a z)
    (hx0 : ∀ i, x i ≠ 0) (hxa : ∀ i, x i + a ≠ 0) :
    ∑ z, (inverseTiltPMF ω x a hweight z).toReal *
        (liftedCellMass scale x z * liftedOutcomeMean a x z) =
      scale * a * ∑ i, (ω i).toReal * (x i / (x i + a)) := by
  rw [inverseTiltPMF_sum_of_none_eq_zero ω x a hweight
    (fun z => liftedCellMass scale x z * liftedOutcomeMean a x z) (by simp [liftedCellMass])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [lifted_functional_atom i (hxa i)]
  field_simp [hx0 i, hxa i]

/-- Functional separation after inverse tilting is the original rational-test
separation multiplied by the deterministic factor `scale * a`. -/
lemma inverseTilt_liftedFunctional_gap {ι : Type*} [Fintype ι]
    (ω₀ ω₁ : PMF ι) (x : ι → ℝ) {a scale : ℝ}
    (hweight₀ : ∀ z, 0 ≤ inverseTiltWeight ω₀ x a z)
    (hweight₁ : ∀ z, 0 ≤ inverseTiltWeight ω₁ x a z)
    (hx0 : ∀ i, x i ≠ 0) (hxa : ∀ i, x i + a ≠ 0) :
    |(∑ z, (inverseTiltPMF ω₀ x a hweight₀ z).toReal *
          (liftedCellMass scale x z * liftedOutcomeMean a x z)) -
      (∑ z, (inverseTiltPMF ω₁ x a hweight₁ z).toReal *
          (liftedCellMass scale x z * liftedOutcomeMean a x z))| =
      |scale * a| *
        |(∑ i, (ω₀ i).toReal * (x i / (x i + a))) -
          ∑ i, (ω₁ i).toReal * (x i / (x i + a))| := by
  rw [inverseTilt_liftedFunctional_sum ω₀ x hweight₀ hx0 hxa,
    inverseTilt_liftedFunctional_sum ω₁ x hweight₁ hx0 hxa]
  rw [← abs_mul]
  congr 1
  ring

/-- The inverse-size tilt makes the expected lifted cell mass exactly
`scale * a`, independently of the positive-node prior. -/
lemma inverseTilt_liftedCellMass_sum {ι : Type*} [Fintype ι]
    (ω : PMF ι) (x : ι → ℝ) {a scale : ℝ}
    (hweight : ∀ z, 0 ≤ inverseTiltWeight ω x a z)
    (hx0 : ∀ i, x i ≠ 0) :
    ∑ z, (inverseTiltPMF ω x a hweight z).toReal * liftedCellMass scale x z =
      scale * a := by
  rw [inverseTiltPMF_sum_of_none_eq_zero ω x a hweight
    (liftedCellMass scale x) (by simp [liftedCellMass])]
  have hωsum : ∑ i, (ω i).toReal = 1 := by
    letI : MeasurableSpace ι := ⊤
    simpa using (PMF.integral_eq_sum ω (fun _ : ι => (1 : ℝ))).symm
  calc
    ∑ i, (ω i).toReal * (a / x i) * liftedCellMass scale x (some i) =
        scale * a * ∑ i, (ω i).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [liftedCellMass]
      field_simp [hx0 i]
    _ = scale * a := by rw [hωsum, mul_one]

/-- Positive nodes in `[a,1]` lift to valid outcome means. -/
lemma liftedOutcomeMean_mem_Icc {ι : Type*} {a : ℝ} {x : ι → ℝ}
    (ha : 0 ≤ a) (hx : ∀ i, a ≤ x i) (z : Option ι) :
    liftedOutcomeMean a x z ∈ Set.Icc (0 : ℝ) 1 := by
  cases z with
  | none => simp [liftedOutcomeMean]
  | some i =>
      have hxi : 0 ≤ x i := ha.trans (hx i)
      by_cases hden0 : x i + a = 0
      · have hxa : x i = 0 := by nlinarith
        simp [liftedOutcomeMean, hxa, hden0]
      · have hden : 0 < x i + a := lt_of_le_of_ne (add_nonneg hxi ha) (Ne.symm hden0)
        constructor
        · exact div_nonneg hxi hden.le
        · exact (div_le_one hden).2 (by linarith)

/-- If `epsilon * (1 + a/a)` stays below `1-epsilon`, then every lifted
propensity lies in the required overlap interval. -/
lemma liftedPropensity_mem_Icc {ι : Type*} {epsilon a : ℝ} {x : ι → ℝ}
    (he : 0 ≤ epsilon) (ha : 0 < a) (hx : ∀ i, a ≤ x i)
    (hoverlap : 2 * epsilon ≤ 1 - epsilon) (z : Option ι) :
    liftedPropensity epsilon a x z ∈ Set.Icc epsilon (1 - epsilon) := by
  cases z with
  | none =>
      simp only [liftedPropensity]
      exact ⟨le_rfl, by linarith⟩
  | some i =>
      have hxi : 0 < x i := lt_of_lt_of_le ha (hx i)
      have hratio0 : 0 ≤ a / x i := div_nonneg ha.le hxi.le
      have hratio1 : a / x i ≤ 1 := (div_le_one hxi).2 (hx i)
      simp only [liftedPropensity]
      constructor
      · nlinarith [mul_nonneg he hratio0]
      · calc
          epsilon * (1 + a / x i) ≤ 2 * epsilon := by nlinarith
          _ ≤ 1 - epsilon := hoverlap

/-- A decoupled positive shift bounded by `κ` times every node gives valid
propensities whenever `epsilon * (1+κ) ≤ 1-epsilon`. -/
lemma liftedPropensity_mem_Icc_of_shift_le {ι : Type*}
    {epsilon b κ : ℝ} {x : ι → ℝ}
    (he : 0 ≤ epsilon) (hb : 0 ≤ b) (hκ : 0 ≤ κ)
    (hx : ∀ i, 0 < x i) (hbx : ∀ i, b ≤ κ * x i)
    (hoverlap : epsilon * (1 + κ) ≤ 1 - epsilon) (z : Option ι) :
    liftedPropensity epsilon b x z ∈ Set.Icc epsilon (1 - epsilon) := by
  cases z with
  | none =>
      simp only [liftedPropensity]
      constructor
      · exact le_rfl
      · calc
          epsilon ≤ epsilon * (1 + κ) := by nlinarith [mul_nonneg he hκ]
          _ ≤ 1 - epsilon := hoverlap
  | some i =>
      have hratio0 : 0 ≤ b / x i := div_nonneg hb (hx i).le
      have hratioκ : b / x i ≤ κ := (div_le_iff₀ (hx i)).2 (hbx i)
      simp only [liftedPropensity]
      constructor
      · nlinarith [mul_nonneg he hratio0]
      · calc
          epsilon * (1 + b / x i) ≤ epsilon * (1 + κ) := by gcongr
          _ ≤ 1 - epsilon := hoverlap

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
