import Causalean.Stat.Concentration.Covering.EuclideanRadialPolynomial.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Euclidean radial monomials and their finite traces

This module defines compactly supported radial monomials with a moving center
and proves finite-trace VC-subgraph bounds.  The bounds are intentionally
non-optimized.  Their important features are that they depend only on the
Euclidean dimension and the finite degree cutoff, and that they are stated at
the trace level, without any assumption on an ambient probability measure.

Odd and even degrees are treated uniformly.  On a nonnegative radial ray,
every positive integral power is monotone, so a threshold on a radial power is
again a distance threshold.  Squared Euclidean distance then supplies the
finite-dimensional affine lift used by the trace argument.
-/

namespace Causalean.Stat.Concentration.EuclideanRadialPolynomial

open Causalean.Stat.Concentration
open scoped BigOperators

/-- The `d`-dimensional real Euclidean space used by the radial classes. -/
abbrev EuclideanPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A Euclidean point paired with a real radius threshold.  Negative thresholds
are allowed; they give a constant ball or exterior label. -/
abbrev RadiusPoint (d : ℕ) := EuclideanPoint d × ℝ

/-- A moving center labels a point-radius pair when the point lies in the
corresponding closed ball about that center. -/
noncomputable def movingCenterClosedBallClassifier (d : ℕ)
    (x : EuclideanPoint d) (zr : RadiusPoint d) : Bool :=
  decide (dist zr.1 x ≤ zr.2)

/-- A moving center labels a point-radius pair when it lies strictly outside
the corresponding ball. -/
noncomputable def movingCenterBallExteriorClassifier (d : ℕ)
    (x : EuclideanPoint d) (zr : RadiusPoint d) : Bool :=
  decide (zr.2 < dist zr.1 x)

private noncomputable def distanceLift (d : ℕ) :
    Option (Option (Fin d)) → RadiusPoint d → ℝ
  | none, zr => if zr.2 < 0 then 1 else ‖zr.1‖ ^ 2 - zr.2 ^ 2
  | some none, zr => if zr.2 < 0 then 0 else 1
  | some (some i), zr => if zr.2 < 0 then 0 else zr.1.ofLp i

private noncomputable def distanceLiftParameter (d : ℕ) (x : EuclideanPoint d) :
    Option (Option (Fin d)) → ℝ
  | none => 1
  | some none => ‖x‖ ^ 2
  | some (some i) => -2 * x.ofLp i

private lemma distanceLift_sum (d : ℕ) (x z : EuclideanPoint d) (r : ℝ)
    (hr : ¬ r < 0) :
    (∑ i, distanceLiftParameter d x i * distanceLift d i (z, r)) =
      dist z x ^ 2 - r ^ 2 := by
  have hinner : (∑ i, x.ofLp i * z.ofLp i) = inner ℝ z x := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change x.ofLp i * z.ofLp i = x.ofLp i * z.ofLp i
    rfl
  have hsum : (∑ i, 2 * x.ofLp i * z.ofLp i) = 2 * inner ℝ z x := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hinner]
  rw [dist_eq_norm, norm_sub_sq_real]
  simp only [Fintype.sum_option]
  simp [distanceLiftParameter, distanceLift, hr]
  rw [hsum]
  ring

private lemma exterior_eq_linearSign (d : ℕ) (x : EuclideanPoint d)
    (zr : RadiusPoint d) :
    movingCenterBallExteriorClassifier d x zr =
      linearSignClass (distanceLift d) (distanceLiftParameter d x) zr := by
  by_cases hr : zr.2 < 0
  · have htrue : zr.2 < dist zr.1 x := lt_of_lt_of_le hr dist_nonneg
    simp [movingCenterBallExteriorClassifier, linearSignClass, distanceLift,
      distanceLiftParameter, Fintype.sum_option, hr, htrue]
  · have hr0 : 0 ≤ zr.2 := le_of_not_gt hr
    unfold movingCenterBallExteriorClassifier linearSignClass
    rw [distanceLift_sum d x zr.1 zr.2 hr]
    apply Bool.decide_congr
    rw [show (zr.2 < dist zr.1 x) ↔ zr.2 ^ 2 < dist zr.1 x ^ 2 by
      exact (sq_lt_sq₀ hr0 dist_nonneg).symm]
    constructor <;> intro h <;> linarith

private theorem movingCenterExterior_vc (d : ℕ) :
    HasVCAtMost (movingCenterBallExteriorClassifier d) (d + 2) := by
  have h := HasVCAtMost.reindex
    (linearSignClass_hasVCAtMost (distanceLift d)) (distanceLiftParameter d)
  have h' : HasVCAtMost
      (fun x => linearSignClass (distanceLift d) (distanceLiftParameter d x))
      (d + 2) := by
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc] using h
  convert h' using 1
  funext x zr
  exact exterior_eq_linearSign d x zr

private theorem HasVCAtMost.boolNot
    {X I : Type*} {pi : I → X → Bool} {v : ℕ}
    (h : HasVCAtMost pi v) : HasVCAtMost (fun i x => !(pi i x)) v := by
  intro n S
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  rw [Finset.mem_shatterer] at hs
  apply (show s.card ≤ (growthFamily pi S).vcDim from ?_).trans (h n S)
  apply Finset.Shatters.card_le_vcDim
  intro t ht
  obtain ⟨u, hu, hsu⟩ := hs (t := s \ t) Finset.sdiff_subset
  obtain ⟨i, hi⟩ := mem_growthFamily_iff.mp hu
  refine ⟨restrictionPattern (pi i) S, ?_, ?_⟩
  · rw [mem_growthFamily_iff]
    exact ⟨i, rfl⟩
  · ext j
    have hmem := Finset.ext_iff.mp hsu j
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hmem
    have hlabel : j ∈ restrictionPattern (fun x => !(pi i x)) S ↔ j ∈ u := by
      rw [hi]
    rw [restrictionPattern_mem_iff] at hlabel
    have hjts : j ∈ t → j ∈ s := fun hj => ht hj
    by_cases hjs : j ∈ s <;> by_cases hjt : j ∈ t <;>
      cases hp : pi i (S j) <;>
      simp_all [restrictionPattern_mem_iff]

private noncomputable def movingCenterOpenBallClassifier (d : ℕ)
    (x : EuclideanPoint d) (zr : RadiusPoint d) : Bool :=
  decide (dist zr.1 x < zr.2)

private lemma openBall_eq_linearSign (d : ℕ) (x : EuclideanPoint d)
    (zr : RadiusPoint d) :
    movingCenterOpenBallClassifier d x zr =
      linearSignClass (distanceLift d)
        (fun i => -distanceLiftParameter d x i) zr := by
  by_cases hr : zr.2 < 0
  · have hfalse : ¬ dist zr.1 x < zr.2 := not_lt_of_ge (hr.le.trans dist_nonneg)
    simp [movingCenterOpenBallClassifier, linearSignClass, distanceLift,
      distanceLiftParameter, Fintype.sum_option, hr, hfalse]
  · have hr0 : 0 ≤ zr.2 := le_of_not_gt hr
    have hsum :
        (∑ i, -distanceLiftParameter d x i * distanceLift d i zr) =
          -(dist zr.1 x ^ 2 - zr.2 ^ 2) := by
      rw [← distanceLift_sum d x zr.1 zr.2 hr]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    unfold movingCenterOpenBallClassifier linearSignClass
    rw [hsum]
    apply Bool.decide_congr
    rw [show (dist zr.1 x < zr.2) ↔ dist zr.1 x ^ 2 < zr.2 ^ 2 by
      exact (sq_lt_sq₀ (dist_nonneg : 0 ≤ dist zr.1 x) hr0).symm]
    constructor <;> intro h <;> linarith

private theorem movingCenterOpenBall_vc (d : ℕ) :
    HasVCAtMost (movingCenterOpenBallClassifier d) (d + 2) := by
  have h := HasVCAtMost.reindex
    (linearSignClass_hasVCAtMost (distanceLift d))
    (fun x i => -distanceLiftParameter d x i)
  have h' : HasVCAtMost
      (fun x => linearSignClass (distanceLift d)
        (fun i => -distanceLiftParameter d x i)) (d + 2) := by
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc] using h
  convert h' using 1
  funext x zr
  exact openBall_eq_linearSign d x zr

private noncomputable def movingCenterNonstrictExteriorClassifier (d : ℕ)
    (x : EuclideanPoint d) (zr : RadiusPoint d) : Bool :=
  decide (zr.2 ≤ dist zr.1 x)

private theorem movingCenterNonstrictExterior_vc (d : ℕ) :
    HasVCAtMost (movingCenterNonstrictExteriorClassifier d) (d + 2) := by
  have h := HasVCAtMost.boolNot (movingCenterOpenBall_vc d)
  convert h using 1
  funext x zr
  by_cases hlt : dist zr.1 x < zr.2
  · simp [movingCenterNonstrictExteriorClassifier, movingCenterOpenBallClassifier,
      hlt, not_le_of_gt hlt]
  · simp [movingCenterNonstrictExteriorClassifier, movingCenterOpenBallClassifier,
      hlt, le_of_not_gt hlt]

/-- Variable-radius closed-ball tests indexed by a moving Euclidean center
have VC dimension at most `d + 2`. -/
theorem movingCenterClosedBall_hasVCAtMost (d : ℕ) :
    HasVCAtMost (movingCenterClosedBallClassifier d) (d + 2) := by
  have h := HasVCAtMost.boolNot (movingCenterExterior_vc d)
  convert h using 1
  funext x zr
  by_cases hlt : zr.2 < dist zr.1 x
  · simp [movingCenterClosedBallClassifier, movingCenterBallExteriorClassifier,
      hlt, not_le_of_gt hlt]
  · simp [movingCenterClosedBallClassifier, movingCenterBallExteriorClassifier,
      hlt, le_of_not_gt hlt]

/-- Variable-radius strict-exterior tests indexed by a moving Euclidean center
have VC dimension at most `d + 2`. -/
theorem movingCenterBallExterior_hasVCAtMost (d : ℕ) :
    HasVCAtMost (movingCenterBallExteriorClassifier d) (d + 2) := by
  exact movingCenterExterior_vc d

/-- A center and a nonnegative radius parameterize a genuine closed Euclidean
ball. -/
abbrev ClosedBallParam (d : ℕ) := EuclideanPoint d × NNReal

/-- The Boolean classifier of closed Euclidean balls in finite-dimensional
real Euclidean space. -/
noncomputable def euclideanClosedBallClassifier (d : ℕ)
    (cr : ClosedBallParam d) (z : EuclideanPoint d) : Bool :=
  decide (dist z cr.1 ≤ (cr.2 : ℝ))

private noncomputable def ballLift (d : ℕ) :
    Option (Option (Fin d)) → EuclideanPoint d → ℝ
  | none, z => ‖z‖ ^ 2
  | some none, _ => 1
  | some (some i), z => z.ofLp i

private noncomputable def ballLiftParameter (d : ℕ) (cr : ClosedBallParam d) :
    Option (Option (Fin d)) → ℝ
  | none => 1
  | some none => ‖cr.1‖ ^ 2 - (cr.2 : ℝ) ^ 2
  | some (some i) => -2 * cr.1.ofLp i

private lemma ballLift_sum (d : ℕ) (cr : ClosedBallParam d)
    (z : EuclideanPoint d) :
    (∑ i, ballLiftParameter d cr i * ballLift d i z) =
      dist z cr.1 ^ 2 - (cr.2 : ℝ) ^ 2 := by
  have hinner : (∑ i, cr.1.ofLp i * z.ofLp i) = inner ℝ z cr.1 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change cr.1.ofLp i * z.ofLp i = cr.1.ofLp i * z.ofLp i
    rfl
  have hsum : (∑ i, 2 * cr.1.ofLp i * z.ofLp i) = 2 * inner ℝ z cr.1 := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hinner]
  rw [dist_eq_norm, norm_sub_sq_real]
  simp only [Fintype.sum_option]
  simp [ballLiftParameter, ballLift]
  rw [hsum]
  ring

private lemma ballExterior_eq_linearSign (d : ℕ) (cr : ClosedBallParam d)
    (z : EuclideanPoint d) :
    decide ((cr.2 : ℝ) < dist z cr.1) =
      linearSignClass (ballLift d) (ballLiftParameter d cr) z := by
  unfold linearSignClass
  rw [ballLift_sum]
  apply Bool.decide_congr
  rw [show ((cr.2 : ℝ) < dist z cr.1) ↔
      (cr.2 : ℝ) ^ 2 < dist z cr.1 ^ 2 by
    exact (sq_lt_sq₀ cr.2.2 dist_nonneg).symm]
  constructor <;> intro h <;> linarith

/-- Closed balls in `d`-dimensional Euclidean space have VC dimension at most
`d + 2`.  This neutral Causalean-only statement replaces the paper-local
planar ball lemma with a finite-dimensional bound. -/
theorem euclideanClosedBall_hasVCAtMost (d : ℕ) :
    HasVCAtMost (euclideanClosedBallClassifier d) (d + 2) := by
  have hext : HasVCAtMost
      (fun cr : ClosedBallParam d => fun z => decide ((cr.2 : ℝ) < dist z cr.1))
      (d + 2) := by
    have h := HasVCAtMost.reindex
      (linearSignClass_hasVCAtMost (ballLift d)) (ballLiftParameter d)
    simpa only [Fintype.card_option, Fintype.card_fin, ballExterior_eq_linearSign] using h
  have h := HasVCAtMost.boolNot hext
  convert h using 1
  funext cr z
  by_cases hlt : (cr.2 : ℝ) < dist z cr.1
  · simp [euclideanClosedBallClassifier, hlt, not_le_of_gt hlt]
  · simp [euclideanClosedBallClassifier, hlt, le_of_not_gt hlt]

/-- The compactly supported radial monomial with center `x`, bandwidth `q`,
relative annulus endpoints `a,b`, and natural degree `k`. -/
noncomputable def radialAnnulusMonomial (d : ℕ)
    (q a b : ℝ) (k : ℕ) (x z : EuclideanPoint d) : ℝ :=
  if a * q ≤ dist z x ∧ dist z x ≤ b * q then
    (dist z x / q) ^ k
  else 0

/-- The parameter space for a moving center and a degree between zero and
`p`, inclusive. -/
abbrev RadialMonomialParam (d p : ℕ) :=
  EuclideanPoint d × Fin (p + 1)

/-- The radial-monomial class in which the center and the degree up to `p`
both vary. -/
noncomputable def radialMonomialClass (d p : ℕ) (q a b : ℝ)
    (θ : RadialMonomialParam d p) (z : EuclideanPoint d) : ℝ :=
  radialAnnulusMonomial d q a b θ.2.1 θ.1 z

/-- An explicit trace bound for one fixed radial degree. -/
def fixedRadialPseudoDimBound (d : ℕ) : ℕ :=
  booleanCombinationVCBound 3 (d + 2)

/-- An explicit trace bound for all radial degrees from zero through `p`. -/
def radialPseudoDimBound (d p : ℕ) : ℕ :=
  finiteUnionVCBound (p + 1) (fixedRadialPseudoDimBound d)

private noncomputable def radialPowerRadius (q : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  q * (t ^ (↑k : ℝ)⁻¹)

private lemma radialPower_threshold_iff (k : ℕ) {q t r : ℝ}
    (hq : 0 < q) (ht : 0 ≤ t) (hr : 0 ≤ r) (hk : k ≠ 0) :
    t < (r / q) ^ k ↔ radialPowerRadius q k t < r := by
  have hu : 0 ≤ r / q := div_nonneg hr hq.le
  have hroot : 0 ≤ t ^ (↑k : ℝ)⁻¹ := Real.rpow_nonneg ht _
  calc
    t < (r / q) ^ k ↔
        (t ^ (↑k : ℝ)⁻¹) ^ k < (r / q) ^ k := by
          rw [Real.rpow_inv_natCast_pow ht hk]
    _ ↔ t ^ (↑k : ℝ)⁻¹ < r / q :=
      pow_lt_pow_iff_left₀ hroot hu hk
    _ ↔ radialPowerRadius q k t < r := by
      simpa [radialPowerRadius, mul_comm] using
        (lt_div_iff₀ hq : t ^ (↑k : ℝ)⁻¹ < r / q ↔
          t ^ (↑k : ℝ)⁻¹ * q < r)

/-
Proof route for the next two declarations:

* On a threshold sample `(z,t)`, `t < 0` is a parameter-free true label.
* For `t ≥ 0`, the subgraph label is the conjunction of the lower annulus
  exterior, the upper closed ball, and a radial-power threshold.
* When `k > 0`, monotonicity of `r ↦ r^k` on `r ≥ 0` turns the last predicate
  into another strict distance threshold.  The case `k = 0` is constant.
* Each distance predicate is a sign test after expanding squared distance in
  the lift `(1, x₁, …, x_d, ‖x‖²)`.  Apply the linear-sign theorem and then
  the Boolean-combination bound.  Finally use the finite-union theorem over
  `Fin (p+1)`.
-/

/-- For every positive bandwidth and ordered nonnegative annulus, the class
of fixed-degree radial monomials with moving center has pseudo-dimension
bounded solely by the Euclidean dimension. -/
theorem radialAnnulusMonomial_hasPseudoDimAtMost
    (d k : ℕ) {q a b : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) :
    HasPseudoDimAtMost
      (fun x : EuclideanPoint d => radialAnnulusMonomial d q a b k x)
      (fixedRadialPseudoDimBound d) := by
  let f0 : EuclideanPoint d → (EuclideanPoint d × ℝ) → Bool := fun x zt =>
    movingCenterNonstrictExteriorClassifier d x (zt.1, a * q)
  let f1 : EuclideanPoint d → (EuclideanPoint d × ℝ) → Bool := fun x zt =>
    movingCenterClosedBallClassifier d x (zt.1, b * q)
  let f2 : EuclideanPoint d → (EuclideanPoint d × ℝ) → Bool := fun x zt =>
    movingCenterBallExteriorClassifier d x (zt.1, radialPowerRadius q k zt.2)
  let pi : (j : Fin 3) → EuclideanPoint d →
      (EuclideanPoint d × ℝ) → Bool := fun j => ![f0, f1, f2] j
  let combine : (EuclideanPoint d × ℝ) → (Fin 3 → Bool) → Bool :=
    fun zt labels => if zt.2 < 0 then true else
      labels 0 && labels 1 && (if k = 0 then decide (zt.2 < 1) else labels 2)
  have h0 : HasVCAtMost f0 (d + 2) := by
    exact HasVCAtMost.compDomain (movingCenterNonstrictExterior_vc d)
      (fun zt : EuclideanPoint d × ℝ => (zt.1, a * q))
  have h1 : HasVCAtMost f1 (d + 2) := by
    exact HasVCAtMost.compDomain (movingCenterClosedBall_hasVCAtMost d)
      (fun zt : EuclideanPoint d × ℝ => (zt.1, b * q))
  have h2 : HasVCAtMost f2 (d + 2) := by
    exact HasVCAtMost.compDomain (movingCenterBallExterior_hasVCAtMost d)
      (fun zt : EuclideanPoint d × ℝ =>
        (zt.1, radialPowerRadius q k zt.2))
  have hpi : ∀ j, HasVCAtMost (pi j) (d + 2) := by
    intro j
    fin_cases j <;> simp only [pi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> assumption
  have hind := booleanCombination_hasVCAtMost pi hpi combine
  have hdiag := HasVCAtMost.reindex hind
    (fun x : EuclideanPoint d => fun _ => x)
  change HasVCAtMost
    (subgraphClassifier
      (fun x : EuclideanPoint d => radialAnnulusMonomial d q a b k x))
    (fixedRadialPseudoDimBound d)
  convert hdiag using 1
  case e'_4 => rfl
  funext x zt
  by_cases ht : zt.2 < 0
  · by_cases hann : a * q ≤ dist zt.1 x ∧ dist zt.1 x ≤ b * q
    · have hp : 0 ≤ (dist zt.1 x / q) ^ k :=
        pow_nonneg (div_nonneg dist_nonneg hq.le) k
      have htp : zt.2 < (dist zt.1 x / q) ^ k := lt_of_lt_of_le ht hp
      simp [subgraphClassifier, radialAnnulusMonomial, combine, pi, f0, f1, f2,
        movingCenterNonstrictExteriorClassifier, movingCenterClosedBallClassifier,
        movingCenterBallExteriorClassifier, hann, ht, hp, htp]
    · simp [subgraphClassifier, radialAnnulusMonomial, combine, pi, f0, f1, f2,
        movingCenterNonstrictExteriorClassifier, movingCenterClosedBallClassifier,
        movingCenterBallExteriorClassifier, hann, ht]
  · have ht0 : 0 ≤ zt.2 := le_of_not_gt ht
    by_cases hann : a * q ≤ dist zt.1 x ∧ dist zt.1 x ≤ b * q
    · by_cases hk : k = 0
      · subst k
        simp [subgraphClassifier, radialAnnulusMonomial, combine, pi, f0, f1, f2,
          movingCenterNonstrictExteriorClassifier, movingCenterClosedBallClassifier,
          movingCenterBallExteriorClassifier, hann, ht]
      · have hpow := radialPower_threshold_iff k hq ht0
          (dist_nonneg : 0 ≤ dist zt.1 x) hk
        simp [subgraphClassifier, radialAnnulusMonomial, combine, pi, f0, f1, f2,
          movingCenterNonstrictExteriorClassifier, movingCenterClosedBallClassifier,
          movingCenterBallExteriorClassifier, hann, ht, hk, hpow]
    · have hnot : ¬ zt.2 < 0 := ht
      simp [subgraphClassifier, radialAnnulusMonomial, combine, pi, f0, f1, f2,
        movingCenterNonstrictExteriorClassifier, movingCenterClosedBallClassifier,
        movingCenterBallExteriorClassifier, hann, ht, hnot]

/-- For every positive bandwidth and ordered nonnegative annulus, allowing
both the Euclidean center and any degree from zero through `p` to vary gives
the explicit pseudo-dimension bound `radialPseudoDimBound d p`. -/
theorem radialMonomialClass_hasPseudoDimAtMost
    (d p : ℕ) {q a b : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) :
    HasPseudoDimAtMost (radialMonomialClass d p q a b)
      (radialPseudoDimBound d p) := by
  let pi : (j : Fin (p + 1)) → EuclideanPoint d →
      (EuclideanPoint d × ℝ) → Bool := fun j =>
    subgraphClassifier
      (fun x : EuclideanPoint d => radialAnnulusMonomial d q a b j.1 x)
  have hpi : ∀ j, HasVCAtMost (pi j) (fixedRadialPseudoDimBound d) := by
    intro j
    exact radialAnnulusMonomial_hasPseudoDimAtMost d j.1 hq ha hab
  have hu := finiteUnion_hasVCAtMost pi hpi
  have hr := HasVCAtMost.reindex hu
    (fun theta : RadialMonomialParam d p =>
      (Sigma.mk theta.2 theta.1 : Sigma fun _ : Fin (p + 1) => EuclideanPoint d))
  change HasVCAtMost (subgraphClassifier (radialMonomialClass d p q a b))
    (radialPseudoDimBound d p)
  simp only [radialPseudoDimBound, Fintype.card_fin, pi, radialMonomialClass] at hr ⊢
  exact hr

end Causalean.Stat.Concentration.EuclideanRadialPolynomial
