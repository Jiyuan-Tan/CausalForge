import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPriorLift
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Taylor expansion of the triple-count Poisson atoms

This file expands the exponential factor of a triple-count Poisson atom into a
truncated Taylor polynomial in the three observable intensities, controls the
discarded remainder by a positive exponential-series tail, and shows that two
priors matching all monomial moments up to a fixed degree produce identical
truncated predictive masses.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

/-- The polynomial in the three observable Poisson intensities whose value is
the `t`th Taylor term of a triple-count atom.  Coordinates are ordered as
`(p,p*pi,p*pi*mu)`. -/
noncomputable def triplePoissonTaylorPolynomial (t : ℕ) (sampleScale : ℝ)
    (c : Fin 3 → ℕ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C ((-sampleScale) ^ t / (Nat.factorial t : ℝ)) *
    MvPolynomial.X 0 ^ t *
  (MvPolynomial.C (sampleScale ^ c 0 / (Nat.factorial (c 0) : ℝ)) *
    MvPolynomial.X 2 ^ c 0) *
  (MvPolynomial.C (sampleScale ^ c 1 / (Nat.factorial (c 1) : ℝ)) *
    (MvPolynomial.X 1 - MvPolynomial.X 2) ^ c 1) *
  (MvPolynomial.C (sampleScale ^ c 2 / (Nat.factorial (c 2) : ℝ)) *
    (MvPolynomial.X 0 - MvPolynomial.X 1) ^ c 2)

/-- The Taylor-term polynomial has total degree at most the Taylor order plus the
total count, so a moment-matching budget of that size suffices to annihilate it.
This is the degree bookkeeping that drives the whole moment-matching argument. -/
lemma triplePoissonTaylorPolynomial_totalDegree_le (t : ℕ) (sampleScale : ℝ)
    (c : Fin 3 → ℕ) :
    (triplePoissonTaylorPolynomial t sampleScale c).totalDegree ≤
      t + c 0 + c 1 + c 2 := by
  let A : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C ((-sampleScale) ^ t / (Nat.factorial t : ℝ)) *
      MvPolynomial.X 0 ^ t
  let B : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C (sampleScale ^ c 0 / (Nat.factorial (c 0) : ℝ)) *
      MvPolynomial.X 2 ^ c 0
  let E : MvPolynomial (Fin 3) ℝ := MvPolynomial.X 1 - MvPolynomial.X 2
  let F : MvPolynomial (Fin 3) ℝ := MvPolynomial.X 0 - MvPolynomial.X 1
  let C : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C (sampleScale ^ c 1 / (Nat.factorial (c 1) : ℝ)) *
      E ^ c 1
  let D : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C (sampleScale ^ c 2 / (Nat.factorial (c 2) : ℝ)) *
      F ^ c 2
  have hF : F.totalDegree ≤ 1 := by
    dsimp [F]
    calc
      _ ≤ max (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree
          (-MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree := by
        simpa [sub_eq_add_neg] using
          MvPolynomial.totalDegree_add
            (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ)
            (-MvPolynomial.X (1 : Fin 3))
      _ ≤ 1 := by simp
  have hE : E.totalDegree ≤ 1 := by
    dsimp [E]
    calc
      _ ≤ max (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree
          (-MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree := by
        simpa [sub_eq_add_neg] using
          MvPolynomial.totalDegree_add
            (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ)
            (-MvPolynomial.X (2 : Fin 3))
      _ ≤ 1 := by simp
  have hA : A.totalDegree ≤ t := by
    dsimp [A]
    simpa using MvPolynomial.totalDegree_mul
      (MvPolynomial.C ((-sampleScale) ^ t / (Nat.factorial t : ℝ)))
      (MvPolynomial.X (0 : Fin 3) ^ t)
  have hB : B.totalDegree ≤ c 0 := by
    dsimp [B]
    simpa using MvPolynomial.totalDegree_mul
      (MvPolynomial.C (sampleScale ^ c 0 / (Nat.factorial (c 0) : ℝ)))
      (MvPolynomial.X (2 : Fin 3) ^ c 0)
  have hC : C.totalDegree ≤ c 1 := by
    dsimp [C]
    calc
      _ ≤ 0 + (E ^ c 1).totalDegree :=
        by simpa only [MvPolynomial.totalDegree_C] using
          MvPolynomial.totalDegree_mul
            (MvPolynomial.C (sampleScale ^ c 1 / (Nat.factorial (c 1) : ℝ)))
            (E ^ c 1)
      _ ≤ 0 + c 1 * E.totalDegree := by
        simpa only [zero_add] using MvPolynomial.totalDegree_pow E (c 1)
      _ ≤ c 1 := by
        simpa only [zero_add, Nat.mul_one] using Nat.mul_le_mul_left (c 1) hE
  have hD : D.totalDegree ≤ c 2 := by
    dsimp [D]
    calc
      _ ≤ 0 + (F ^ c 2).totalDegree :=
        by simpa only [MvPolynomial.totalDegree_C] using
          MvPolynomial.totalDegree_mul
            (MvPolynomial.C (sampleScale ^ c 2 / (Nat.factorial (c 2) : ℝ)))
            (F ^ c 2)
      _ ≤ 0 + c 2 * F.totalDegree := by
        simpa only [zero_add] using MvPolynomial.totalDegree_pow F (c 2)
      _ ≤ c 2 := by
        simpa only [zero_add, Nat.mul_one] using Nat.mul_le_mul_left (c 2) hF
  change (A * B * C * D).totalDegree ≤ _
  calc
    _ ≤ (A * B * C).totalDegree + D.totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ((A * B).totalDegree + C.totalDegree) + D.totalDegree := by
      gcongr
      exact MvPolynomial.totalDegree_mul _ _
    _ ≤ ((A.totalDegree + B.totalDegree) + C.totalDegree) + D.totalDegree := by
      gcongr
      exact MvPolynomial.totalDegree_mul _ _
    _ ≤ t + c 0 + c 1 + c 2 := by omega

/-- Equality of all monomial moments through degree `D` implies equality of
the prior expectations of any three-variable polynomial of degree at most
`D`. -/
lemma weighted_mvPolynomial_sum_eq_of_moments
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁) (v₀ : ι₀ → Fin 3 → ℝ)
    (v₁ : ι₁ → Fin 3 → ℝ) (D : ℕ)
    (hmoment : ∀ s : Fin 3 →₀ ℕ, s.sum (fun _ e => e) ≤ D →
      ∑ r, (ω₀ r).toReal * ∏ q, v₀ r q ^ s q =
        ∑ r, (ω₁ r).toReal * ∏ q, v₁ r q ^ s q)
    (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.totalDegree ≤ D) :
    ∑ r, (ω₀ r).toReal * MvPolynomial.eval (v₀ r) Q =
      ∑ r, (ω₁ r).toReal * MvPolynomial.eval (v₁ r) Q := by
  have expand₀ : ∑ r, (ω₀ r).toReal * MvPolynomial.eval (v₀ r) Q =
      ∑ s ∈ Q.support, Q.coeff s *
        ∑ r, (ω₀ r).toReal * ∏ q, v₀ r q ^ s q := by
    simp_rw [MvPolynomial.eval_eq', Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have expand₁ : ∑ r, (ω₁ r).toReal * MvPolynomial.eval (v₁ r) Q =
      ∑ s ∈ Q.support, Q.coeff s *
        ∑ r, (ω₁ r).toReal * ∏ q, v₁ r q ^ s q := by
    simp_rw [MvPolynomial.eval_eq', Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring
  calc
    _ = ∑ s ∈ Q.support, Q.coeff s *
        ∑ r, (ω₀ r).toReal * ∏ q, v₀ r q ^ s q := expand₀
    _ = ∑ s ∈ Q.support, Q.coeff s *
        ∑ r, (ω₁ r).toReal * ∏ q, v₁ r q ^ s q := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hmoment s ((MvPolynomial.le_totalDegree hs).trans hQ)]
    _ = _ := expand₁.symm

/-- Positive exponential-series tail beginning at degree `L`. -/
noncomputable def expSeriesTail (x : ℝ) (L : ℕ) : ℝ :=
  ∑' t : ℕ, x ^ (t + L) / (Nat.factorial (t + L) : ℝ)

/-- Absolute Taylor remainder for `exp (-x)`, bounded by the corresponding
positive exponential-series tail. -/
lemma abs_exp_neg_sub_taylor_le_tail (x : ℝ) (hx : 0 ≤ x) (L : ℕ) :
    |Real.exp (-x) - ∑ t ∈ Finset.range L, (-x) ^ t / (Nat.factorial t : ℝ)| ≤
      expSeriesTail x L := by
  let f : ℕ → ℝ := fun t => (-x) ^ t / (Nat.factorial t : ℝ)
  have hf : Summable f := by
    simpa [f] using NormedSpace.expSeries_div_summable (-x)
  have hsplit := hf.sum_add_tsum_nat_add L
  have hexp : Real.exp (-x) = ∑' t, f t := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [f] using (NormedSpace.expSeries_div_hasSum_exp (-x)).tsum_eq.symm
  have hrem : Real.exp (-x) - ∑ t ∈ Finset.range L,
      (-x) ^ t / (Nat.factorial t : ℝ) =
      ∑' t : ℕ, f (t + L) := by
    rw [hexp]
    change (∑' t, f t) - ∑ t ∈ Finset.range L, f t = _
    linarith [hsplit]
  rw [hrem]
  change ‖∑' t : ℕ, f (t + L)‖ ≤ expSeriesTail x L
  have habs : Summable (fun t : ℕ => ‖f (t + L)‖) :=
    (NormedSpace.norm_expSeries_div_summable (-x)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  refine (norm_tsum_le_tsum_norm habs).trans_eq ?_
  unfold expSeriesTail
  apply tsum_congr
  intro t
  simp only [f, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_of_nonneg hx]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial (t + L) : ℝ))]

/-- Product of the three Poisson power/factorial terms for the sufficient
counts `(N₁₁,N₁₀,N₀)`. -/
noncomputable def triplePoissonCoefficient (sampleScale p pi mu : ℝ)
    (c : Fin 3 → ℕ) : ℝ :=
  (sampleScale * p * pi * mu) ^ c 0 / (Nat.factorial (c 0) : ℝ) *
  (sampleScale * p * pi * (1 - mu)) ^ c 1 / (Nat.factorial (c 1) : ℝ) *
  (sampleScale * p * (1 - pi)) ^ c 2 / (Nat.factorial (c 2) : ℝ)

/-- The exact probability that the three sufficient counts equal a given triple,
for one category with mass p, propensity π and treated success rate μ: the
Poisson power/factorial coefficient times the exponential of minus the total
category intensity. -/
noncomputable def triplePoissonMass (sampleScale p pi mu : ℝ)
    (c : Fin 3 → ℕ) : ℝ :=
  Real.exp (-(sampleScale * p)) *
    triplePoissonCoefficient sampleScale p pi mu c

/-- The triple-count atom mass with its exponential factor replaced by the first
L terms of the exponential series.  Unlike the exact mass, this is a polynomial
in the observable intensities, so it is killed by moment matching. -/
noncomputable def triplePoissonTaylorMass (L : ℕ)
    (sampleScale p pi mu : ℝ) (c : Fin 3 → ℕ) : ℝ :=
  (∑ t ∈ Finset.range L,
      (-(sampleScale * p)) ^ t / (Nat.factorial t : ℝ)) *
    triplePoissonCoefficient sampleScale p pi mu c

/-- The single term of Taylor order t in the expansion of a triple-count atom
mass: the tth exponential-series coefficient of minus the category intensity
times the Poisson power/factorial coefficient. -/
noncomputable def triplePoissonTaylorTerm (t : ℕ)
    (sampleScale p pi mu : ℝ) (c : Fin 3 → ℕ) : ℝ :=
  (-(sampleScale * p)) ^ t / (Nat.factorial t : ℝ) *
    triplePoissonCoefficient sampleScale p pi mu c

/-- Evaluating the Taylor-term polynomial at the observable coordinates
(p, p·π, p·π·μ) returns exactly the corresponding Taylor term of the atom mass.
This is the bridge from analytic remainder control to polynomial moment
matching. -/
lemma triplePoissonTaylorPolynomial_eval (t : ℕ) (sampleScale p pi mu : ℝ)
    (c : Fin 3 → ℕ) :
    MvPolynomial.eval ![p, p * pi, p * pi * mu]
        (triplePoissonTaylorPolynomial t sampleScale c) =
      triplePoissonTaylorTerm t sampleScale p pi mu c := by
  have h10 : sampleScale * p * pi * (1 - mu) =
      sampleScale * (p * pi - p * pi * mu) := by ring
  have h0 : sampleScale * p * (1 - pi) =
      sampleScale * (p - p * pi) := by ring
  simp [triplePoissonTaylorPolynomial, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_sub, triplePoissonTaylorTerm, triplePoissonCoefficient]
  rw [h10, h0]
  simp only [mul_pow]
  ring

/-- The truncated atom mass is the sum of its individual Taylor terms of orders
0 through L−1. -/
lemma triplePoissonTaylorMass_eq_sum_terms (L : ℕ)
    (sampleScale p pi mu : ℝ) (c : Fin 3 → ℕ) :
    triplePoissonTaylorMass L sampleScale p pi mu c =
      ∑ t ∈ Finset.range L,
        triplePoissonTaylorTerm t sampleScale p pi mu c := by
  unfold triplePoissonTaylorMass triplePoissonTaylorTerm
  rw [Finset.sum_mul]

/-- The Poisson power/factorial coefficient of a count triple is nonnegative
whenever the sample scale and category mass are nonnegative and the propensity
and success rate lie in the unit interval. -/
lemma triplePoissonCoefficient_nonneg
    {sampleScale p pi mu : ℝ} (hs : 0 ≤ sampleScale) (hp : 0 ≤ p)
    (hpi : pi ∈ Set.Icc (0 : ℝ) 1) (hmu : mu ∈ Set.Icc (0 : ℝ) 1)
    (c : Fin 3 → ℕ) :
    0 ≤ triplePoissonCoefficient sampleScale p pi mu c := by
  unfold triplePoissonCoefficient
  have h11 : 0 ≤ sampleScale * p * pi * mu := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hs hp) hpi.1) hmu.1
  have h10 : 0 ≤ sampleScale * p * pi * (1 - mu) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hs hp) hpi.1) (sub_nonneg.mpr hmu.2)
  have h0 : 0 ≤ sampleScale * p * (1 - pi) := by
    exact mul_nonneg (mul_nonneg hs hp) (sub_nonneg.mpr hpi.2)
  positivity

/-- Truncating the exponential series at order L changes a triple-count atom mass
by at most the Poisson power/factorial coefficient times the positive
exponential-series tail of the category intensity from order L on. -/
lemma abs_triplePoissonMass_sub_taylor_le
    {sampleScale p pi mu : ℝ} (hs : 0 ≤ sampleScale) (hp : 0 ≤ p)
    (hpi : pi ∈ Set.Icc (0 : ℝ) 1) (hmu : mu ∈ Set.Icc (0 : ℝ) 1)
    (c : Fin 3 → ℕ) (L : ℕ) :
    |triplePoissonMass sampleScale p pi mu c -
        triplePoissonTaylorMass L sampleScale p pi mu c| ≤
      triplePoissonCoefficient sampleScale p pi mu c *
        expSeriesTail (sampleScale * p) L := by
  have hcoef := triplePoissonCoefficient_nonneg hs hp hpi hmu c
  have htail := abs_exp_neg_sub_taylor_le_tail
    (sampleScale * p) (mul_nonneg hs hp) L
  unfold triplePoissonMass triplePoissonTaylorMass
  rw [← sub_mul, abs_mul, abs_of_nonneg hcoef]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right htail hcoef

/-- Finite prior predictive mass of one triple-count atom. -/
noncomputable def mixedTriplePoissonMass
    {ι : Type*} [Fintype ι] (ω : PMF ι)
    (sampleScale : ℝ) (p pi mu : ι → ℝ) (c : Fin 3 → ℕ) : ℝ :=
  ∑ r, (ω r).toReal * triplePoissonMass sampleScale (p r) (pi r) (mu r) c

/-- Prior average of the Taylor-truncated triple-count atom masses over a finite
parameter prior — the polynomial surrogate of the prior predictive mass. -/
noncomputable def mixedTriplePoissonTaylorMass
    {ι : Type*} [Fintype ι] (ω : PMF ι) (L : ℕ)
    (sampleScale : ℝ) (p pi mu : ι → ℝ) (c : Fin 3 → ℕ) : ℝ :=
  ∑ r, (ω r).toReal * triplePoissonTaylorMass L sampleScale (p r) (pi r) (mu r) c

/-- The prior-averaged truncated mass is the sum over Taylor orders 0 through
L−1 of the prior-averaged individual Taylor terms, which is the form in which
moment matching is applied one order at a time. -/
lemma mixedTriplePoissonTaylorMass_eq_sum_terms
    {ι : Type*} [Fintype ι] (ω : PMF ι) (L : ℕ)
    (sampleScale : ℝ) (p pi mu : ι → ℝ) (c : Fin 3 → ℕ) :
    mixedTriplePoissonTaylorMass ω L sampleScale p pi mu c =
      ∑ t ∈ Finset.range L, ∑ r,
        (ω r).toReal * triplePoissonTaylorTerm t sampleScale (p r) (pi r) (mu r) c := by
  unfold mixedTriplePoissonTaylorMass
  simp_rw [triplePoissonTaylorMass_eq_sum_terms]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]

/-- Termwise moment cancellation implies equality of the truncated mixed
triple-Poisson predictive masses. -/
lemma mixedTriplePoissonTaylorMass_eq_of_termwise
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁) (L : ℕ) (sampleScale : ℝ)
    (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (c : Fin 3 → ℕ)
    (hterm : ∀ t < L,
      ∑ r, (ω₀ r).toReal *
          triplePoissonTaylorTerm t sampleScale (p₀ r) (pi₀ r) (mu₀ r) c =
        ∑ r, (ω₁ r).toReal *
          triplePoissonTaylorTerm t sampleScale (p₁ r) (pi₁ r) (mu₁ r) c) :
    mixedTriplePoissonTaylorMass ω₀ L sampleScale p₀ pi₀ mu₀ c =
      mixedTriplePoissonTaylorMass ω₁ L sampleScale p₁ pi₁ mu₁ c := by
  rw [mixedTriplePoissonTaylorMass_eq_sum_terms,
    mixedTriplePoissonTaylorMass_eq_sum_terms]
  apply Finset.sum_congr rfl
  intro t ht
  exact hterm t (Finset.mem_range.mp ht)

/-- Matching the raw monomials in `(p,p*pi,p*pi*mu)` through degree `D`
matches each Taylor term whose count-plus-Taylor degree is at most `D`. -/
lemma mixedTriplePoissonTaylorTerm_eq_of_moments
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁) (sampleScale : ℝ)
    (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ) (D t : ℕ)
    (c : Fin 3 → ℕ)
    (hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p₀ r ^ i * (p₀ r * pi₀ r) ^ j * (p₀ r * pi₀ r * mu₀ r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p₁ r ^ i * (p₁ r * pi₁ r) ^ j * (p₁ r * pi₁ r * mu₁ r) ^ k))
    (hdegree : t + c 0 + c 1 + c 2 ≤ D) :
    ∑ r, (ω₀ r).toReal *
        triplePoissonTaylorTerm t sampleScale (p₀ r) (pi₀ r) (mu₀ r) c =
      ∑ r, (ω₁ r).toReal *
        triplePoissonTaylorTerm t sampleScale (p₁ r) (pi₁ r) (mu₁ r) c := by
  let v₀ : ι₀ → Fin 3 → ℝ := fun r => ![p₀ r, p₀ r * pi₀ r, p₀ r * pi₀ r * mu₀ r]
  let v₁ : ι₁ → Fin 3 → ℝ := fun r => ![p₁ r, p₁ r * pi₁ r, p₁ r * pi₁ r * mu₁ r]
  have hsums (s : Fin 3 →₀ ℕ) :
      s.sum (fun _ e => e) = s 0 + s 1 + s 2 := by
    classical
    rw [Finsupp.sum_fintype]
    · rw [Fin.sum_univ_three]
    · intro i
      rfl
  have hm : ∀ s : Fin 3 →₀ ℕ, s.sum (fun _ e => e) ≤ D →
      ∑ r, (ω₀ r).toReal * ∏ q, v₀ r q ^ s q =
        ∑ r, (ω₁ r).toReal * ∏ q, v₁ r q ^ s q := by
    intro s hs
    simpa only [v₀, v₁, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_succ, Function.comp_apply, mul_assoc] using
      hmoment (s 0) (s 1) (s 2) (by simpa [hsums s] using hs)
  have hpoly := weighted_mvPolynomial_sum_eq_of_moments ω₀ ω₁ v₀ v₁ D hm
    (triplePoissonTaylorPolynomial t sampleScale c)
    ((triplePoissonTaylorPolynomial_totalDegree_le t sampleScale c).trans hdegree)
  simpa [v₀, v₁, triplePoissonTaylorPolynomial_eval] using hpoly

/-- Moment matching through degree `D` matches the complete Taylor-truncated
predictive atom whenever `L-1 + |c| ≤ D`. -/
lemma mixedTriplePoissonTaylorMass_eq_of_moments
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁) (sampleScale : ℝ)
    (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ) (D L : ℕ)
    (c : Fin 3 → ℕ)
    (hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p₀ r ^ i * (p₀ r * pi₀ r) ^ j * (p₀ r * pi₀ r * mu₀ r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p₁ r ^ i * (p₁ r * pi₁ r) ^ j * (p₁ r * pi₁ r * mu₁ r) ^ k))
    (hdegree : L + c 0 + c 1 + c 2 ≤ D + 1) :
    mixedTriplePoissonTaylorMass ω₀ L sampleScale p₀ pi₀ mu₀ c =
      mixedTriplePoissonTaylorMass ω₁ L sampleScale p₁ pi₁ mu₁ c := by
  apply mixedTriplePoissonTaylorMass_eq_of_termwise
  intro t ht
  apply mixedTriplePoissonTaylorTerm_eq_of_moments
    ω₀ ω₁ sampleScale p₀ pi₀ mu₀ p₁ pi₁ mu₁ D t c hmoment
  omega

/-- Averaging over the prior, the gap between the exact predictive mass of a
count triple and its Taylor-truncated surrogate is at most the prior average of
the per-parameter remainder bounds. -/
lemma abs_mixedTriplePoissonMass_sub_taylor_le
    {ι : Type*} [Fintype ι] (ω : PMF ι)
    {sampleScale : ℝ} (p pi mu : ι → ℝ)
    (hs : 0 ≤ sampleScale) (hp : ∀ r, 0 ≤ p r)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (c : Fin 3 → ℕ) (L : ℕ) :
    |mixedTriplePoissonMass ω sampleScale p pi mu c -
        mixedTriplePoissonTaylorMass ω L sampleScale p pi mu c| ≤
      ∑ r, (ω r).toReal *
        (triplePoissonCoefficient sampleScale (p r) (pi r) (mu r) c *
          expSeriesTail (sampleScale * p r) L) := by
  unfold mixedTriplePoissonMass mixedTriplePoissonTaylorMass
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro r _
  rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left
    (abs_triplePoissonMass_sub_taylor_le hs (hp r) (hpi r) (hmu r) c L)
    ENNReal.toReal_nonneg

/-- If all Taylor terms through degree `L-1` match, the mixed triple-Poisson
atom gap is bounded entirely by the two positive tails. -/
lemma abs_mixedTriplePoissonMass_sub_le_two_tails
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁)
    {sampleScale : ℝ} (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (hs : 0 ≤ sampleScale) (hp₀ : ∀ r, 0 ≤ p₀ r) (hp₁ : ∀ r, 0 ≤ p₁ r)
    (hpi₀ : ∀ r, pi₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hpi₁ : ∀ r, pi₁ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₀ : ∀ r, mu₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₁ : ∀ r, mu₁ r ∈ Set.Icc (0 : ℝ) 1)
    (c : Fin 3 → ℕ) (L : ℕ)
    (hmatch : mixedTriplePoissonTaylorMass ω₀ L sampleScale p₀ pi₀ mu₀ c =
      mixedTriplePoissonTaylorMass ω₁ L sampleScale p₁ pi₁ mu₁ c) :
    |mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c -
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c| ≤
      (∑ r, (ω₀ r).toReal *
        (triplePoissonCoefficient sampleScale (p₀ r) (pi₀ r) (mu₀ r) c *
          expSeriesTail (sampleScale * p₀ r) L)) +
      ∑ r, (ω₁ r).toReal *
        (triplePoissonCoefficient sampleScale (p₁ r) (pi₁ r) (mu₁ r) c *
          expSeriesTail (sampleScale * p₁ r) L) := by
  let M₀ := mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c
  let M₁ := mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c
  let T := mixedTriplePoissonTaylorMass ω₀ L sampleScale p₀ pi₀ mu₀ c
  have h0 := abs_mixedTriplePoissonMass_sub_taylor_le
    ω₀ p₀ pi₀ mu₀ hs hp₀ hpi₀ hmu₀ c L
  have h1 := abs_mixedTriplePoissonMass_sub_taylor_le
    ω₁ p₁ pi₁ mu₁ hs hp₁ hpi₁ hmu₁ c L
  rw [← hmatch] at h1
  change |M₀ - M₁| ≤ _
  exact (abs_sub_le M₀ T M₁).trans (add_le_add h0 (by simpa [abs_sub_comm] using h1))

/-- Fully assembled one-atom C.5 bound: matched observable moments eliminate
the Taylor polynomial, leaving only the two positive exponential tails. -/
lemma abs_mixedTriplePoissonMass_sub_le_two_tails_of_moments
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁)
    {sampleScale : ℝ} (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (hs : 0 ≤ sampleScale) (hp₀ : ∀ r, 0 ≤ p₀ r) (hp₁ : ∀ r, 0 ≤ p₁ r)
    (hpi₀ : ∀ r, pi₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hpi₁ : ∀ r, pi₁ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₀ : ∀ r, mu₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₁ : ∀ r, mu₁ r ∈ Set.Icc (0 : ℝ) 1)
    (D L : ℕ) (c : Fin 3 → ℕ)
    (hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p₀ r ^ i * (p₀ r * pi₀ r) ^ j * (p₀ r * pi₀ r * mu₀ r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p₁ r ^ i * (p₁ r * pi₁ r) ^ j * (p₁ r * pi₁ r * mu₁ r) ^ k))
    (hdegree : L + c 0 + c 1 + c 2 ≤ D + 1) :
    |mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c -
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c| ≤
      (∑ r, (ω₀ r).toReal *
        (triplePoissonCoefficient sampleScale (p₀ r) (pi₀ r) (mu₀ r) c *
          expSeriesTail (sampleScale * p₀ r) L)) +
      ∑ r, (ω₁ r).toReal *
        (triplePoissonCoefficient sampleScale (p₁ r) (pi₁ r) (mu₁ r) c *
          expSeriesTail (sampleScale * p₁ r) L) := by
  apply abs_mixedTriplePoissonMass_sub_le_two_tails
    ω₀ ω₁ p₀ pi₀ mu₀ p₁ pi₁ mu₁ hs hp₀ hp₁ hpi₀ hpi₁ hmu₀ hmu₁
  exact mixedTriplePoissonTaylorMass_eq_of_moments
    ω₀ ω₁ sampleScale p₀ pi₀ mu₀ p₁ pi₁ mu₁ D L c hmoment hdegree

/-- Summed finite-count version of the C.5 remainder bound.  The truncation
order may depend on the count atom, which is needed for total-degree matching. -/
lemma sum_abs_mixedTriplePoissonMass_sub_le_two_tails_of_moments
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁)
    {sampleScale : ℝ} (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (hs : 0 ≤ sampleScale) (hp₀ : ∀ r, 0 ≤ p₀ r) (hp₁ : ∀ r, 0 ≤ p₁ r)
    (hpi₀ : ∀ r, pi₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hpi₁ : ∀ r, pi₁ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₀ : ∀ r, mu₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₁ : ∀ r, mu₁ r ∈ Set.Icc (0 : ℝ) 1)
    (D : ℕ) (S : Finset (Fin 3 → ℕ)) (L : (Fin 3 → ℕ) → ℕ)
    (hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p₀ r ^ i * (p₀ r * pi₀ r) ^ j * (p₀ r * pi₀ r * mu₀ r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p₁ r ^ i * (p₁ r * pi₁ r) ^ j * (p₁ r * pi₁ r * mu₁ r) ^ k))
    (hdegree : ∀ c ∈ S, L c + c 0 + c 1 + c 2 ≤ D + 1) :
    ∑ c ∈ S, |mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c -
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c| ≤
      (∑ r, (ω₀ r).toReal * ∑ c ∈ S,
        triplePoissonCoefficient sampleScale (p₀ r) (pi₀ r) (mu₀ r) c *
          expSeriesTail (sampleScale * p₀ r) (L c)) +
      ∑ r, (ω₁ r).toReal * ∑ c ∈ S,
        triplePoissonCoefficient sampleScale (p₁ r) (pi₁ r) (mu₁ r) c *
          expSeriesTail (sampleScale * p₁ r) (L c) := by
  calc
    _ ≤ ∑ c ∈ S,
        ((∑ r, (ω₀ r).toReal *
          (triplePoissonCoefficient sampleScale (p₀ r) (pi₀ r) (mu₀ r) c *
            expSeriesTail (sampleScale * p₀ r) (L c))) +
        ∑ r, (ω₁ r).toReal *
          (triplePoissonCoefficient sampleScale (p₁ r) (pi₁ r) (mu₁ r) c *
            expSeriesTail (sampleScale * p₁ r) (L c))) := by
      apply Finset.sum_le_sum
      intro c hc
      exact abs_mixedTriplePoissonMass_sub_le_two_tails_of_moments
        ω₀ ω₁ p₀ pi₀ mu₀ p₁ pi₁ mu₁ hs hp₀ hp₁ hpi₀ hpi₁ hmu₀ hmu₁
        D (L c) c hmoment (hdegree c hc)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1 <;>
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
