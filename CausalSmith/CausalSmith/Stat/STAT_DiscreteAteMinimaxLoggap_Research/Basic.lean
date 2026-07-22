/-
# Discrete-confounder ATE minimax model

This file is the shared, finite-alphabet substrate for the paper.  The nearby
`Causalean.Estimation.MinimaxATE.Model` is deliberately not reused for the law:
that model fixes a uniform covariate marginal, whereas rare, arbitrary cell
masses are essential here.  We do reuse the general `IIDSample`/finite-product
transport.  The potential-outcome overlay below is finite and binary, so the
general regime-indexed PO API would be a different abstraction (`bypass-justified`).
-/

import Causalean.Stat.Sample
import Causalean.Stat.Sample.PiTransport
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Defines Cell, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
abbrev Cell := Fin 2 × Fin 2

/-- One observed unit `(X,A,Y)`. -/
abbrev Obs (d : ℕ) := Fin d × Bool × Bool

/-- A probability law with arbitrary masses on the finite observation alphabet. -/
structure DiscreteLaw (d : ℕ) where
  pmf : PMF (Obs d) -- @realizes P(probability law on Fin d × Bool × Bool)

/-- The measure associated with a finite law. -/
noncomputable def obsLaw {d : ℕ} (P : DiscreteLaw d) : Measure (Obs d) :=
  P.pmf.toMeasure

instance {d : ℕ} (P : DiscreteLaw d) : IsProbabilityMeasure (obsLaw P) := by
  unfold obsLaw
  infer_instance

/-- The mass of one `(k,a,y)` atom. -/
noncomputable def jointMass {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a y : Bool) : ℝ :=
  (P.pmf (k, a, y)).toReal
  -- @realizes q_{aky}(P(X=k,A=a,Y=y); range [0,1])

lemma jointMass_mem_unitInterval {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a y : Bool) : jointMass P k a y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_le_coe_of_le_coe (P.pmf.coe_le_one (k, a, y))
  -- @realizes q_{aky}(joint atom mass lies in [0,1])

/-- The four masses in category `k`, indexed by `(A,Y)`. -/
noncomputable def cellVector {d : ℕ} (P : DiscreteLaw d) (k : Fin d) : Cell → ℝ :=
  fun ay => jointMass P k (finTwoEquiv ay.1) (finTwoEquiv ay.2)
  -- @realizes q_k(four-vector ordered by (A,Y))

lemma cellVector_mem_unitCube {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    ∀ ay, cellVector P k ay ∈ Set.Icc (0 : ℝ) 1 := by
  intro ay
  exact jointMass_mem_unitInterval P k (finTwoEquiv ay.1) (finTwoEquiv ay.2)
  -- @realizes q_k(four-vector lies in [0,1]^4)

/-- Marginal mass `P(X=k)`. -/
noncomputable def cellMass {d : ℕ} (P : DiscreteLaw d) (k : Fin d) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, jointMass P k a y
  -- @realizes p_k(P(X=k); range [0,1])

lemma cellMass_mem_unitInterval {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    cellMass P k ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ cellMass P k := by
    unfold cellMass
    exact Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P k a y).1
  have hsum : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
    simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  constructor
  · exact hnonneg
  · calc
      cellMass P k ≤ ∑ k' : Fin d, cellMass P k' := by
        exact Finset.single_le_sum
          (fun i _ => by
            unfold cellMass
            exact Finset.sum_nonneg fun a _ =>
              Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P i a y).1)
          (Finset.mem_univ k)
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := hsum
  -- @realizes p_k(category mass lies in [0,1])

/-- Joint mass `P(X=k,A=a)`. -/
noncomputable def armMass {d : ℕ} (P : DiscreteLaw d) (k : Fin d) (a : Bool) : ℝ :=
  ∑ y : Bool, jointMass P k a y

/-- Propensity, with Lean's total division convention on zero-mass cells. -/
noncomputable def propensity {d : ℕ} (P : DiscreteLaw d) (k : Fin d) : ℝ :=
  armMass P k true / cellMass P k
  -- @realizes pi_k(P(A=1|X=k); constrained on positive cells by Overlap)

lemma propensity_mem_unitInterval {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    propensity P k ∈ Set.Icc (0 : ℝ) 1 := by
  have harm_nonneg : 0 ≤ armMass P k true := by
    unfold armMass
    exact Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P k true y).1
  have hmass_nonneg : 0 ≤ cellMass P k := (cellMass_mem_unitInterval P k).1
  have harm_le : armMass P k true ≤ cellMass P k := by
    simp [armMass, cellMass]
    have hfalse0 := (jointMass_mem_unitInterval P k false false).1
    have hfalse1 := (jointMass_mem_unitInterval P k false true).1
    linarith
  constructor
  · exact div_nonneg harm_nonneg hmass_nonneg
  · exact div_le_one_of_le₀ harm_le hmass_nonneg
  -- @realizes pi_k(propensity lies in [0,1])

/-- Binary outcome regression, again totalized on empty arm-cells. -/
noncomputable def outcomeMean {d : ℕ} (P : DiscreteLaw d)
    (a : Bool) (k : Fin d) : ℝ :=
  jointMass P k a true / armMass P k a
  -- @realizes mu_{ak}(E[Y|A=a,X=k]; range [0,1] on positive arm-cells)

lemma outcomeMean_mem_unitInterval {d : ℕ} (P : DiscreteLaw d)
    (a : Bool) (k : Fin d) : outcomeMean P a k ∈ Set.Icc (0 : ℝ) 1 := by
  have hj_nonneg : 0 ≤ jointMass P k a true :=
    (jointMass_mem_unitInterval P k a true).1
  have harm_nonneg : 0 ≤ armMass P k a := by
    unfold armMass
    exact Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P k a y).1
  have hj_le : jointMass P k a true ≤ armMass P k a := by
    simp [armMass]
    exact (jointMass_mem_unitInterval P k a false).1
  constructor
  · exact div_nonneg hj_nonneg harm_nonneg
  · exact div_le_one_of_le₀ hj_le harm_nonneg
  -- @realizes mu_{ak}(binary conditional mean lies in [0,1])

/-- Canonical finite i.i.d. product law. -/
noncomputable def productLaw {d : ℕ} (P : DiscreteLaw d) (n : ℕ) :
    Measure (Fin n → Obs d) :=
  Measure.pi (fun _ : Fin n => obsLaw P)
  -- @realizes O_i(i in Fin n; O_i=(X_i,A_i,Y_i))

instance {d n : ℕ} (P : DiscreteLaw d) : IsProbabilityMeasure (productLaw P n) := by
  unfold productLaw
  infer_instance

-- @env: S1
variable (n d : ℕ) -- @realizes n(sample size in Nat) @realizes d(alphabet size in Nat)
variable (epsilon c : ℝ)
  -- @realizes epsilon(overlap constant; range imposed by theorem hypotheses)
  -- @realizes c(positive range constant)
variable (k : Fin d) -- @realizes k(category index in Fin d)
variable (P : DiscreteLaw d)
variable (sample : Fin n → Obs d)
  -- @realizes X(first coordinate in Fin d)
  -- @realizes A(second coordinate in Bool)
  -- @realizes Y(third coordinate in Bool)

/-- The ambient infinite sample pushes forward to the canonical finite product. -/
lemma finProductLaw_eq_map {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => P)).map
        (fun ω : ℕ → X => fun i : Fin n => ω i) =
      Measure.pi (fun _ : Fin n => P) := by
  exact Causalean.Stat.iidSample_finN_pushforward
    (Causalean.Stat.iidSample_infinitePi P) n

-- @node: ass:iid-sampling
/-- The observed sample law is the `n`-fold product of the one-unit law. -/
def IidSampling {d n : ℕ} (P : DiscreteLaw d)
    (mu_n : Measure (Fin n → Obs d)) : Prop :=
  mu_n = productLaw P n

-- @node: ass:overlap
/-- Positive-mass categories have propensity in `[epsilon,1-epsilon]`. -/
def Overlap {d : ℕ} (epsilon : ℝ) (P : DiscreteLaw d) : Prop :=
  ∀ k, 0 < cellMass P k →
    epsilon ≤ propensity P k ∧ propensity P k ≤ 1 - epsilon
    -- @realizes epsilon(0 < epsilon ≤ 1/2 supplied by consumers)
    -- @realizes pi_k(propensity constrained to [epsilon,1-epsilon])
    -- @realizes p_k(constraint applies when p_k>0)

/-- Full-data atom `(X,A,Y,Y(0),Y(1))`. -/
abbrev FullObs (d : ℕ) := Fin d × Bool × Bool × Bool × Bool

/-- Finite potential-outcome overlay used only by the causal witness. -/
structure PotentialLaw (d : ℕ) where
  pmf : PMF (FullObs d)
  -- @realizes Y(a)(binary potential outcomes carried in the last two coordinates)

noncomputable def fullMass {d : ℕ} (Q : PotentialLaw d)
    (z : FullObs d) : ℝ := (Q.pmf z).toReal

-- @node: ass:consistency
/-- `Y=Y(A)` almost surely, written as zero mass on inconsistent atoms. -/
def Consistency {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) → fullMass Q z = 0
  -- @realizes Y(observed outcome equals selected potential outcome)
  -- @realizes A(selects Y(0) or Y(1))
  -- @realizes Y(a)(potential outcome indexed by treatment)

/-- Conditional atom mass for `(Y(0),Y(1),A,X)`. -/
noncomputable def poAtom {d : ℕ} (Q : PotentialLaw d)
    (k : Fin d) (a y0 y1 : Bool) : ℝ :=
  ∑ y : Bool, fullMass Q (k, a, y, y0, y1)

-- @node: ass:conditional-exchangeability
/-- Finite conditional-independence identity `(Y(0),Y(1)) ⟂ A | X`. -/
def ConditionalExchangeability {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ k a y0 y1,
    poAtom Q k a y0 y1 *
        (∑ a' : Bool, ∑ y0' : Bool, ∑ y1' : Bool, poAtom Q k a' y0' y1') =
      (∑ a' : Bool, poAtom Q k a' y0 y1) *
        (∑ y0' : Bool, ∑ y1' : Bool, poAtom Q k a y0' y1')
  -- @realizes Y(a)(potential-outcome pair in conditional independence)
  -- @realizes A(treatment in conditional independence)
  -- @realizes X(conditioning category)

-- @node: def:experiment-class
/-- Membership of a sample law in the unrestricted overlap experiment class. -/
structure ExperimentClass (n : ℕ) {d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (mu_n : Measure (Fin n → Obs d)) : Prop where
  epsilon_pos : 0 < epsilon
    -- @realizes epsilon(strictly positive overlap constant)
  epsilon_le_half : epsilon ≤ 1 / 2
    -- @realizes epsilon(overlap constant at most 1/2)
  product_law : IidSampling P mu_n
    -- @realizes \mathcal E_{n,d,\epsilon}(member law is productLaw P n)
    -- @realizes O_i(i.i.d. observations governed by the product law)
  overlap : Overlap epsilon P
    -- @realizes \mathcal E_{n,d,\epsilon}(base law satisfies overlap)

/-- Four-cell arm mass. -/
def vectorArmMass (u : Cell → ℝ) (a : Fin 2) : ℝ :=
  u (a, 0) + u (a, 1)

/-- Total four-cell mass. -/
def vectorMass (u : Cell → ℝ) : ℝ :=
  vectorArmMass u 0 + vectorArmMass u 1

-- @node: def:overlap-cone
/-- The nonnegative four-cell cone with treatment mass in the overlap band. -/
def overlapCone (epsilon : ℝ) : Set (Cell → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧
    epsilon * vectorMass u ≤ vectorArmMass u 1 ∧
    vectorArmMass u 1 ≤ (1 - epsilon) * vectorMass u}
  -- @realizes \mathcal C_\epsilon(nonnegative overlap-restricted four-cell cone)

/-- Total arithmetic extension of the homogeneous four-cell contribution.
The paper-facing functional is `cellPhiOnCone` below. -/
noncomputable def cellPhi (u : Cell → ℝ) : ℝ :=
  if u = 0 then 0
  else vectorMass u *
    (u (1, 1) / vectorArmMass u 1 - u (0, 1) / vectorArmMass u 0)

-- @node: def:cell-functional
/-- The homogeneous four-cell ATE contribution on its stated overlap-cone domain. -/
noncomputable def cellPhiOnCone (epsilon : ℝ) (u : overlapCone epsilon) : ℝ :=
  cellPhi u.1
  -- @realizes \phi(homogeneous four-cell ATE contribution)

@[simp] lemma cellPhiOnCone_apply (epsilon : ℝ) (u : overlapCone epsilon) :
    cellPhiOnCone epsilon u = cellPhi u.1 := rfl

/-- The observed-data ATE functional `sum_k phi(q_k)`. -/
-- @node: def:ate-functional
noncomputable def ateFunctional {d : ℕ} (P : DiscreteLaw d) : ℝ :=
  ∑ k : Fin d, cellPhi (cellVector P k)
  -- @realizes \tau(P)(sum of cell contributions; range [-1,1] on valid laws)

/-- The equivalent weighted-regression formula under overlap. -/
lemma ateFunctional_eq_weighted_regression {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (h : Overlap epsilon P) :
    ateFunctional P =
      ∑ k : Fin d, cellMass P k * (outcomeMean P true k - outcomeMean P false k) := by
  classical
  apply Finset.sum_congr rfl
  intro k _
  by_cases hz : cellVector P k = 0
  · have h00 := congrFun hz (0, 0)
    have h01 := congrFun hz (0, 1)
    have h10 := congrFun hz (1, 0)
    have h11 := congrFun hz (1, 1)
    simp [cellVector, finTwoEquiv] at h00 h01 h10 h11
    simp [cellPhi, hz, cellMass, outcomeMean, armMass, h00, h01, h10, h11]
  · simp [cellPhi, hz, cellVector, vectorMass, vectorArmMass, cellMass,
      outcomeMean, armMass, finTwoEquiv]
    <;> ring

/-- Shows that ate Functional mem interval lies in the stated set or interval. -/
lemma ateFunctional_mem_interval {d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (h : Overlap epsilon P) : ateFunctional P ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ateFunctional_eq_weighted_regression P h]
  have hsum : ∑ k : Fin d, cellMass P k = 1 := by
    have htotal : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
      simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
    calc
      ∑ k : Fin d, cellMass P k = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := htotal
  have habs :
      |∑ k : Fin d, cellMass P k *
          (outcomeMean P true k - outcomeMean P false k)| ≤ 1 := by
    calc
      |∑ k : Fin d, cellMass P k *
          (outcomeMean P true k - outcomeMean P false k)| ≤
          ∑ k : Fin d, |cellMass P k *
            (outcomeMean P true k - outcomeMean P false k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin d, cellMass P k := by
        apply Finset.sum_le_sum
        intro k _
        have hp := cellMass_mem_unitInterval P k
        have hm1 := outcomeMean_mem_unitInterval P true k
        have hm0 := outcomeMean_mem_unitInterval P false k
        rcases hm1 with ⟨hm1lo, hm1hi⟩
        rcases hm0 with ⟨hm0lo, hm0hi⟩
        rw [abs_mul, abs_of_nonneg hp.1]
        have hdiff : |outcomeMean P true k - outcomeMean P false k| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        exact mul_le_of_le_one_right hp.1 hdiff
      _ = 1 := hsum
  exact abs_le.mp habs
  -- @realizes \tau(P)(ATE functional lies in [-1,1])

/-- Mean squared error under a supplied sample law. -/
-- @realizes \(\mathsf R_{n,d,\epsilon}\)(expected squared loss under the product law)
noncomputable def mse {d n : ℕ} (mu_n : Measure (Fin n → Obs d))
    (est : (Fin n → Obs d) → ℝ) (target : ℝ) : ℝ :=
  ∫ x, (est x - target) ^ 2 ∂mu_n

-- @env: S3
variable (n d : ℕ) (epsilon : ℝ)
/-- A law packaged with overlap-class membership. -/
def ClassLaw (n d : ℕ) (epsilon : ℝ) :=
  {P : DiscreteLaw d // ExperimentClass n epsilon P (productLaw P n)}

/-- Worst-case MSE of one measurable estimator over the experiment class. -/
-- @realizes \(\mathsf R_{n,d,\epsilon}\)(supremum over the overlap experiment class)
noncomputable def worstCaseMSE (n d : ℕ) (epsilon : ℝ)
    (est : (Fin n → Obs d) → ℝ) : ℝ :=
  ⨆ P : ClassLaw n d epsilon, mse (productLaw P.1 n) est (ateFunctional P.1)

/-- Infimum, over measurable estimators, of their worst-case product-law MSE. -/
-- @realizes \(\mathsf R_{n,d,\epsilon}\)(infimum measurable estimator worst-case MSE)
-- @node: def:minimax-risk
noncomputable def minimaxRisk (n d : ℕ) (epsilon : ℝ) : ℝ :=
  ⨅ est : {f : (Fin n → Obs d) → ℝ // Measurable f},
    worstCaseMSE n d epsilon est.1

-- @realizes \(\mathsf R_{n,d,\epsilon}\)(minimax risk intrinsically lies in [0,1])
lemma minimaxRisk_mem_unitInterval (n d : ℕ) (epsilon : ℝ) :
    minimaxRisk n d epsilon ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonneg (est : {f : (Fin n → Obs d) → ℝ // Measurable f}) :
      0 ≤ worstCaseMSE n d epsilon est.1 := by
    unfold worstCaseMSE
    cases isEmpty_or_nonempty (ClassLaw n d epsilon) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        by_cases hbounded : BddAbove (Set.range (fun P : ClassLaw n d epsilon =>
            mse (productLaw P.1 n) est (ateFunctional P.1)))
        · have hmse : 0 ≤ mse
              (productLaw (Classical.arbitrary (ClassLaw n d epsilon)).1 n)
              est (ateFunctional (Classical.arbitrary (ClassLaw n d epsilon)).1) := by
            unfold mse
            exact integral_nonneg (fun x => sq_nonneg
              (est.1 x - ateFunctional (Classical.arbitrary (ClassLaw n d epsilon)).1))
          exact hmse.trans (le_ciSup hbounded (Classical.arbitrary _))
        · change 0 ≤ (⨆ P : ClassLaw n d epsilon,
              mse (productLaw P.1 n) est.1 (ateFunctional P.1))
          rw [show (⨆ P : ClassLaw n d epsilon,
              mse (productLaw P.1 n) est.1 (ateFunctional P.1)) = sSup ∅ from
              csSup_of_not_bddAbove hbounded]
          simp
  have hb : BddBelow (Set.range (fun est :
      {f : (Fin n → Obs d) → ℝ // Measurable f} =>
        worstCaseMSE n d epsilon est.1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact hnonneg est
  letI : Nonempty {f : (Fin n → Obs d) → ℝ // Measurable f} :=
    ⟨⟨fun _ => 0, measurable_const⟩⟩
  constructor
  · apply le_ciInf
    intro est
    exact hnonneg est
  · have hzero : Measurable (fun _ : Fin n → Obs d => (0 : ℝ)) := measurable_const
    refine (ciInf_le hb ⟨fun _ => 0, hzero⟩).trans ?_
    unfold worstCaseMSE
    cases isEmpty_or_nonempty (ClassLaw n d epsilon) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        apply ciSup_le
        intro P
        have ht := ateFunctional_mem_interval P.1 P.2.overlap
        have hs : ateFunctional P.1 ^ 2 ≤ 1 := by
          rw [sq_le_one_iff_abs_le_one]
          exact abs_le.mpr ht
        simpa [mse] using hs

/-- Observed marginal of a full-data law. -/
noncomputable def observedMarginal {d : ℕ} (Q : PotentialLaw d) : DiscreteLaw d where
  pmf := Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))

/-- Unnormalized explicit witness mass. -/
noncomputable def twoCategoryMass (epsilon : ℝ) (z : FullObs 2) : ℝ :=
  let xFirst : Bool := z.1 = 0
  let y0 : Bool := false
  let y1 : Bool := xFirst
  let propensityWeight : ℝ :=
    if z.2.1 then (if xFirst then epsilon else 1 - epsilon)
    else (if xFirst then 1 - epsilon else epsilon)
  if z.2.2.2.1 = y0 ∧ z.2.2.2.2 = y1 ∧
      z.2.2.1 = (if z.2.1 then y1 else y0) then
    (1 / 2 : ℝ) * propensityWeight
  else 0

lemma twoCategoryMass_nonneg (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (z : FullObs 2) : 0 ≤ twoCategoryMass epsilon z := by
  simp only [twoCategoryMass]
  split_ifs <;> nlinarith

/-- Establishes the stated summation identity or bound for two Category Mass sum. -/
lemma twoCategoryMass_sum (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∑ z : FullObs 2, ENNReal.ofReal (twoCategoryMass epsilon z) = 1 := by
  classical
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, twoCategoryMass]
  have he : ENNReal.ofReal epsilon + ENNReal.ofReal (1 - epsilon) = 1 := by
    rw [← ENNReal.ofReal_add h0 (sub_nonneg.mpr h1)]
    norm_num
  calc
    2⁻¹ * ENNReal.ofReal epsilon + 2⁻¹ * ENNReal.ofReal (1 - epsilon) +
          (2⁻¹ * ENNReal.ofReal (1 - epsilon) + 2⁻¹ * ENNReal.ofReal epsilon) =
        2⁻¹ * (ENNReal.ofReal epsilon + ENNReal.ofReal (1 - epsilon)) +
          2⁻¹ * (ENNReal.ofReal epsilon + ENNReal.ofReal (1 - epsilon)) := by ring
    _ = 1 := by rw [he, mul_one]; exact ENNReal.inv_two_add_inv_two

-- @node: def:two-category-witness
/-- Explicit two-category confounding witness with `p=(1/2,1/2)` and
propensities `(epsilon,1-epsilon)`. -/
noncomputable def twoCategoryWitness (epsilon : ℝ) (h0 : 0 ≤ epsilon)
    (h1 : epsilon ≤ 1) : PotentialLaw 2 where
  pmf := PMF.ofFintype (fun z => ENNReal.ofReal (twoCategoryMass epsilon z))
    (twoCategoryMass_sum epsilon h0 h1)
  -- @realizes p_k(p_1=p_2=1/2)
  -- @realizes pi_k(pi_1=epsilon, pi_2=1-epsilon)
  -- @realizes mu_{ak}(mu_0k=0, mu_11=1, mu_12=0)
  -- @realizes X(binary category in Fin 2)
  -- @realizes A(Bernoulli propensity conditional on X)
  -- @realizes Y(a)(Y(0)=0 and Y(1)=1{X=1})

/-- Naive observed treated-minus-control contrast. -/
noncomputable def naiveContrast {d : ℕ} (P : DiscreteLaw d) : ℝ :=
  let treated := ∑ k : Fin d, jointMass P k true true
  let control := ∑ k : Fin d, jointMass P k false true
  let pT := ∑ k : Fin d, armMass P k true
  let pC := ∑ k : Fin d, armMass P k false
  treated / pT - control / pC

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
