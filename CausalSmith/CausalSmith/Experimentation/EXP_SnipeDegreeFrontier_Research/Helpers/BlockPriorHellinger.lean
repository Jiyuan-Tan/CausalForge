import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.HellingerAffinity
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourableProperties
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import Causalean.Experimentation.DesignBased.ProductMeasure
import Mathlib.Probability.ProductMeasure

/-!
# Hellinger control for the continuous block prior
-/

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat

/-- Expectation under an identical-coordinate product design is invariant
under a bijective relabeling of the coordinate type. -/
lemma FiniteDesign.E_prod_equiv
    {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
    [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (D : FiniteDesign W) (g : (κ → W) → ℝ) :
    (prodDesign (fun _ : ι => D)).E
        (fun z => g (fun k => z (e k))) =
      (prodDesign (fun _ : κ => D)).E g := by
  classical
  let q : (κ → W) ≃ (ι → W) :=
    Equiv.arrowCongr e (Equiv.refl W)
  simp only [FiniteDesign.E, prodDesign_p]
  rw [← Equiv.sum_comp q]
  apply Finset.sum_congr rfl
  intro w hw
  have hq (i : ι) : q w i = w (e.symm i) := by
    simp [q, Equiv.arrowCongr]
  have harg : (fun k => q w (e k)) = w := by
    funext k
    rw [hq, e.symm_apply_apply]
  have hprod :
      (∏ i : ι, D.p (q w i)) = ∏ k : κ, D.p (w k) := by
    rw [← Equiv.prod_comp e (fun i : ι => D.p (q w i))]
    apply Finset.prod_congr rfl
    intro k hk
    rw [hq, e.symm_apply_apply]
  rw [harg, hprod]

/-- The global Bernoulli expectation of a function of one active block is
the corresponding `d`-coordinate block expectation. -/
lemma E_blockAssignment
    (n d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Fin (blockCount n d)) (g : (Fin d → Bool) → ℝ) :
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
      (fun _ => hp1)).E
        (fun z => g (blockAssignment n d b z)) =
      (blockDesign d p hp0 hp1).E g := by
  classical
  let emb : Fin d → Fin n := fun k =>
    ⟨b.val * d + k.val, by
      have hb : b.val < n / d := by simpa [blockCount] using b.isLt
      calc
        b.val * d + k.val < b.val * d + d :=
          Nat.add_lt_add_left k.isLt _
        _ = (b.val + 1) * d := by simp [Nat.add_mul]
        _ ≤ (n / d) * d := Nat.mul_le_mul_right d hb
        _ ≤ n := Nat.div_mul_le_self n d⟩
  have hemb : Function.Injective emb := by
    intro k l hkl
    apply Fin.ext
    have := congrArg Fin.val hkl
    dsimp [emb] at this
    omega
  let S : Finset (Fin n) := Finset.univ.image emb
  let e : Fin d ≃ ↥S :=
    Equiv.ofBijective
      (fun k => (⟨emb k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩ :
        ↥S))
      ⟨by
        intro k l h
        exact hemb (congrArg Subtype.val h),
       by
        intro j
        obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp j.property
        refine ⟨k, ?_⟩
        apply Subtype.ext
        exact hkj⟩
  let Dc : FiniteDesign Bool := coinDesign p hp0 hp1
  let Dn : FiniteDesign (Fin n → Bool) :=
    bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0) (fun _ => hp1)
  have hrestrict (z : Fin n → Bool) :
      blockAssignment n d b z =
        fun k => (S.restrict z) (e k) := by
    funext k
    rfl
  rw [show
      (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
        (fun _ => hp1)).E
          (fun z => g (blockAssignment n d b z)) =
        ∫ z, g (blockAssignment n d b z) ∂Dn.toMeasure by
      exact (Dn.integral_toMeasure _).symm]
  rw [show Dn.toMeasure =
      Measure.pi (fun _ : Fin n => Dc.toMeasure) by
    exact prodDesign_toMeasure_eq_pi (fun _ : Fin n => Dc)]
  rw [← Measure.infinitePi_eq_pi]
  rw [show (fun z : Fin n → Bool => g (blockAssignment n d b z)) =
      (fun z => (fun w : ↥S → Bool => g (fun k => w (e k)))
        (S.restrict z)) by
    funext z
    rw [hrestrict]]
  have hr := MeasureTheory.integral_restrict_infinitePi
    (fun _ : Fin n => Dc.toMeasure)
    (s := S) (f := fun w : ↥S → Bool => g (fun k => w (e k)))
    (measurable_of_finite _).aestronglyMeasurable
  rw [hr]
  · rw [← prodDesign_toMeasure_eq_pi (fun _ : ↥S => Dc)]
    rw [FiniteDesign.integral_toMeasure]
    exact FiniteDesign.E_prod_equiv e Dc g

private lemma cosSqDensity_nonneg
    (s : ℝ) (hs : 0 < s) (u : ℝ) :
    0 ≤ cosSqDensity s u := by
  unfold cosSqDensity
  split_ifs
  · positivity
  · norm_num

/-- Establishes the stated mathematical result for block prior density nonneg. -/
lemma blockPriorDensity_nonneg
    (n d β : ℕ) (B p σ : ℝ)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ blockPriorDensity n d β B p σ := by
  intro x
  unfold blockPriorDensity assignmentMass
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> linarith
  · apply Finset.prod_nonneg
    intro b hb
    exact cosSqDensity_nonneg (B / 2) (by linarith) _

set_option maxHeartbeats 800000 in
/-- Establishes the stated mathematical result for block prior density integrable. -/
lemma blockPriorDensity_integrable
    (n d β : ℕ) (B p σ : ℝ)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1) :
    Integrable (blockPriorDensity n d β B p σ)
      (blockDominatingMeasure n d) := by
  classical
  let shift : (Fin n → Bool) → Fin (blockCount n d) → ℝ :=
    fun z b => σ * tiltAmplitude B β p (blockCount n d) d *
      blockRepresenter β p d (blockAssignment n d b z)
  have hinner (z : Fin n → Bool) :
      Integrable
        (fun y : Fin (blockCount n d) → ℝ =>
          blockPriorDensity n d β B p σ (z, y))
        (Measure.pi (fun _ : Fin (blockCount n d) => volume)) := by
    change Integrable (fun y =>
      assignmentMass n p z *
        ∏ b, cosSqDensity (B / 2) (y b - shift z b))
      (Measure.pi (fun _ : Fin (blockCount n d) => volume))
    exact (Integrable.fintype_prod fun b =>
      cosSqDensity_translate_integrable (B / 2) (shift z b)).const_mul _
  have hmeas :
      AEStronglyMeasurable (blockPriorDensity n d β B p σ)
        (blockDominatingMeasure n d) := by
    apply Measurable.aestronglyMeasurable
    unfold blockPriorDensity
    apply Measurable.mul
    · exact (measurable_of_finite
        (assignmentMass n p)).comp measurable_fst
    · apply Finset.measurable_prod
      intro b hb
      apply (cosSqDensity_measurable (B / 2)).comp
      apply Measurable.sub
      · exact (measurable_pi_apply b).comp measurable_snd
      · exact (measurable_of_finite (fun z : Fin n → Bool =>
          shift z b)).comp measurable_fst
  rw [blockDominatingMeasure] at hmeas ⊢
  rw [integrable_prod_iff hmeas]
  exact ⟨Filter.Eventually.of_forall hinner, Integrable.of_finite⟩

/-- For normalized nonnegative coordinate densities, the squared Hellinger
integral of their finite products is twice the product-affinity defect. -/
lemma hellingerSqDensity_pi_eq_two_mul_one_sub_affinity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ → ℝ)
    (hf0 : ∀ i u, 0 ≤ f i u) (hg0 : ∀ i u, 0 ≤ g i u)
    (hfint : ∀ i, Integrable (f i) volume)
    (hgint : ∀ i, Integrable (g i) volume)
    (hf1 : ∀ i, ∫ u, f i u = 1)
    (hg1 : ∀ i, ∫ u, g i u = 1)
    (haint : ∀ i,
      Integrable (fun u => Real.sqrt (f i u * g i u)) volume) :
    hellingerSqDensity (Measure.pi (fun _ : ι => volume))
        (fun x => ∏ i, f i (x i))
        (fun x => ∏ i, g i (x i)) =
      2 * (1 - ∏ i, ∫ u, Real.sqrt (f i u * g i u)) := by
  classical
  let F : (ι → ℝ) → ℝ := fun x => ∏ i, f i (x i)
  let G : (ι → ℝ) → ℝ := fun x => ∏ i, g i (x i)
  have hFint : Integrable F (Measure.pi (fun _ : ι => volume)) :=
    Integrable.fintype_prod hfint
  have hGint : Integrable G (Measure.pi (fun _ : ι => volume)) :=
    Integrable.fintype_prod hgint
  have hF0 : ∀ x, 0 ≤ F x :=
    fun x => Finset.prod_nonneg fun i _ => hf0 i (x i)
  have hG0 : ∀ x, 0 ≤ G x :=
    fun x => Finset.prod_nonneg fun i _ => hg0 i (x i)
  have hcross :
      Integrable (fun x => Real.sqrt (F x * G x))
        (Measure.pi (fun _ : ι => volume)) := by
    rw [show (fun x => Real.sqrt (F x * G x)) =
        (fun x => ∏ i, Real.sqrt (f i (x i) * g i (x i))) by
      funext x
      dsimp [F, G]
      rw [← Finset.prod_mul_distrib, Real.sqrt_prod]
      intro i hi
      exact mul_nonneg (hf0 i (x i)) (hg0 i (x i))]
    exact Integrable.fintype_prod haint
  unfold hellingerSqDensity
  have hpoint :
      (fun x => (Real.sqrt (F x) - Real.sqrt (G x)) ^ 2) =
        (fun x => F x + G x - 2 * Real.sqrt (F x * G x)) := by
    funext x
    rw [Real.sqrt_mul (hF0 x)]
    nlinarith [Real.sq_sqrt (hF0 x), Real.sq_sqrt (hG0 x)]
  change ∫ x, (Real.sqrt (F x) - Real.sqrt (G x)) ^ 2
      ∂(Measure.pi (fun _ : ι => volume)) =
    2 * (1 - ∏ i, ∫ u, Real.sqrt (f i u * g i u))
  rw [hpoint]
  change ∫ x, (F + G) x -
      2 * Real.sqrt (F x * G x)
      ∂(Measure.pi (fun _ : ι => volume)) =
    2 * (1 - ∏ i, ∫ u, Real.sqrt (f i u * g i u))
  rw [integral_sub (hFint.add hGint) (hcross.const_mul 2),
    show (∫ x, (F + G) x ∂Measure.pi (fun _ : ι => volume)) =
      ∫ x, F x + G x ∂Measure.pi (fun _ : ι => volume) by rfl,
    integral_add hFint hGint, integral_const_mul]
  rw [show (∫ x, F x ∂Measure.pi (fun _ : ι => volume)) = 1 by
    dsimp [F]
    rw [MeasureTheory.integral_fintype_prod_eq_prod]
    simp [hf1]]
  rw [show (∫ x, G x ∂Measure.pi (fun _ : ι => volume)) = 1 by
    dsimp [G]
    rw [MeasureTheory.integral_fintype_prod_eq_prod]
    simp [hg1]]
  rw [show
      (∫ x, Real.sqrt (F x * G x)
          ∂Measure.pi (fun _ : ι => volume)) =
        ∏ i, ∫ u, Real.sqrt (f i u * g i u) by
    exact densityAffinity_pi _ f g hf0 hg0]
  ring

/-- Conditional on an assignment, the two translated cosine-product
densities have Hellinger square controlled by the sum of squared block
representers. -/
lemma conditional_block_hellinger_le
    (n d β : ℕ) (B p : ℝ)
    (hB : 0 < B) (z : Fin n → Bool) :
    hellingerSqDensity
        (Measure.pi (fun _ : Fin (blockCount n d) => volume))
        (fun y => ∏ b : Fin (blockCount n d),
          cosSqDensity (B / 2)
            (y b - tiltAmplitude B β p (blockCount n d) d *
              blockRepresenter β p d (blockAssignment n d b z)))
        (fun y => ∏ b : Fin (blockCount n d),
          cosSqDensity (B / 2)
            (y b + tiltAmplitude B β p (blockCount n d) d *
              blockRepresenter β p d (blockAssignment n d b z))) ≤
      4 * Real.pi ^ 2 * tiltAmplitude B β p (blockCount n d) d ^ 2 /
          B ^ 2 *
        ∑ b : Fin (blockCount n d),
          blockRepresenter β p d (blockAssignment n d b z) ^ 2 := by
  classical
  let s : ℝ := B / 2
  let δ : ℝ := tiltAmplitude B β p (blockCount n d) d
  let h : Fin (blockCount n d) → ℝ :=
    fun b => blockRepresenter β p d (blockAssignment n d b z)
  let f : Fin (blockCount n d) → ℝ → ℝ :=
    fun b u => cosSqDensity s (u - δ * h b)
  let g : Fin (blockCount n d) → ℝ → ℝ :=
    fun b u => cosSqDensity s (u + δ * h b)
  have hs : 0 < s := by dsimp [s]; linarith
  have hf0 : ∀ b u, 0 ≤ f b u :=
    fun b u => cosSqDensity_nonneg s hs _
  have hg0 : ∀ b u, 0 ≤ g b u :=
    fun b u => cosSqDensity_nonneg s hs _
  have hfint : ∀ b, Integrable (f b) volume :=
    fun b => cosSqDensity_translate_integrable s (δ * h b)
  have hgint : ∀ b, Integrable (g b) volume := by
    intro b
    simpa [g, sub_eq_add_neg, add_comm] using
      cosSqDensity_translate_integrable s (-δ * h b)
  have hf1 : ∀ b, ∫ u, f b u = 1 :=
    fun b => cosSqDensity_translate_integral_one s (δ * h b) hs
  have hg1 : ∀ b, ∫ u, g b u = 1 := by
    intro b
    simpa [g, sub_eq_add_neg, add_comm] using
      cosSqDensity_translate_integral_one s (-δ * h b) hs
  have hflp (b : Fin (blockCount n d)) :
      MemLp (fun u => Real.sqrt (f b u)) 2 volume := by
    have hasm :
        AEStronglyMeasurable (fun u => Real.sqrt (f b u)) volume :=
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (hfint b).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hasm]
    convert hfint b using 1
    funext u
    exact Real.sq_sqrt (hf0 b u)
  have hglp (b : Fin (blockCount n d)) :
      MemLp (fun u => Real.sqrt (g b u)) 2 volume := by
    have hasm :
        AEStronglyMeasurable (fun u => Real.sqrt (g b u)) volume :=
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (hgint b).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hasm]
    convert hgint b using 1
    funext u
    exact Real.sq_sqrt (hg0 b u)
  have haint : ∀ b,
      Integrable (fun u => Real.sqrt (f b u * g b u)) volume := by
    intro b
    convert (hflp b).integrable_mul (hglp b) using 1
    funext u
    simp only [Pi.mul_apply]
    rw [Real.sqrt_mul (hf0 b u)]
  change hellingerSqDensity
      (Measure.pi (fun _ : Fin (blockCount n d) => volume))
      (fun y => ∏ b, f b (y b)) (fun y => ∏ b, g b (y b)) ≤
    4 * Real.pi ^ 2 * δ ^ 2 / B ^ 2 * ∑ b, h b ^ 2
  rw [hellingerSqDensity_pi_eq_two_mul_one_sub_affinity
    f g hf0 hg0 hfint hgint hf1 hg1 haint]
  calc
    2 * (1 - ∏ b, ∫ u, Real.sqrt (f b u * g b u)) ≤
        2 * ∑ b, (1 - ∫ u, Real.sqrt (f b u * g b u)) := by
      gcongr
      apply one_sub_prod_le_sum
      · intro b
        exact integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun u => Real.sqrt_nonneg _)
      · intro b
        have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
          (p := (2 : ℝ)) (q := (2 : ℝ))
          Real.HolderConjugate.two_two
          (Filter.Eventually.of_forall fun u => Real.sqrt_nonneg (f b u))
          (Filter.Eventually.of_forall fun u => Real.sqrt_nonneg (g b u))
          (by simpa using hflp b) (by simpa using hglp b)
        simp_rw [Real.rpow_two, Real.sq_sqrt (hf0 b _),
          Real.sq_sqrt (hg0 b _), hf1 b, hg1 b] at hcs
        simpa [Real.sqrt_mul (hf0 b _)] using hcs
    _ ≤ 2 * ∑ b,
        (Real.pi ^ 2 * ((δ * h b) - (-δ * h b)) ^ 2 /
          (8 * s ^ 2)) := by
      gcongr with b
      simpa [f, g, sub_eq_add_neg] using
        cosSqDensity_affinity_defect_sharp s (δ * h b) (-δ * h b) hs
    _ = 4 * Real.pi ^ 2 * δ ^ 2 / B ^ 2 * ∑ b, h b ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      dsimp [s]
      field_simp
      ring

/-- The Bernoulli average of the summed squared block representers is
`m / A_d`. -/
lemma E_sum_blockRepresenter_sq
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
      (fun _ => le_of_lt hp1)).E
        (fun z => ∑ b : Fin (blockCount n d),
          blockRepresenter β p d (blockAssignment n d b z) ^ 2) =
      blockCount n d / blockEnergy β p d := by
  classical
  rw [FiniteDesign.E_sum]
  have hblock :
      (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
          (fun w => blockRepresenter β p d w ^ 2) =
        (blockEnergy β p d)⁻¹ := by
    let D := blockDesign d p (le_of_lt hp0) (le_of_lt hp1)
    have hD : IsProductBernoulli D p := by
      exact ⟨hp0, hp1,
        ⟨fun _ => le_of_lt hp0, fun _ => le_of_lt hp1, rfl⟩⟩
    exact (blockRepresenter_contrast_energy β d p D hD hβ hd).2
  rw [show
      (∑ b : Fin (blockCount n d),
        (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E
          (fun z =>
            blockRepresenter β p d (blockAssignment n d b z) ^ 2)) =
        ∑ _b : Fin (blockCount n d), (blockEnergy β p d)⁻¹ by
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (bernoulliDesign (fun _ : Fin n => p) (fun _ => le_of_lt hp0)
          (fun _ => le_of_lt hp1)).E
          (fun z =>
            blockRepresenter β p d (blockAssignment n d b z) ^ 2) =
        (blockDesign d p (le_of_lt hp0) (le_of_lt hp1)).E
          (fun w => blockRepresenter β p d w ^ 2) :=
        E_blockAssignment n d p (le_of_lt hp0) (le_of_lt hp1) b
          (fun w => blockRepresenter β p d w ^ 2)
      _ = (blockEnergy β p d)⁻¹ := hblock]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul, div_eq_mul_inv]

/-- The same identity in the explicit assignment-mass notation used by the
common dominating density. -/
lemma sum_assignmentMass_mul_sum_blockRepresenter_sq
    (n d β : ℕ) (p : ℝ)
    (hβ : 1 ≤ β) (hd : 1 ≤ d)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ z : Fin n → Bool, assignmentMass n p z *
        (∑ b : Fin (blockCount n d),
          blockRepresenter β p d (blockAssignment n d b z) ^ 2) =
      blockCount n d / blockEnergy β p d := by
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)
  have hprob (z : Fin n → Bool) :
      assignmentMass n p z = D.p z := by
    simp only [assignmentMass, D, bernoulliDesign, prodDesign_p, coinDesign]
    apply Finset.prod_congr rfl
    intro i hi
    cases z i <;> simp
  simp_rw [hprob]
  exact E_sum_blockRepresenter_sq n d β p hβ hd hp0 hp1

/-- The two explicit prior-predictive densities obey the displayed global
Hellinger bound. -/
lemma blockPrior_hellinger_le
    (n d β : ℕ) (B p : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 < B) (hβ : 1 ≤ β)
    (hp0 : 0 < p) (hp1 : p < 1) :
    hellingerSqDensity (blockDominatingMeasure n d)
        (blockPriorDensity n d β B p 1)
        (blockPriorDensity n d β B p (-1)) ≤
      4 * Real.pi ^ 2 * blockCount n d *
          tiltAmplitude B β p (blockCount n d) d ^ 2 /
        (B ^ 2 * blockEnergy β p d) := by
  classical
  let μy : Measure (Fin (blockCount n d) → ℝ) :=
    Measure.pi (fun _ : Fin (blockCount n d) => volume)
  let δ := tiltAmplitude B β p (blockCount n d) d
  let Cplus : (Fin n → Bool) → (Fin (blockCount n d) → ℝ) → ℝ :=
    fun z y => ∏ b, cosSqDensity (B / 2)
      (y b - δ * blockRepresenter β p d (blockAssignment n d b z))
  let Cminus : (Fin n → Bool) → (Fin (blockCount n d) → ℝ) → ℝ :=
    fun z y => ∏ b, cosSqDensity (B / 2)
      (y b + δ * blockRepresenter β p d (blockAssignment n d b z))
  have hs : 0 < B / 2 := by linarith
  have ha0 (z : Fin n → Bool) : 0 ≤ assignmentMass n p z := by
    unfold assignmentMass
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> linarith
  have hCplus0 (z) (y) : 0 ≤ Cplus z y := by
    dsimp [Cplus]
    exact Finset.prod_nonneg fun b _ =>
      cosSqDensity_nonneg (B / 2) hs _
  have hCminus0 (z) (y) : 0 ≤ Cminus z y := by
    dsimp [Cminus]
    exact Finset.prod_nonneg fun b _ =>
      cosSqDensity_nonneg (B / 2) hs _
  have hCplusInt (z) : Integrable (Cplus z) μy := by
    dsimp [Cplus, μy]
    exact Integrable.fintype_prod fun b =>
      cosSqDensity_translate_integrable (B / 2)
        (δ * blockRepresenter β p d (blockAssignment n d b z))
  have hCminusInt (z) : Integrable (Cminus z) μy := by
    dsimp [Cminus, μy]
    rw [show
        (fun y : Fin (blockCount n d) → ℝ =>
          ∏ b, cosSqDensity (B / 2)
            (y b + δ * blockRepresenter β p d (blockAssignment n d b z))) =
        (fun y => ∏ b, cosSqDensity (B / 2)
          (y b - (-δ * blockRepresenter β p d
            (blockAssignment n d b z)))) by
      funext y
      apply Finset.prod_congr rfl
      intro b hb
      congr 2
      ring]
    exact Integrable.fintype_prod fun b =>
      cosSqDensity_translate_integrable (B / 2)
        (-δ * blockRepresenter β p d (blockAssignment n d b z))
  have hhellInt (z) :
      Integrable (fun y => (Real.sqrt (Cplus z y) -
        Real.sqrt (Cminus z y)) ^ 2) μy := by
    have hmeas :
        AEStronglyMeasurable (fun y => (Real.sqrt (Cplus z y) -
          Real.sqrt (Cminus z y)) ^ 2) μy := by
      fun_prop
    apply Integrable.mono'
        ((hCplusInt z).const_mul 2 |>.add ((hCminusInt z).const_mul 2))
        hmeas
    exact Filter.Eventually.of_forall fun y => by
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sq_sqrt (hCplus0 z y),
        Real.sq_sqrt (hCminus0 z y),
        sq_nonneg (Real.sqrt (Cplus z y) + Real.sqrt (Cminus z y))]
  have hjointInt :
      Integrable
        (fun x : (Fin n → Bool) × (Fin (blockCount n d) → ℝ) =>
          (Real.sqrt (blockPriorDensity n d β B p 1 x) -
            Real.sqrt (blockPriorDensity n d β B p (-1) x)) ^ 2)
        (blockDominatingMeasure n d) := by
    rw [blockDominatingMeasure]
    have hdensMeas (σ : ℝ) :
        Measurable (blockPriorDensity n d β B p σ) := by
      unfold blockPriorDensity
      apply Measurable.mul
      · exact (measurable_of_finite
          (assignmentMass n p)).comp measurable_fst
      · apply Finset.measurable_prod
        intro b hb
        apply (cosSqDensity_measurable (B / 2)).comp
        apply Measurable.sub
        · exact (measurable_pi_apply b).comp measurable_snd
        · exact (measurable_of_finite (fun z : Fin n → Bool =>
            σ * tiltAmplitude B β p (blockCount n d) d *
              blockRepresenter β p d
                (blockAssignment n d b z))).comp measurable_fst
    have hmeas :
        AEStronglyMeasurable
          (fun x : (Fin n → Bool) × (Fin (blockCount n d) → ℝ) =>
            (Real.sqrt (blockPriorDensity n d β B p 1 x) -
              Real.sqrt (blockPriorDensity n d β B p (-1) x)) ^ 2)
          (Measure.count.prod μy) := by
      exact (((Real.continuous_sqrt.measurable.comp (hdensMeas 1)).sub
        (Real.continuous_sqrt.measurable.comp (hdensMeas (-1)))).pow_const
          2).aestronglyMeasurable
    rw [integrable_prod_iff hmeas]
    constructor
    · exact Filter.Eventually.of_forall fun z => by
        have hz :
            (fun y => (Real.sqrt
                (blockPriorDensity n d β B p 1 (z, y)) -
              Real.sqrt
                (blockPriorDensity n d β B p (-1) (z, y))) ^ 2) =
              (fun y => assignmentMass n p z *
                (Real.sqrt (Cplus z y) -
                  Real.sqrt (Cminus z y)) ^ 2) := by
          funext y
          simp only [blockPriorDensity, Cplus, Cminus, δ, one_mul,
            neg_one_mul, neg_mul, sub_neg_eq_add]
          change (Real.sqrt (assignmentMass n p z * Cplus z y) -
              Real.sqrt (assignmentMass n p z * Cminus z y)) ^ 2 =
            assignmentMass n p z *
              (Real.sqrt (Cplus z y) - Real.sqrt (Cminus z y)) ^ 2
          rw [Real.sqrt_mul (ha0 z), Real.sqrt_mul (ha0 z),
            ← mul_sub, mul_pow]
          rw [Real.sq_sqrt (ha0 z)]
        rw [hz]
        exact (hhellInt z).const_mul (assignmentMass n p z)
    · exact Integrable.of_finite
  unfold hellingerSqDensity
  rw [blockDominatingMeasure, integral_prod _ hjointInt]
  have hinner (z : Fin n → Bool) :
      (∫ y, (Real.sqrt (blockPriorDensity n d β B p 1 (z, y)) -
          Real.sqrt (blockPriorDensity n d β B p (-1) (z, y))) ^ 2
          ∂μy) =
        assignmentMass n p z *
          hellingerSqDensity μy (Cplus z) (Cminus z) := by
    rw [show
        (fun y => (Real.sqrt (blockPriorDensity n d β B p 1 (z, y)) -
          Real.sqrt (blockPriorDensity n d β B p (-1) (z, y))) ^ 2) =
        (fun y => assignmentMass n p z *
          (Real.sqrt (Cplus z y) - Real.sqrt (Cminus z y)) ^ 2) by
      funext y
      simp only [blockPriorDensity, Cplus, Cminus, δ, one_mul,
        neg_one_mul, neg_mul, sub_neg_eq_add]
      change (Real.sqrt (assignmentMass n p z * Cplus z y) -
          Real.sqrt (assignmentMass n p z * Cminus z y)) ^ 2 =
        assignmentMass n p z *
          (Real.sqrt (Cplus z y) - Real.sqrt (Cminus z y)) ^ 2
      rw [Real.sqrt_mul (ha0 z), Real.sqrt_mul (ha0 z),
        ← mul_sub, mul_pow, Real.sq_sqrt (ha0 z)]]
    rw [integral_const_mul]
    rfl
  rw [show
      (fun z : Fin n → Bool =>
        ∫ y, (Real.sqrt (blockPriorDensity n d β B p 1 (z, y)) -
          Real.sqrt (blockPriorDensity n d β B p (-1) (z, y))) ^ 2 ∂μy) =
      (fun z => assignmentMass n p z *
        hellingerSqDensity μy (Cplus z) (Cminus z)) by
    funext z
    exact hinner z]
  rw [MeasureTheory.integral_fintype]
  · have hcount (z : Fin n → Bool) :
        Measure.count.real ({z} : Set (Fin n → Bool)) = 1 := by
      rw [measureReal_def, Measure.count_apply_finite]
      · simp
      · exact Set.finite_singleton z
    simp_rw [hcount, one_smul]
    calc
      ∑ z : Fin n → Bool,
          assignmentMass n p z *
            hellingerSqDensity μy (Cplus z) (Cminus z) ≤
        ∑ z : Fin n → Bool,
          assignmentMass n p z *
            (4 * Real.pi ^ 2 * δ ^ 2 / B ^ 2 *
              ∑ b : Fin (blockCount n d),
                blockRepresenter β p d (blockAssignment n d b z) ^ 2) := by
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_left _ (ha0 z)
        exact conditional_block_hellinger_le n d β B p hB z
      _ = 4 * Real.pi ^ 2 * δ ^ 2 / B ^ 2 *
          (blockCount n d / blockEnergy β p d) := by
        rw [show
            (∑ z : Fin n → Bool,
              assignmentMass n p z *
                (4 * Real.pi ^ 2 * δ ^ 2 / B ^ 2 *
                  ∑ b : Fin (blockCount n d),
                    blockRepresenter β p d
                      (blockAssignment n d b z) ^ 2)) =
              4 * Real.pi ^ 2 * δ ^ 2 / B ^ 2 *
                ∑ z : Fin n → Bool, assignmentMass n p z *
                  (∑ b : Fin (blockCount n d),
                    blockRepresenter β p d
                      (blockAssignment n d b z) ^ 2) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          ring]
        rw [sum_assignmentMass_mul_sum_blockRepresenter_sq
          n d β p hβ hd hp0 hp1]
      _ = 4 * Real.pi ^ 2 * blockCount n d * δ ^ 2 /
          (B ^ 2 * blockEnergy β p d) := by
        have hA : blockEnergy β p d ≠ 0 :=
          ne_of_gt (blockEnergy_pos β d p hβ hd hp0 hp1)
        have hB0 : B ≠ 0 := ne_of_gt hB
        field_simp
  · exact Integrable.of_finite

end CausalSmith.Experimentation.SnipeDegreeFrontier
