import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductTV
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductConditioning
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonPredictive
import Causalean.Stat.Minimax.Mixture

/-!
# Product predictive identification

Mixing independent coordinate kernels over an iid finite prior equals the iid
product of the one-coordinate mixed predictive law.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped NNReal ENNReal BigOperators

lemma oneArmFiniteIidPMF_apply {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ω : PMF α) (m : ℕ) (z : Fin m → α) :
    oneArmFiniteIidPMF ω m z = ∏ i, ω (z i) := by
  rw [oneArmFiniteIidPMF, Measure.toPMF_apply]
  unfold oneArmFiniteIidMeasure
  rw [Measure.pi_singleton]
  congr 1
  funext i
  exact ω.toMeasure_apply_singleton (z i) (MeasurableSet.singleton (z i))

/-- Finite iid product of a countable PMF, represented as a measure. -/
noncomputable def oneArmCountIidMeasure
    {β : Type*} [MeasurableSpace β] (q : PMF β) (m : ℕ) :
    Measure (Fin m → β) :=
  Measure.pi fun _ : Fin m => q.toMeasure

noncomputable instance oneArmCountIidMeasure_isProbabilityMeasure
    {β : Type*} [MeasurableSpace β] (q : PMF β) (m : ℕ) :
    IsProbabilityMeasure (oneArmCountIidMeasure q m) := by
  unfold oneArmCountIidMeasure
  infer_instance

/-- Mixing coordinatewise product kernels over an iid finite prior is exactly
the iid product of the one-coordinate mixed PMF. -/
theorem mixture_iid_productKernel_eq
    {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ω : PMF α) (K : α → PMF β) (m : ℕ) :
    mixture (oneArmFiniteIidPMF ω m)
        (fun z => Measure.pi fun i : Fin m => (K (z i)).toMeasure) =
      oneArmCountIidMeasure (ω.bind K) m := by
  apply Measure.ext_of_singleton
  intro c
  rw [mixture_apply, oneArmCountIidMeasure, Measure.pi_singleton]
  have hK (r : α) (b : β) : (K r).toMeasure {b} = K r b :=
    (K r).toMeasure_apply_singleton b (MeasurableSet.singleton b)
  have hbind (b : β) : (ω.bind K).toMeasure {b} = (ω.bind K) b :=
    (ω.bind K).toMeasure_apply_singleton b (MeasurableSet.singleton b)
  simp_rw [oneArmFiniteIidPMF_apply]
  simp_rw [Measure.pi_singleton]
  simp_rw [hK]
  simp_rw [hbind]
  simp_rw [PMF.bind_apply]
  calc
    ∑ z : Fin m → α, (∏ i, ω (z i)) * ∏ i, K (z i) (c i) =
        ∑ z : Fin m → α, ∏ i, (ω (z i) * K (z i) (c i)) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ r : α, ω r * K r (c i) := by
      rw [Fintype.prod_sum]
    _ = _ := by simp only [tsum_fintype]

/-- Adding one parameter-independent anchor coordinate to every product kernel
preserves the iid predictive factorization on the active coordinates. -/
theorem mixture_iid_productKernel_with_common_anchor_eq
    {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ω : PMF α) (anchorLaw : PMF β) (K : α → PMF β) (m : ℕ) :
    mixture (oneArmFiniteIidPMF ω m)
        (fun z => Measure.pi fun r : Fin (m + 1) =>
          Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
            (fun i => (K (z i)).toMeasure) r) =
      Measure.pi (fun r : Fin (m + 1) =>
        Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
          (fun _ => (ω.bind K).toMeasure) r) := by
  letI : ∀ z : Fin m → α, ∀ r : Fin (m + 1), SigmaFinite
      (Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
        (fun i => (K (z i)).toMeasure) r) := fun z r =>
    Fin.cases (by change SigmaFinite anchorLaw.toMeasure; infer_instance)
      (fun i => by change SigmaFinite (K (z i)).toMeasure; infer_instance) r
  letI : ∀ r : Fin (m + 1), SigmaFinite
      (Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
        (fun _ => (ω.bind K).toMeasure) r) := fun r =>
    Fin.cases (by change SigmaFinite anchorLaw.toMeasure; infer_instance)
      (fun _ => by change SigmaFinite (ω.bind K).toMeasure; infer_instance) r
  apply Measure.ext_of_singleton
  intro c
  rw [mixture_apply, Measure.pi_singleton]
  simp_rw [oneArmFiniteIidPMF_apply]
  simp_rw [Measure.pi_singleton]
  have hanchor : anchorLaw.toMeasure {c 0} = anchorLaw (c 0) :=
    anchorLaw.toMeasure_apply_singleton (c 0) (MeasurableSet.singleton (c 0))
  have hK (r : α) (i : Fin m) :
      (K r).toMeasure {c i.succ} = K r (c i.succ) :=
    (K r).toMeasure_apply_singleton (c i.succ)
      (MeasurableSet.singleton (c i.succ))
  have hbind (i : Fin m) :
      (ω.bind K).toMeasure {c i.succ} = (ω.bind K) (c i.succ) :=
    (ω.bind K).toMeasure_apply_singleton (c i.succ)
      (MeasurableSet.singleton (c i.succ))
  have hprodK (z : Fin m → α) :
      (∏ r : Fin (m + 1),
        (Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
          (fun i => (K (z i)).toMeasure) r) {c r}) =
        anchorLaw (c 0) * ∏ i, K (z i) (c i.succ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [hanchor]
    simp_rw [hK]
  have hprodBind :
      (∏ r : Fin (m + 1),
        (Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
          (fun _ => (ω.bind K).toMeasure) r) {c r}) =
        anchorLaw (c 0) * ∏ i : Fin m, (ω.bind K) (c i.succ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [hanchor]
    simp_rw [hbind]
  simp_rw [hprodK, hprodBind, PMF.bind_apply]
  calc
    ∑ z : Fin m → α, (∏ i : Fin m, ω (z i)) *
        (anchorLaw (c 0) * ∏ i : Fin m, K (z i) (c i.succ)) =
      anchorLaw (c 0) *
        ∑ z : Fin m → α, ∏ i : Fin m,
          (ω (z i) * K (z i) (c i.succ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          calc
            _ = anchorLaw (c 0) *
                ((∏ i : Fin m, ω (z i)) *
                  ∏ i : Fin m, K (z i) (c i.succ)) := by ac_rfl
            _ = _ := by rw [Finset.prod_mul_distrib]
    _ = anchorLaw (c 0) *
        ∏ i : Fin m, ∑ r : α, ω r * K r (c i.succ) := by
      rw [Fintype.prod_sum]
    _ = _ := by simp only [tsum_fintype]

/-- A common anchor coordinate costs no total variation; only the `m` iid
active predictive coordinates contribute. -/
theorem tvDist_mixture_iid_productKernel_with_common_anchor_le
    {α₀ α₁ β : Type*} [Fintype α₀] [Fintype α₁] [Countable β]
    [MeasurableSpace α₀] [MeasurableSingletonClass α₀]
    [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ω₀ : PMF α₀) (ω₁ : PMF α₁) (anchorLaw : PMF β)
    (K₀ : α₀ → PMF β) (K₁ : α₁ → PMF β) (m : ℕ) :
    tvDist
        (mixture (oneArmFiniteIidPMF ω₀ m)
          (fun z => Measure.pi fun r : Fin (m + 1) =>
            Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
              (fun i => (K₀ (z i)).toMeasure) r))
        (mixture (oneArmFiniteIidPMF ω₁ m)
          (fun z => Measure.pi fun r : Fin (m + 1) =>
            Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
              (fun i => (K₁ (z i)).toMeasure) r)) ≤
      (m : ℝ) * tvDist (ω₀.bind K₀).toMeasure (ω₁.bind K₁).toMeasure := by
  rw [mixture_iid_productKernel_with_common_anchor_eq,
    mixture_iid_productKernel_with_common_anchor_eq]
  let mu : Fin (m + 1) → Measure β := fun r =>
    Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
      (fun _ => (ω₀.bind K₀).toMeasure) r
  let nu : Fin (m + 1) → Measure β := fun r =>
    Fin.cases (motive := fun _ => Measure β) anchorLaw.toMeasure
      (fun _ => (ω₁.bind K₁).toMeasure) r
  have hmu : ∀ r, IsProbabilityMeasure (mu r) := fun r => by
    refine Fin.cases ?_ (fun _ => ?_) r <;> dsimp [mu] <;> infer_instance
  have hnu : ∀ r, IsProbabilityMeasure (nu r) := fun r => by
    refine Fin.cases ?_ (fun _ => ?_) r <;> dsimp [nu] <;> infer_instance
  letI : ∀ r, IsProbabilityMeasure (mu r) := hmu
  letI : ∀ r, IsProbabilityMeasure (nu r) := hnu
  have hanchorZero : tvDist anchorLaw.toMeasure anchorLaw.toMeasure = 0 := by
    unfold tvDist
    simp
  change tvDist (Measure.pi mu) (Measure.pi nu) ≤ _
  calc
    tvDist (Measure.pi mu) (Measure.pi nu) ≤
        ∑ r, tvDist (mu r) (nu r) := tvDist_pi_le_sum mu nu
    _ = (m : ℝ) * tvDist (ω₀.bind K₀).toMeasure
        (ω₁.bind K₁).toMeasure := by
      rw [Fin.sum_univ_succ]
      simp [mu, nu, hanchorZero]

/-- Specialization to the one-cell triple-Poisson predictive kernel. -/
theorem mixture_iid_triplePoisson_eq
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ω : PMF α) (lam11 lam10 lam0 : α → ℝ≥0) (m : ℕ) :
    mixture (oneArmFiniteIidPMF ω m)
        (fun z => Measure.pi fun i : Fin m =>
          (triplePoissonPMF (lam11 (z i)) (lam10 (z i)) (lam0 (z i))).toMeasure) =
      oneArmCountIidMeasure (mixedTriplePoissonPMF ω lam11 lam10 lam0) m := by
  exact mixture_iid_productKernel_eq ω
    (fun r => triplePoissonPMF (lam11 r) (lam10 r) (lam0 r)) m

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
