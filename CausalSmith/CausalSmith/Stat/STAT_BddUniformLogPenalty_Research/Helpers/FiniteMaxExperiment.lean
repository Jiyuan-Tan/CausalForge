import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxCore

/-!
# The finite angular marked-Poisson experiment

This file identifies the hard-family marked Poisson law with the common
complement block and independent coordinate-cell blocks used by the
coordinatewise direct-product theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Equip the packing-experiment index set with the discrete measurable structure. -/
local instance packingExperimentIndexMeasurableSpace (M : ℕ) :
    MeasurableSpace (Unit ⊕ Fin M) := ⊤

/-- Every singleton packing-experiment index is measurable. -/
local instance packingExperimentIndexMeasurableSingletonClass (M : ℕ) :
    MeasurableSingletonClass (Unit ⊕ Fin M) := ⟨fun _ => trivial⟩

/-- A canonical vertex whose only potentially nonzero coordinate is `j`. -/
-- @node: packingSingleBit
def packingSingleBit {M : ℕ} (j : Fin M) (b : Bool) : Fin M → Bool :=
  fun k => if k = j then b else false

-- @node: packingSingleBit_self
/-- Activating the selected packing coordinate sets that coordinate to its prescribed bit. -/
lemma packingSingleBit_self {M : ℕ} (j : Fin M) (b : Bool) :
    packingSingleBit j b j = b := by simp [packingSingleBit]

/-- The canonical marked-Poisson experiment for coordinate `j` and bit `b`. -/
-- @node: packingCellExperiment
noncomputable def packingCellExperiment {M : ℕ}
    (p : FiniteMeasurablePartition Observation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → CtyLaw) (lam : ℝ≥0)
    (j : Fin M) (b : Bool) : Measure (FiniteSample (Observation × ℝ)) := by
  letI : IsProbabilityMeasure (laws (packingSingleBit j b)).law :=
    (laws (packingSingleBit j b)).law_isProbability
  exact canonicalMarkedPoissonSampleLaw
    (p.cellObservationLaw (laws (packingSingleBit j b)).law (.inr j))
    packingMarkLaw
    (lam * p.cellMass (laws (packingSingleBit j b)).law (.inr j))

/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
instance packingCellExperiment_isProbabilityMeasure {M : ℕ}
    (p : FiniteMeasurablePartition Observation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → CtyLaw) (lam : ℝ≥0)
    (j : Fin M) (b : Bool) :
    IsProbabilityMeasure (packingCellExperiment p laws lam j b) := by
  unfold packingCellExperiment
  infer_instance

/-- The common complement block, represented at the all-false vertex. -/
-- @node: packingCommonExperiment
noncomputable def packingCommonExperiment {M : ℕ}
    (p : FiniteMeasurablePartition Observation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → CtyLaw) (lam : ℝ≥0) :
    Measure (Unit → FiniteSample (Observation × ℝ)) := by
  let omega0 : Fin M → Bool := fun _ => false
  letI : IsProbabilityMeasure (laws omega0).law := (laws omega0).law_isProbability
  exact Measure.pi (fun _ : Unit => canonicalMarkedPoissonSampleLaw
    (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
    (lam * p.cellMass (laws omega0).law (.inl ())))

/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
instance packingCommonExperiment_isProbabilityMeasure {M : ℕ}
    (p : FiniteMeasurablePartition Observation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → CtyLaw) (lam : ℝ≥0) :
    IsProbabilityMeasure (packingCommonExperiment p laws lam) := by
  unfold packingCommonExperiment
  infer_instance

/-- Put the common block and coordinate blocks back into the sum-indexed
family and superpose them in increasing mark order. -/
-- @node: synthesizePackingConfiguration
noncomputable def synthesizePackingConfiguration {M : ℕ}
    (z : (Unit → FiniteSample (Observation × ℝ)) ×
      (Fin M → FiniteSample (Observation × ℝ))) :
    FiniteSample (Observation × ℝ) :=
  superposeByMarks
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm z)

-- @node: synthesizePackingConfiguration_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma synthesizePackingConfiguration_measurable {M : ℕ} :
    Measurable (synthesizePackingConfiguration (M := M)) := by
  exact measurable_superposeByMarks.comp
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm.measurable

/-- Pointwise measurable mapping commutes with a finite Poisson sample law. -/
-- @node: map_finitePoissonSampleLaw_finiteSampleMap
lemma map_finitePoissonSampleLaw_finiteSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → Y) (hf : Measurable f) (lam : ℝ≥0) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw P lam) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f P) lam) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  let μ := Measure.map F (finitePoissonSampleLaw P lam)
  let ν := finitePoissonSampleLaw (Measure.map f P) lam
  have hrest (n : ℕ) :
      μ.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        ν.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by
    rw [show μ = Measure.map F (finitePoissonSampleLaw P lam) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (measurableSet_singleton n))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({n} : Set ℕ) := by
      ext s
      rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show ν = finitePoissonSampleLaw (Measure.map f P) lam by rfl,
      finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
      Measure.map_map hF (measurable_fixedSizeEmbed n)]
    have hfun : F ∘ fixedSizeEmbed n =
        fixedSizeEmbed n ∘ (fun x : Fin n → X => fun i => f (x i)) := by
      funext x
      exact finiteSampleMap_fixedSizeEmbed f n x
    rw [hfun]
    congr 1
    let G : (Fin n → X) → (Fin n → Y) := fun x i => f (x i)
    have hG : Measurable G :=
      measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
    change Measure.map (fixedSizeEmbed n ∘ G) (Measure.pi fun _ : Fin n => P) = _
    calc
      Measure.map (fixedSizeEmbed n ∘ G) (Measure.pi fun _ : Fin n => P) =
          Measure.map (fixedSizeEmbed n)
            (Measure.map G (Measure.pi fun _ : Fin n => P)) :=
        (Measure.map_map (measurable_fixedSizeEmbed n) hG).symm
      _ = Measure.map (fixedSizeEmbed n)
          (Measure.pi fun _ : Fin n => Measure.map f P) := by
        rw [show G = (fun x i => f (x i)) by rfl,
          Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  have hdecomp (η : Measure (FiniteSample Y)) :
      η = Measure.sum (fun n =>
        η.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
    have hdis : Pairwise (Function.onFun Disjoint
        (fun n : ℕ => (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
          ({n} : Set ℕ))) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro s hi hj
      apply hij
      simpa using hi.symm.trans hj
    have hcover : ⋃ n : ℕ, (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
        ({n} : Set ℕ) = Set.univ := by
      ext s
      simp
    calc
      η = η.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = η.restrict (⋃ n : ℕ,
          FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun n =>
          η.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun n => measurable_finiteSample_count (measurableSet_singleton n))
  change μ = ν
  rw [hdecomp μ, hdecomp ν]
  congr 1
  funext n
  exact hrest n

/-- Mapping only the observation coordinate commutes with a finite marked
Poisson sample law. -/
-- @node: map_finiteMarkedPoissonSampleLaw_finiteSampleMap
lemma map_finiteMarkedPoissonSampleLaw_finiteSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (f : X → Y) (hf : Measurable f) (lam : ℝ≥0) :
    Measure.map (finiteSampleMap (fun z : X × ℝ => (f z.1, z.2)))
        (finiteMarkedPoissonSampleLaw P R lam) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finiteMarkedPoissonSampleLaw (Measure.map f P) R lam) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let g : X × ℝ → Y × ℝ := fun z => (f z.1, z.2)
  have hg : Measurable g := (hf.comp measurable_fst).prodMk measurable_snd
  unfold finiteMarkedPoissonSampleLaw
  rw [map_finitePoissonSampleLaw_finiteSampleMap (P.prod R) g hg lam]
  congr 2
  have hmap := (Measure.map_prod_map P R hf measurable_id).symm
  rw [Measure.map_id] at hmap
  exact hmap

/-- The two-cell partition of outcome-distance space into radii at most `w`
and radii larger than `w`. -/
-- @node: packingRadialPartition
noncomputable def packingRadialPartition (w : ℝ) :
    FiniteMeasurablePartition (ℝ × ℝ) Bool :=
    FiniteMeasurablePartition.ofSets
    (fun b => if b then {z | w < z.2} else {z | z.2 ≤ w})
    (by
      intro b
      cases b
      · change MeasurableSet {z : ℝ × ℝ | z.2 ≤ w}
        exact measurableSet_Iic.preimage
          (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
      · change MeasurableSet {z : ℝ × ℝ | w < z.2}
        exact measurableSet_Ioi.preimage
          (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ)))
    (by
      intro b b' h
      cases b <;> cases b'
      · exact (h rfl).elim
      · apply Set.disjoint_left.2
        intro z hz hz'
        simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz
        simp only [if_true, Set.mem_setOf_eq] at hz'
        exact (not_lt_of_ge hz) hz'
      · apply Set.disjoint_left.2
        intro z hz hz'
        simp only [if_true, Set.mem_setOf_eq] at hz
        simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz'
        exact (not_lt_of_ge hz') hz
      · exact (h rfl).elim)
    (by
      ext z
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases h : z.2 ≤ w
      · exact ⟨false, by simpa using h⟩
      · exact ⟨true, by simpa using lt_of_not_ge h⟩)

-- @node: packingRadialPartition_cellSet_false
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma packingRadialPartition_cellSet_false (w : ℝ) :
    (packingRadialPartition w).cellSet false = {z : ℝ × ℝ | z.2 ≤ w} := by
  exact FiniteMeasurablePartition.ofSets_cellSet _ _ _ _ false

/-- The canonically ordered short-radius block is a measurable image of the
full raw marked-Poisson outcome-distance experiment. -/
-- @node: map_shortRadiusBlock_finiteMarkedPoissonSampleLaw
lemma map_shortRadiusBlock_finiteMarkedPoissonSampleLaw
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (w : ℝ) (lam : ℝ≥0) :
    Measure.map (orderByMarks ∘ (packingRadialPartition w).restrictCell false)
        (finiteMarkedPoissonSampleLaw P R lam) =
      canonicalMarkedPoissonSampleLaw
        ((packingRadialPartition w).cellObservationLaw P false) R
        (lam * (packingRadialPartition w).cellMass P false) := by
  let p := packingRadialPartition w
  have hjoint := p.map_restrictPartition_finiteMarkedPoissonSampleLaw P R lam
  have hcell : Measure.map (p.restrictCell false)
      (finiteMarkedPoissonSampleLaw P R lam) =
      finiteMarkedPoissonSampleLaw (p.cellObservationLaw P false) R
        (lam * p.cellMass P false) := by
    calc
      Measure.map (p.restrictCell false)
          (finiteMarkedPoissonSampleLaw P R lam) =
          Measure.map (Function.eval false)
            (Measure.map p.restrictPartition
              (finiteMarkedPoissonSampleLaw P R lam)) := by
        rw [Measure.map_map (measurable_pi_apply false)
          p.measurable_restrictPartition]
        rfl
      _ = Measure.map (Function.eval false)
          (Measure.pi fun b : Bool =>
            finiteMarkedPoissonSampleLaw (p.cellObservationLaw P b) R
              (lam * p.cellMass P b)) := by rw [hjoint]
      _ = _ := by
        rw [Measure.pi_map_eval]
        simp only [measure_univ, Finset.prod_const_one, one_smul]
  rw [show orderByMarks ∘ p.restrictCell false =
      orderByMarks ∘ p.restrictCell false by rfl,
    ← Measure.map_map measurable_orderByMarks (p.measurable_restrictCell false),
    hcell]
  rfl

/-- For a law supported by the packing square, mapping its restriction to a
packing cell into outcome-distance coordinates gives the corresponding
short-radius restriction of the one-point distance law. -/
-- @node: map_packingCell_restrict_eq_onePointDistance_restrict
lemma map_packingCell_restrict_eq_onePointDistance_restrict
    (P : CtyLaw) (x : Score) (w : ℝ) :
    Measure.map (fun o : Observation => (o.1, dist o.2 x))
        (P.law.restrict {o | o.2 ∈ Metric.closedBall x w ∩ P.support}) =
      (onePointDistanceLaw P x).restrict {z | z.2 ≤ w} := by
  let f : Observation → ℝ × ℝ := fun o => (o.1, dist o.2 x)
  have hf : Measurable f := by fun_prop
  have hsupp : ∀ᵐ o ∂P.law, o.2 ∈ P.support := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa [P.support_eq_marginal_support] using
      (Measure.map Prod.snd P.law).support_mem_ae
  have hset : {o : Observation | o.2 ∈ Metric.closedBall x w ∩ P.support} =ᵐ[P.law]
      f ⁻¹' {z : ℝ × ℝ | z.2 ≤ w} := by
    filter_upwards [hsupp] with o ho
    simp only [Set.mem_setOf_eq, Set.mem_preimage, f, Metric.mem_closedBall]
    exact propext (and_iff_left ho)
  rw [P.law.restrict_congr_set hset]
  change Measure.map f (P.law.restrict (f ⁻¹' {z : ℝ × ℝ | z.2 ≤ w})) =
    (Measure.map f P.law).restrict {z : ℝ × ℝ | z.2 ≤ w}
  exact (Measure.restrict_map hf
    (measurableSet_Iic.preimage
      (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ)))).symm

/-- Mapping a marked configuration pointwise without changing its marks
commutes definitionally with canonical mark ordering. -/
-- @node: finiteSampleMap_orderByMarks
lemma finiteSampleMap_orderByMarks
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : FiniteSample (X × ℝ)) :
    finiteSampleMap (fun z : X × ℝ => (f z.1, z.2)) (orderByMarks s) =
      orderByMarks (finiteSampleMap (fun z : X × ℝ => (f z.1, z.2)) s) := by
  rfl

/-- Normalising a positive packing-cell restriction and then mapping to
outcome-distance coordinates gives the normalised short-radius law. -/
-- @node: map_packingCellObservationLaw_eq_radialCellObservationLaw
lemma map_packingCellObservationLaw_eq_radialCellObservationLaw {M : ℕ}
    (centers : Fin M → Score) (w m : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (P : CtyLaw) (hsupport : P.support = packingSquare)
    (hm : 0 < m) (j : Fin M)
    (hmass : Measure.map Prod.snd P.law (packingCell centers w j) =
      ENNReal.ofReal m) :
    (letI : IsProbabilityMeasure P.law := P.law_isProbability
     letI : IsProbabilityMeasure (onePointDistanceLaw P (centers j)) :=
       onePointDistanceLaw_isProbabilityMeasure P (centers j)
    Measure.map (fun o : Observation => (o.1, dist o.2 (centers j)))
        ((packingFinitePartition centers w hdis).cellObservationLaw P.law (.inr j)) =
      (packingRadialPartition w).cellObservationLaw
        (onePointDistanceLaw P (centers j)) false) := by
  let p := packingFinitePartition centers w hdis
  let r := packingRadialPartition w
  let f : Observation → ℝ × ℝ := fun o => (o.1, dist o.2 (centers j))
  have hf : Measurable f := by fun_prop
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  letI : IsProbabilityMeasure (onePointDistanceLaw P (centers j)) :=
    onePointDistanceLaw_isProbabilityMeasure P (centers j)
  letI : IsProbabilityMeasure (p.cellObservationLaw P.law (.inr j)) := inferInstance
  letI : IsProbabilityMeasure
      (Measure.map f (p.cellObservationLaw P.law (.inr j))) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hpMass : P.law (p.cellSet (.inr j)) = ENNReal.ofReal m := by
    rw [show p = packingFinitePartition centers w hdis by rfl,
      packingFinitePartition_cell_measure_eq_map_snd]
    exact hmass
  have hpPos : P.law (p.cellSet (.inr j)) ≠ 0 := by
    rw [hpMass]
    exact (ENNReal.ofReal_pos.mpr hm).ne'
  have hmapRest : Measure.map f (P.law.restrict (p.cellSet (.inr j))) =
      (onePointDistanceLaw P (centers j)).restrict (r.cellSet false) := by
    rw [show p.cellSet (.inr j) =
        {o : Observation | o.2 ∈ Metric.closedBall (centers j) w ∩ P.support} by
      rw [show p = packingFinitePartition centers w hdis by rfl,
        packingFinitePartition_cellSet, packingPartitionSet, hsupport]
      rfl]
    rw [show r.cellSet false = {z : ℝ × ℝ | z.2 ≤ w} by
      exact packingRadialPartition_cellSet_false w]
    exact map_packingCell_restrict_eq_onePointDistance_restrict P (centers j) w
  have hrMass : onePointDistanceLaw P (centers j) (r.cellSet false) =
      ENNReal.ofReal m := by
    have hu := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ) hmapRest
    calc
      onePointDistanceLaw P (centers j) (r.cellSet false) =
          ((onePointDistanceLaw P (centers j)).restrict (r.cellSet false)) Set.univ := by
        rw [Measure.restrict_apply_univ]
      _ = (Measure.map f (P.law.restrict (p.cellSet (.inr j)))) Set.univ := hu.symm
      _ = P.law (p.cellSet (.inr j)) := by
        rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
          Measure.restrict_apply_univ]
      _ = ENNReal.ofReal m := hpMass
  have hrPos : onePointDistanceLaw P (centers j) (r.cellSet false) ≠ 0 := by
    rw [hrMass]
    exact (ENNReal.ofReal_pos.mpr hm).ne'
  unfold FiniteMeasurablePartition.cellObservationLaw
  rw [dif_neg hpPos, dif_neg hrPos, Measure.map_smul, hpMass, hrMass, hmapRest]

/-- A compressed canonical cell experiment is the canonical short-radius
block of the full one-point outcome-distance marked-Poisson experiment. -/
-- @node: compressedPackingCellExperiment_eq_shortRadiusBlock
lemma compressedPackingCellExperiment_eq_shortRadiusBlock {M : ℕ}
    (centers : Fin M → Score) (w m : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (lam : ℝ≥0) (j : Fin M) (b : Bool) :
    (let P := laws (packingSingleBit j b)
     letI : IsProbabilityMeasure P.law := P.law_isProbability
     letI : IsProbabilityMeasure (onePointDistanceLaw P (centers j)) :=
       onePointDistanceLaw_isProbabilityMeasure P (centers j)
    compressedCoordinateLaw
        (compressPackingCell centers j)
        (packingCellExperiment (packingFinitePartition centers w hdis) laws lam j b) =
      Measure.map (orderByMarks ∘ (packingRadialPartition w).restrictCell false)
        (finiteMarkedPoissonSampleLaw
          (onePointDistanceLaw (laws (packingSingleBit j b)) (centers j))
          packingMarkLaw lam)) := by
  let P := laws (packingSingleBit j b)
  let p := packingFinitePartition centers w hdis
  let r := packingRadialPartition w
  let f : Observation → ℝ × ℝ := fun o => (o.1, dist o.2 (centers j))
  have hf : Measurable f := by fun_prop
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  letI : IsProbabilityMeasure (onePointDistanceLaw P (centers j)) :=
    onePointDistanceLaw_isProbabilityMeasure P (centers j)
  letI : IsProbabilityMeasure (p.cellObservationLaw P.law (.inr j)) := inferInstance
  letI : IsProbabilityMeasure
      (Measure.map f (p.cellObservationLaw P.law (.inr j))) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hmapObs := map_packingCellObservationLaw_eq_radialCellObservationLaw
    centers w m hdis P (hsupport _) hm j (hmass _ j)
  have hmassCell : p.cellMass P.law (.inr j) = r.cellMass
      (onePointDistanceLaw P (centers j)) false := by
    unfold FiniteMeasurablePartition.cellMass
    congr 1
    have hp : P.law (p.cellSet (.inr j)) = ENNReal.ofReal m := by
      rw [show p = packingFinitePartition centers w hdis by rfl,
        packingFinitePartition_cell_measure_eq_map_snd]
      exact hmass _ j
    have hr : onePointDistanceLaw P (centers j) (r.cellSet false) =
        ENNReal.ofReal m := by
      have hrest : Measure.map f (P.law.restrict (p.cellSet (.inr j))) =
          (onePointDistanceLaw P (centers j)).restrict (r.cellSet false) := by
        rw [show p.cellSet (.inr j) =
            {o : Observation | o.2 ∈ Metric.closedBall (centers j) w ∩ P.support} by
          rw [show p = packingFinitePartition centers w hdis by rfl,
            packingFinitePartition_cellSet, packingPartitionSet, hsupport _]
          rfl]
        rw [show r.cellSet false = {z : ℝ × ℝ | z.2 ≤ w} by
          exact packingRadialPartition_cellSet_false w]
        exact map_packingCell_restrict_eq_onePointDistance_restrict P (centers j) w
      have hu := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ) hrest
      calc
        onePointDistanceLaw P (centers j) (r.cellSet false) =
            ((onePointDistanceLaw P (centers j)).restrict (r.cellSet false)) Set.univ := by
          rw [Measure.restrict_apply_univ]
        _ = (Measure.map f (P.law.restrict (p.cellSet (.inr j)))) Set.univ := hu.symm
        _ = P.law (p.cellSet (.inr j)) := by
          rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
            Measure.restrict_apply_univ]
        _ = ENNReal.ofReal m := hp
    rw [hp, hr]
  unfold compressedCoordinateLaw compressPackingCell packingCellExperiment
  unfold canonicalMarkedPoissonSampleLaw
  rw [Measure.map_map
      (measurable_finiteSampleMap _ (packingMarkedDistance_measurable _))
      measurable_orderByMarks]
  have hcomm :
      finiteSampleMap (packingMarkedDistance (centers j)) ∘ orderByMarks =
        orderByMarks ∘ finiteSampleMap
          (fun z : Observation × ℝ => (f z.1, z.2)) := by
    funext s
    exact finiteSampleMap_orderByMarks f s
  rw [hcomm, ← Measure.map_map measurable_orderByMarks
      (measurable_finiteSampleMap _ (by fun_prop))]
  rw [map_finiteMarkedPoissonSampleLaw_finiteSampleMap
    (p.cellObservationLaw P.law (.inr j)) packingMarkLaw f (by fun_prop)
    (lam * p.cellMass P.law (.inr j))]
  calc
    Measure.map orderByMarks
        (finiteMarkedPoissonSampleLaw
          (Measure.map f (p.cellObservationLaw P.law (.inr j))) packingMarkLaw
          (lam * p.cellMass P.law (.inr j))) =
        canonicalMarkedPoissonSampleLaw
          (r.cellObservationLaw (onePointDistanceLaw P (centers j)) false)
          packingMarkLaw
          (lam * r.cellMass (onePointDistanceLaw P (centers j)) false) := by
      unfold canonicalMarkedPoissonSampleLaw
      rw [hmassCell]
      congr 3
    _ = Measure.map (orderByMarks ∘ r.restrictCell false)
        (finiteMarkedPoissonSampleLaw
          (onePointDistanceLaw P (centers j)) packingMarkLaw lam) := by
      exact (map_shortRadiusBlock_finiteMarkedPoissonSampleLaw
        (onePointDistanceLaw P (centers j)) packingMarkLaw w lam).symm

/-- The compressed cell KL budget is at most twice the fixed-size packing
budget, exactly the factor introduced by mean-`2n` Poissonization. -/
-- @node: compressedPackingCellExperiment_klDiv_le
lemma compressedPackingCellExperiment_klDiv_le {M n : ℕ}
    (hn : 1 ≤ n) (hM : 1 ≤ M)
    (centers : Fin M → Score) (w m alpha : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (halpha : 0 ≤ alpha)
    (hpi : ∀ omega j,
      InformationTheory.klDiv
        (compressedSampleLaw (laws omega) n (centers j))
        (compressedSampleLaw
          (laws (Causalean.Stat.flipBit j omega)) n (centers j)) ≤
        ENNReal.ofReal (alpha * Real.log M))
    (j : Fin M) :
    InformationTheory.klDiv
      (compressedCoordinateLaw
        (compressPackingCell centers j)
        (packingCellExperiment (packingFinitePartition centers w hdis)
          laws (2 * n) j false))
      (compressedCoordinateLaw
        (compressPackingCell centers j)
        (packingCellExperiment (packingFinitePartition centers w hdis)
          laws (2 * n) j true)) ≤
      ENNReal.ofReal ((2 * alpha) * Real.log M) := by
  let P0 := laws (packingSingleBit j false)
  let P1 := laws (packingSingleBit j true)
  let Q0 := onePointDistanceLaw P0 (centers j)
  let Q1 := onePointDistanceLaw P1 (centers j)
  let F := orderByMarks ∘ (packingRadialPartition w).restrictCell false
  letI : IsProbabilityMeasure Q0 := onePointDistanceLaw_isProbabilityMeasure _ _
  letI : IsProbabilityMeasure Q1 := onePointDistanceLaw_isProbabilityMeasure _ _
  rw [compressedPackingCellExperiment_eq_shortRadiusBlock centers w m hdis laws
      hsupport hm hmass (2 * n) j false,
    compressedPackingCellExperiment_eq_shortRadiusBlock centers w m hdis laws
      hsupport hm hmass (2 * n) j true]
  have hB : 0 ≤ alpha * Real.log M :=
    mul_nonneg halpha (Real.log_nonneg (by exact_mod_cast hM))
  have hflip : Causalean.Stat.flipBit j (packingSingleBit j false) =
      packingSingleBit j true := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [Causalean.Stat.flipBit, packingSingleBit]
    · simp [Causalean.Stat.flipBit, packingSingleBit, hkj]
  have hfixed : InformationTheory.klDiv
      (Measure.pi fun _ : Fin n => Q0)
      (Measure.pi fun _ : Fin n => Q1) ≤
      ENNReal.ofReal (alpha * Real.log M) := by
    simpa [Q0, Q1, P0, P1, compressedSampleLaw_eq_pi_onePointDistanceLaw,
      hflip] using hpi (packingSingleBit j false) j
  have hpois := markedPoissonKL_le_two_mul_of_piKL Q0 Q1 packingMarkLaw
    n hn hB hfixed
  rw [finiteMeasureMarkedPoissonLaw_probability_eq Q0 Q0,
    finiteMeasureMarkedPoissonLaw_probability_eq Q1 Q0] at hpois
  calc
    InformationTheory.klDiv
        (compressedCoordinateLaw F (finiteMarkedPoissonSampleLaw Q0 packingMarkLaw (2 * n)))
        (compressedCoordinateLaw F (finiteMarkedPoissonSampleLaw Q1 packingMarkLaw (2 * n))) ≤
      InformationTheory.klDiv
        (finiteMarkedPoissonSampleLaw Q0 packingMarkLaw (2 * n))
        (finiteMarkedPoissonSampleLaw Q1 packingMarkLaw (2 * n)) :=
      compressedCoordinateLaw_klDiv_le F
        (measurable_orderByMarks.comp
          ((packingRadialPartition w).measurable_restrictCell false)) _ _
    _ ≤ ENNReal.ofReal (2 * (alpha * Real.log M)) := hpois
    _ = ENNReal.ofReal ((2 * alpha) * Real.log M) := by ring_nf

/-- Splitting the hard-family Poisson law gives the direct-product experiment
with one common complement coordinate and one bit-dependent law per cell. -/
-- @node: packingExperiment_synthesis_law
lemma packingExperiment_synthesis_law {M : ℕ}
    (centers : Fin M → Score) (w m : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (hlocal : ∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict {o | o.2 ∈ packingCell centers w j} =
        (laws omega').law.restrict {o | o.2 ∈ packingCell centers w j})
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hoff : ∀ omega omega',
      (laws omega).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j})
    (lam : ℝ≥0) (omega : Fin M → Bool) :
    (letI : IsProbabilityMeasure (laws omega).law :=
      (laws omega).law_isProbability
    Measure.map synthesizePackingConfiguration
        ((packingCommonExperiment (packingFinitePartition centers w hdis) laws lam).prod
          (Measure.pi fun j =>
            packingCellExperiment (packingFinitePartition centers w hdis)
              laws lam j (omega j))) =
      canonicalMarkedPoissonSampleLaw (laws omega).law packingMarkLaw lam) := by
  let p := packingFinitePartition centers w hdis
  let omega0 : Fin M → Bool := fun _ => false
  letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega0).law := (laws omega0).law_isProbability
  let cellLaw (k : Unit ⊕ Fin M) : Measure (FiniteSample (Observation × ℝ)) :=
    canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega).law k) packingMarkLaw
      (lam * p.cellMass (laws omega).law k)
  have hcoord (j : Fin M) :
      packingCellExperiment p laws lam j (omega j) = cellLaw (.inr j) := by
    symm
    exact packingCanonicalCellLaw_eq_of_bit_eq centers w m hdis laws hm hmass
      hlocal packingMarkLaw lam omega (packingSingleBit j (omega j)) j
      (packingSingleBit_self j (omega j)).symm
  have hcommon :
      (fun _ : Unit => canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
        (lam * p.cellMass (laws omega0).law (.inl ()))) =
      (fun _ : Unit => cellLaw (.inl ())) := by
    funext u
    cases u
    exact packingCanonicalComplementLaw_eq centers w hdis laws hsupport hoff
      packingMarkLaw lam omega0 omega
  have hprod :
      (packingCommonExperiment p laws lam).prod
          (Measure.pi fun j => packingCellExperiment p laws lam j (omega j)) =
        (Measure.pi fun u : Unit => cellLaw (.inl u)).prod
          (Measure.pi fun j : Fin M => cellLaw (.inr j)) := by
    change (Measure.pi (fun _ : Unit => canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
        (lam * p.cellMass (laws omega0).law (.inl ())))).prod
      (Measure.pi fun j => packingCellExperiment p laws lam j (omega j)) = _
    rw [show (fun _ : Unit => canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
        (lam * p.cellMass (laws omega0).law (.inl ()))) =
      (fun u : Unit => cellLaw (.inl u)) from hcommon]
    rw [show (fun j => packingCellExperiment p laws lam j (omega j)) =
        (fun j : Fin M => cellLaw (.inr j)) by
      funext j
      exact hcoord j]
  rw [show packingFinitePartition centers w hdis = p by rfl, hprod]
  calc
    Measure.map synthesizePackingConfiguration
        ((Measure.pi fun u : Unit => cellLaw (.inl u)).prod
          (Measure.pi fun j : Fin M => cellLaw (.inr j))) =
        Measure.map superposeByMarks (Measure.pi cellLaw) := by
      rw [show synthesizePackingConfiguration =
          superposeByMarks ∘
            (MeasurableEquiv.sumPiEquivProdPi
              (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm by rfl,
        ← Measure.map_map
        measurable_superposeByMarks
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm.measurable]
      rw [(measurePreserving_sumPiEquivProdPi_symm cellLaw).map_eq]
    _ = canonicalMarkedPoissonSampleLaw (laws omega).law packingMarkLaw lam := by
      simpa [cellLaw] using
        (map_superposeByMarks_canonicalCellLaws p (laws omega).law
          packingMarkLaw lam)

end CausalSmith.Stat.BddUniformLogPenalty
