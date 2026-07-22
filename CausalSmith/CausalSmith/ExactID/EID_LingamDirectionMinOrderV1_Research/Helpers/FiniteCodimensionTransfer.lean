/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Codimension chains in the finite retained cumulant band

The theorem statement uses the function-valued `CumVec` ambient.  Every set in
the exceptional-locus argument is nevertheless supported on a finite retained
band.  This file transfers irreducible components and endpoint-fixed strict
chains, not only closedness and irreducibility, to the corresponding finite
complex affine space.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FiniteCumBand
import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.CodimensionOne

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (IsIrreducibleAffineComponent HasAffineCodimensionIn)

private lemma restrict_image_extend (L : ℕ)
    (A : Set (RetainedCumCoord L → ℂ)) :
    restrictCumBand L '' (extendCumBand L '' A) = A := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨extendCumBand L x, ⟨x, hx, rfl⟩, restrict_extendCumBand L x⟩

private lemma extend_image_restrict {L : ℕ} {A : Set (CumVec ℂ)}
    (hA : A ⊆ bandSupportedCumulants L) :
    extendCumBand L '' (restrictCumBand L '' A) = A := by
  ext t
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    simpa [extend_restrictCumBand (hA hs)] using hs
  · intro ht
    exact ⟨restrictCumBand L t, ⟨t, ht, rfl⟩,
      extend_restrictCumBand (hA ht)⟩

private lemma image_strictMono_on {α β ι : Type*} [Preorder ι]
    (f : α → β) {S : Set α} (hf : Set.InjOn f S)
    {chain : ι → Set α} (hc : StrictMono chain)
    (hsub : ∀ i, chain i ⊆ S) :
    StrictMono (fun i => f '' chain i) := by
  intro i j hij
  have hs := hc hij
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hs.le, ?_⟩
  intro heq
  change f '' chain i = f '' chain j at heq
  apply hs.ne
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hfy⟩ : ∃ y ∈ chain j, f y = f x := by
      have : f x ∈ f '' chain j := by
        rw [← heq]
        exact ⟨x, hx, rfl⟩
      simpa [eq_comm] using this
    exact hf (hsub j hy) (hsub i hx) hfy ▸ hy
  · intro hx
    obtain ⟨y, hy, hfy⟩ : ∃ y ∈ chain i, f y = f x := by
      have : f x ∈ f '' chain i := by
        rw [heq]
        exact ⟨x, hx, rfl⟩
      simpa [eq_comm] using this
    exact hf (hsub i hy) (hsub j hx) hfy ▸ hy

private lemma extendCumBand_injective (L : ℕ) :
    Function.Injective (extendCumBand L) := by
  intro x y h
  simpa using congrArg (restrictCumBand L) h

private lemma image_strictMono_extend {L : ℕ} {ι : Type*} [Preorder ι]
    {chain : ι → Set (RetainedCumCoord L → ℂ)} (hc : StrictMono chain) :
    StrictMono (fun i => extendCumBand L '' chain i) := by
  apply image_strictMono_on (extendCumBand L)
    (S := Set.univ) (fun _ _ _ _ h => extendCumBand_injective L h) hc
  exact fun _ => Set.subset_univ _

/-- Irreducible-component maximality is preserved by finite-band
restriction. -/
theorem irreducibleComponent_iff_affineComponent {L : ℕ}
    {C Z : Set (CumVec ℂ)} (hC : C ⊆ bandSupportedCumulants L)
    (hZ : Z ⊆ bandSupportedCumulants L) :
    IsIrreducibleComponent C Z ↔
      IsIrreducibleAffineComponent
        (restrictCumBand L '' C) (restrictCumBand L '' Z) := by
  constructor
  · intro h
    refine ⟨(irreducibleZariskiClosed_iff_affine hC).mp h.1,
      Set.image_mono h.2.1, ?_⟩
    intro D hD hCD hDZ
    let D' := extendCumBand L '' D
    have hD'band : D' ⊆ bandSupportedCumulants L := by
      rintro _ ⟨x, _, rfl⟩
      exact extendCumBand_mem_band L x
    have hD'irr : IsIrreducibleZariskiClosed D' := by
      apply (irreducibleZariskiClosed_iff_affine hD'band).mpr
      simpa [D', restrict_image_extend] using hD
    have hCD' : C ⊆ D' := by
      rw [← (image_restrictCumBand_subset_iff hC hD'band)]
      simpa [D', restrict_image_extend] using hCD
    have hD'Z : D' ⊆ Z := by
      rw [← (image_restrictCumBand_subset_iff hD'band hZ)]
      simpa [D', restrict_image_extend] using hDZ
    have heq := h.2.2 D' hD'irr hCD' hD'Z
    have := congrArg (fun S => restrictCumBand L '' S) heq
    simpa [D', restrict_image_extend] using this
  · intro h
    refine ⟨(irreducibleZariskiClosed_iff_affine hC).mpr h.1,
      (image_restrictCumBand_subset_iff hC hZ).mp h.2.1, ?_⟩
    intro D hD hCD hDZ
    have hDband : D ⊆ bandSupportedCumulants L := hDZ.trans hZ
    have hDi := (irreducibleZariskiClosed_iff_affine hDband).mp hD
    have himage := h.2.2 (restrictCumBand L '' D) hDi
      ((image_restrictCumBand_subset_iff hC hDband).mpr hCD)
      ((image_restrictCumBand_subset_iff hDband hZ).mpr hDZ)
    exact image_restrictCumBand_inj hDband hC himage

/-- Exact custom codimension in a band-supported `CumVec` set is equivalent to
the same endpoint-fixed irreducible-chain statement in the finite retained
affine space. -/
theorem hasCodimensionIn_iff_affineCodimensionIn {L d : ℕ}
    {Z X : Set (CumVec ℂ)} (hZ : Z ⊆ bandSupportedCumulants L)
    (hX : X ⊆ bandSupportedCumulants L) :
    HasCodimensionIn d Z X ↔
      HasAffineCodimensionIn d
        (restrictCumBand L '' Z) (restrictCumBand L '' X) := by
  let f := restrictCumBand L
  let g := extendCumBand L
  have hf := restrictCumBand_injective_on_band L
  constructor
  · rintro ⟨hall, C, hC, hno⟩
    constructor
    · intro D hD
      let D' := g '' D
      have hD'band : D' ⊆ bandSupportedCumulants L := by
        rintro _ ⟨x, _, rfl⟩
        exact extendCumBand_mem_band L x
      have hD'comp : IsIrreducibleComponent D' Z := by
        apply (irreducibleComponent_iff_affineComponent hD'band hZ).mpr
        simpa [D', f, g, restrict_image_extend] using hD
      obtain ⟨chain, hmono, hirr, hzero, hlast⟩ := hall D' hD'comp
      refine ⟨fun i => f '' chain i,
        image_strictMono_on f hf hmono
          (fun i => (hmono.monotone (Fin.le_last i)).trans
            (hlast.le.trans hX)), ?_, ?_, ?_⟩
      · intro i
        have hiband : chain i ⊆ bandSupportedCumulants L := by
          exact (hmono.monotone (Fin.le_last i)) |>.trans (hlast.le.trans hX)
        exact (irreducibleZariskiClosed_iff_affine hiband).mp (hirr i)
      · change f '' chain 0 = D
        rw [hzero]
        simpa [D', f, g, restrict_image_extend]
      · change f '' chain (Fin.last d) = f '' X
        rw [hlast]
    · refine ⟨f '' C, ?_, ?_⟩
      · exact (irreducibleComponent_iff_affineComponent
          (hC.2.1.trans hZ) hZ).mp hC
      · rintro ⟨chain, hmono, hirr, hzero, hlast⟩
        apply hno
        refine ⟨fun i => g '' chain i, image_strictMono_extend hmono, ?_, ?_, ?_⟩
        · intro i
          have hiband : g '' chain i ⊆ bandSupportedCumulants L := by
            rintro _ ⟨x, _, rfl⟩
            exact extendCumBand_mem_band L x
          apply (irreducibleZariskiClosed_iff_affine hiband).mpr
          simpa [g, restrict_image_extend] using hirr i
        · change g '' chain 0 = C
          rw [hzero]
          exact extend_image_restrict (hC.2.1.trans hZ)
        · change g '' chain (Fin.last (d + 1)) = X
          rw [hlast]
          exact extend_image_restrict hX
  · rintro ⟨hall, C, hC, hno⟩
    constructor
    · intro D hD
      have hDband := hD.2.1.trans hZ
      have hDfcomp := (irreducibleComponent_iff_affineComponent hDband hZ).mp hD
      obtain ⟨chain, hmono, hirr, hzero, hlast⟩ := hall (f '' D) hDfcomp
      refine ⟨fun i => g '' chain i, image_strictMono_extend hmono, ?_, ?_, ?_⟩
      · intro i
        have hiband : g '' chain i ⊆ bandSupportedCumulants L := by
          rintro _ ⟨x, _, rfl⟩
          exact extendCumBand_mem_band L x
        apply (irreducibleZariskiClosed_iff_affine hiband).mpr
        simpa [g, restrict_image_extend] using hirr i
      · change g '' chain 0 = D
        rw [hzero]
        exact extend_image_restrict hDband
      · change g '' chain (Fin.last d) = X
        rw [hlast]
        exact extend_image_restrict hX
    · let D := g '' C
      have hDband : D ⊆ bandSupportedCumulants L := by
        rintro _ ⟨x, _, rfl⟩
        exact extendCumBand_mem_band L x
      have hDcomp : IsIrreducibleComponent D Z := by
        apply (irreducibleComponent_iff_affineComponent hDband hZ).mpr
        simpa [D, f, g, restrict_image_extend] using hC
      refine ⟨D, hDcomp, ?_⟩
      rintro ⟨chain, hmono, hirr, hzero, hlast⟩
      apply hno
      refine ⟨fun i => f '' chain i,
        image_strictMono_on f hf hmono
          (fun i => (hmono.monotone (Fin.le_last i)).trans
            (hlast.le.trans hX)), ?_, ?_, ?_⟩
      · intro i
        have hiband := (hmono.monotone (Fin.le_last i)).trans
          (hlast.le.trans hX)
        exact (irreducibleZariskiClosed_iff_affine hiband).mp (hirr i)
      · change f '' chain 0 = C
        rw [hzero]
        simpa [D, f, g, restrict_image_extend]
      · change f '' chain (Fin.last (d + 1)) = f '' X
        rw [hlast]

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
