/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Conic Duality

This file develops the conic linear-programming duality backbone for partial
identification bounds. It treats sharp bounds as optimal values of linear
programs over a cone in real Hilbert spaces and proves weak duality, a Farkas
feasibility alternative, primal attainment under a closedness qualification,
and zero duality gap under the same qualification.

The main structure `ConicProgram` packages the cone `K`, constraint operator
`A`, right-hand side `b`, and objective direction `c`. The predicates
`PrimalFeasible` and `DualFeasible` define the primal and dual feasible sets,
while `primalValue` and `dualValue` record the corresponding optimal values.
The theorem `weak_duality` gives the pointwise inequality, and
`dualValue_le_primalValue` lifts it to values.

The theorem `farkas` restates conic separation as a feasibility alternative.
The set `augmentedImage` is the closedness constraint qualification used by
`strong_duality_primal_attained` and `strong_duality_zero_gap`, which provide
primal attainment and no duality gap for feasible bounded-below programs.

The Hilbert-space formulation covers infinite-dimensional function spaces used
by proxy and bridge problems. Measure-cone weak-star duality is intentionally
left outside this module; the module note at the end explains the missing
signed-measure and cone infrastructure. -/

open scoped RealInnerProductSpace

namespace Causalean
namespace PartialID

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Primal data of a conic linear program over real Hilbert spaces:
minimize `⟪c, x⟫` subject to `A x = b` and `x ∈ K`. -/
structure ConicProgram (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] where
  /-- The constraint cone (nonnegativity / shape restrictions). -/
  K : ProperCone ℝ E
  /-- The linear constraint operator. -/
  A : E →L[ℝ] F
  /-- The right-hand side (observed-data target). -/
  b : F
  /-- The objective direction. -/
  c : E

namespace ConicProgram

variable (P : ConicProgram E F)

/-- A point is **primal feasible** when it satisfies the equality constraint and
lies in the cone. -/
def PrimalFeasible (x : E) : Prop := P.A x = P.b ∧ x ∈ P.K

/-- A dual multiplier is **dual feasible** when the reduced cost `c - Aᵀ y` lies in
the dual cone `K⋆ = innerDual K`. -/
def DualFeasible (y : F) : Prop :=
  P.c - (ContinuousLinearMap.adjoint P.A) y ∈ ProperCone.innerDual (P.K : Set E)

/-- The **primal optimal value** `inf { ⟪c, x⟫ : x primal feasible }`. -/
noncomputable def primalValue : ℝ :=
  sInf ((fun x => ⟪P.c, x⟫) '' {x | P.PrimalFeasible x})

/-- The **dual optimal value** `sup { ⟪b, y⟫ : y dual feasible }`. -/
noncomputable def dualValue : ℝ :=
  sSup ((fun y => ⟪P.b, y⟫) '' {y | P.DualFeasible y})

/-- **Weak duality (pointwise).**  Any dual-feasible objective value lower-bounds
any primal-feasible objective value. -/
theorem weak_duality {x : E} {y : F}
    (hx : P.PrimalFeasible x) (hy : P.DualFeasible y) :
    ⟪P.b, y⟫ ≤ ⟪P.c, x⟫ := by
  -- Dual feasibility says `0 ≤ ⟪x, c - Aᵀ y⟫` for `x ∈ K`.
  have h0 : 0 ≤ ⟪x, P.c - (ContinuousLinearMap.adjoint P.A) y⟫ :=
    ProperCone.mem_innerDual.mp hy hx.2
  have e1 : ⟪x, P.c - (ContinuousLinearMap.adjoint P.A) y⟫ = ⟪x, P.c⟫ - ⟪P.A x, y⟫ := by
    rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  rw [e1, hx.1] at h0
  -- h0 : 0 ≤ ⟪x, P.c⟫ - ⟪P.b, y⟫
  have ec := real_inner_comm x P.c
  linarith

/-- **Weak duality (value form).**  When both programs are feasible,
`dualValue ≤ primalValue`.  (Boundedness is not needed: the pointwise bound
exhibits `primalValue` as an explicit upper bound for the dual values.) -/
theorem dualValue_le_primalValue
    (hP : {x | P.PrimalFeasible x}.Nonempty) (hD : {y | P.DualFeasible y}.Nonempty) :
    P.dualValue ≤ P.primalValue := by
  rw [dualValue, primalValue]
  refine csSup_le (hD.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  refine le_csInf (hP.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact P.weak_duality hx hy

/-- **Farkas alternative / feasibility engine.**  The point `b` lies in the closed
image cone `A(K)` iff every direction `y` whose pullback `Aᵀ y` lies in the dual
cone has nonnegative pairing `0 ≤ ⟪b, y⟫`.  This is the strong-duality engine: a
restatement of `ProperCone.relative_hyperplane_separation` in conic-program
notation.  `ProperCone.map` bakes in the closure of `A(K)`, which is exactly the
constraint-qualification gap between this and literal primal feasibility. -/
theorem farkas {b : F} :
    b ∈ ProperCone.map P.A P.K ↔
      ∀ y : F, (ContinuousLinearMap.adjoint P.A) y ∈ ProperCone.innerDual (P.K : Set E)
        → 0 ≤ ⟪b, y⟫ :=
  ProperCone.relative_hyperplane_separation

/-- The **augmented image cone** `{ (A x, ⟪c, x⟫) : x ∈ K }` in `F × ℝ`.  Its
closedness is the constraint qualification for primal attainment, and the
geometry (a boundary point `(b, primalValue)`) is where the dual certificate is
read off. -/
def augmentedImage : Set (F × ℝ) := (fun x => (P.A x, ⟪P.c, x⟫)) '' (P.K : Set E)

/-- **Strong duality I — primal attainment (closedness CQ).**  If the augmented
image cone is closed and the program is feasible and bounded below, the primal
optimum is *attained*: some feasible point achieves `primalValue`.  This is the
"there is an extremal data-generating distribution" half of sharpness.

Proof: the value set `{⟪c,x⟫ : x feasible}` is the slice `r ↦ (b, r)` of the
closed `augmentedImage`, hence closed; a nonempty closed set in `ℝ` bounded below
contains its infimum (`IsClosed.csInf_mem`). -/
theorem strong_duality_primal_attained
    (hP : {x | P.PrimalFeasible x}.Nonempty)
    (hbdd : BddBelow ((fun x => ⟪P.c, x⟫) '' {x | P.PrimalFeasible x}))
    (hCQ : IsClosed P.augmentedImage) :
    ∃ x, P.PrimalFeasible x ∧ ⟪P.c, x⟫ = P.primalValue := by
  have hSeq : (fun x => ⟪P.c, x⟫) '' {x | P.PrimalFeasible x}
      = (fun r : ℝ => (P.b, r)) ⁻¹' P.augmentedImage := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx.2, by simp only [hx.1]⟩
    · rintro ⟨x, hxK, hxeq⟩
      exact ⟨x, ⟨(Prod.ext_iff.mp hxeq).1, hxK⟩, (Prod.ext_iff.mp hxeq).2⟩
  have hScl : IsClosed ((fun x => ⟪P.c, x⟫) '' {x | P.PrimalFeasible x}) := by
    rw [hSeq]; exact hCQ.preimage (by fun_prop)
  have hmem := hScl.csInf_mem (hP.image _) hbdd
  obtain ⟨x, hx, hxval⟩ := hmem
  exact ⟨x, hx, hxval⟩

/-- **Strong duality II — zero gap (closedness CQ).**  If the augmented image cone
is closed (the *same* CQ as primal attainment) and the program is feasible and
bounded below, there is no duality gap: `primalValue = dualValue`.

Closedness alone suffices — **no Slater / interior condition is needed** (and the
classical interior Slater is anyway vacuous for the positive cone of an
infinite-dimensional space).  Reason: closedness gives primal attainment, and
`⟪c,x⟫ ≥ primalValue` on the feasible set then rules out the degenerate
(`s ≤ 0`) separating hyperplanes — so the certificate is never vertical.

PROOF: For each `ε > 0` separate the point `(b, primalValue − ε)` from the
closed augmented cone `map Ã K` (with `Ã x = (A x, ⟪c,x⟫) : F × ℝ`) using
`ProperCone.hyperplane_separation_point` (locally-convex separation on the
normed product `F × ℝ`; **no** inner product on `F × ℝ` is needed). The point is
outside the cone because `↑(map Ã K) = closure (Ã '' K) = augmentedImage`
(closed by `hCQ`), and a feasible witness for `(b, primalValue − ε)` would force
`⟪c,x⟫ = primalValue − ε < primalValue`, contradicting the lower bound. Decompose
the separating functional `g : (F × ℝ) →L[ℝ] ℝ` as `g (v,t) = ⟪y₀,v⟫ + s·t`,
where `y₀` is the Riesz representative of `v ↦ g (v,0)` and `s := g (0,1)`. Then
`s = 0` is impossible (primal feasibility gives `⟪y₀,b⟫ ≥ 0` while separation
gives `⟪y₀,b⟫ < 0`) and `s < 0` is impossible (`⟪c,x⟫ ≥ primalValue`); so `s > 0`
and `ȳ := −(1/s)•y₀` is dual feasible with `⟪b, ȳ⟫ > primalValue − ε`. Letting
`ε → 0` gives `primalValue ≤ dualValue`; combined with weak duality, equality. -/
theorem strong_duality_zero_gap
    (hP : {x | P.PrimalFeasible x}.Nonempty)
    (hbdd : BddBelow ((fun x => ⟪P.c, x⟫) '' {x | P.PrimalFeasible x}))
    (hCQ : IsClosed P.augmentedImage) :
    P.primalValue = P.dualValue := by
  -- The augmented operator `Ã x = (A x, ⟪c, x⟫)`.
  set Ã : E →L[ℝ] (F × ℝ) := (P.A).prod (innerSL ℝ P.c) with hÃdef
  have hÃapp : ∀ x : E, Ã x = (P.A x, ⟪P.c, x⟫) := fun x => rfl
  -- The underlying `PointedCone.map` image set is exactly the augmented image.
  have hpcimg : ((PointedCone.map (Ã : E →ₗ[ℝ] (F × ℝ)) (P.K : PointedCone ℝ E)) : Set (F × ℝ))
      = P.augmentedImage := by
    rw [PointedCone.coe_map]
    ext z
    simp only [augmentedImage, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hÃapp x).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, hÃapp x⟩
  -- `p* := primalValue` is a finite lower bound for the feasible objective values.
  set S : Set ℝ := (fun x => ⟪P.c, x⟫) '' {x | P.PrimalFeasible x} with hSdef
  have hSne : S.Nonempty := hP.image _
  have hlb : ∀ x : E, P.PrimalFeasible x → P.primalValue ≤ ⟪P.c, x⟫ := by
    intro x hx
    exact csInf_le hbdd ⟨x, hx, rfl⟩
  -- (A) dualValue ≤ primalValue: every dual-feasible value is ≤ every feasible objective,
  --     hence ≤ the infimum p*.
  have hA : ∀ y : F, P.DualFeasible y → ⟪P.b, y⟫ ≤ P.primalValue := by
    intro y hy
    refine le_csInf hSne ?_
    rintro _ ⟨x, hx, rfl⟩
    exact P.weak_duality hx hy
  -- (B) primalValue ≤ dualValue, via separation.
  -- First: for every ε > 0 there is a dual-feasible ȳ with ⟪b, ȳ⟫ > p* - ε.
  have hB : ∀ ε : ℝ, 0 < ε → ∃ y : F, P.DualFeasible y ∧ P.primalValue - ε < ⟪P.b, y⟫ := by
    intro ε hε
    -- The point (b, p* - ε) is not in the map cone.
    have hnotmem : (P.b, P.primalValue - ε) ∉ ProperCone.map Ã P.K := by
      intro hmem
      have hcl : (P.b, P.primalValue - ε)
          ∈ (PointedCone.map (Ã : E →ₗ[ℝ] (F × ℝ)) (P.K : PointedCone ℝ E)).closure :=
        ProperCone.mem_map.mp hmem
      rw [PointedCone.mem_closure] at hcl
      -- closure of the augmented image is itself, since it is closed.
      have : (P.b, P.primalValue - ε) ∈ P.augmentedImage := by
        have hset : closure
            ((PointedCone.map (Ã : E →ₗ[ℝ] (F × ℝ)) (P.K : PointedCone ℝ E)) : Set (F × ℝ))
            = P.augmentedImage := by
          rw [hpcimg]; exact hCQ.closure_eq
        rwa [hset] at hcl
      obtain ⟨x, hxK, hxeq⟩ := this
      have h1 : P.A x = P.b := (Prod.ext_iff.mp hxeq).1
      have h2 : ⟪P.c, x⟫ = P.primalValue - ε := (Prod.ext_iff.mp hxeq).2
      have hfeas : P.PrimalFeasible x := ⟨h1, hxK⟩
      have := hlb x hfeas
      rw [h2] at this
      linarith
    -- Separate.
    obtain ⟨g, hgpos, hgneg⟩ :=
      ProperCone.hyperplane_separation_point (ProperCone.map Ã P.K) hnotmem
    -- Decompose g into the F-part (Riesz) and the ℝ-part s := g(0,1).
    set s : ℝ := g (0, 1) with hsdef
    set φ : F →L[ℝ] ℝ := g.comp ((ContinuousLinearMap.inl ℝ F ℝ)) with hφdef
    -- φ v = g (v, 0); Riesz representative y₀.
    set y₀ : F := (InnerProductSpace.toDual ℝ F).symm φ with hy₀def
    have hφapp : ∀ v : F, φ v = ⟪y₀, v⟫ := by
      intro v
      rw [hy₀def]
      rw [InnerProductSpace.toDual_symm_apply]
    -- g decomposes: g (v, t) = ⟪y₀, v⟫ + t * s.
    have hgdecomp : ∀ (v : F) (t : ℝ), g (v, t) = ⟪y₀, v⟫ + s * t := by
      intro v t
      have hvt : ((v, t) : F × ℝ) = (v, 0) + t • (0, 1) := by
        simp
      rw [hvt, map_add, map_smul]
      have hv : g (v, 0) = ⟪y₀, v⟫ := by
        rw [← hφapp v]; rfl
      rw [hv]
      simp only [hsdef, smul_eq_mul]
      ring
    -- (i): ∀ x ∈ K, 0 ≤ ⟪y₀, A x⟫ + s * ⟪c, x⟫.
    have hi : ∀ x : E, x ∈ P.K → 0 ≤ ⟪y₀, P.A x⟫ + s * ⟪P.c, x⟫ := by
      intro x hx
      have hxmem : Ã x ∈ ProperCone.map Ã P.K := by
        apply ProperCone.mem_map.mpr
        rw [PointedCone.mem_closure]
        apply subset_closure
        -- Ã x ∈ (PointedCone.map ↑Ã ↑P.K : Set _) = augmentedImage
        rw [hpcimg]
        exact ⟨x, hx, rfl⟩
      have := hgpos (Ã x) hxmem
      rw [hÃapp x, hgdecomp] at this
      exact this
    -- (ii): ⟪y₀, b⟫ + (p* - ε) * s < 0.
    have hii : ⟪y₀, P.b⟫ + s * (P.primalValue - ε) < 0 := by
      have := hgneg
      rw [hgdecomp] at this
      exact this
    -- Get a feasible point x₀.
    obtain ⟨x₀, hx₀⟩ := hP
    have hx₀K : x₀ ∈ P.K := hx₀.2
    have hx₀A : P.A x₀ = P.b := hx₀.1
    have hx₀val : P.primalValue ≤ ⟪P.c, x₀⟫ := hlb x₀ hx₀
    -- Case on s.
    rcases lt_trichotomy s 0 with hs | hs | hs
    · -- s < 0 impossible.
      exfalso
      have h1 := hi x₀ hx₀K
      rw [hx₀A] at h1
      -- 0 ≤ ⟪y₀, b⟫ + s * ⟪c, x₀⟫
      -- since s < 0 and ⟪c,x₀⟫ ≥ p*: s * ⟪c,x₀⟫ ≤ s * p*
      have hmul : s * ⟪P.c, x₀⟫ ≤ s * P.primalValue := by
        apply mul_le_mul_of_nonpos_left hx₀val (le_of_lt hs)
      -- (ii): ⟪y₀,b⟫ + (p*-ε)*s < 0, i.e. ⟪y₀,b⟫ + s*p* - s*ε < 0
      nlinarith [hii, h1, hmul, hε, hs]
    · -- s = 0 impossible.
      exfalso
      have h1 := hi x₀ hx₀K
      rw [hx₀A, hs] at h1
      simp only [zero_mul, add_zero] at h1
      -- h1 : 0 ≤ ⟪y₀, b⟫
      have h2 := hii
      rw [hs] at h2
      simp only [zero_mul, add_zero] at h2
      -- h2 : ⟪y₀, b⟫ < 0
      linarith
    · -- s > 0: ȳ := -(1/s) • y₀ is dual feasible with ⟪b, ȳ⟫ > p* - ε.
      refine ⟨-(1/s) • y₀, ?_, ?_⟩
      · -- dual feasibility
        rw [DualFeasible, ProperCone.mem_innerDual]
        intro x hx
        have hred : ⟪x, P.c - (ContinuousLinearMap.adjoint P.A) (-(1/s) • y₀)⟫
            = (1/s) * (⟪y₀, P.A x⟫ + s * ⟪P.c, x⟫) := by
          rw [inner_sub_right]
          rw [map_smul, inner_smul_right]
          rw [ContinuousLinearMap.adjoint_inner_right]
          rw [real_inner_comm x P.c, real_inner_comm (P.A x) y₀]
          field_simp
          ring
        rw [hred]
        have hpos : (0 : ℝ) ≤ 1/s := le_of_lt (by positivity)
        exact mul_nonneg hpos (hi x hx)
      · -- value bound
        have hval : ⟪P.b, -(1/s) • y₀⟫ = -(1/s) * ⟪y₀, P.b⟫ := by
          rw [inner_smul_right, real_inner_comm P.b y₀]
        rw [hval]
        -- from (ii): ⟪y₀, b⟫ + s*(p*-ε) < 0; multiply by 1/s > 0.
        have hsinv : (0:ℝ) < 1 / s := by positivity
        have key : (1/s) * (⟪y₀, P.b⟫ + s * (P.primalValue - ε)) < (1/s) * 0 :=
          mul_lt_mul_of_pos_left hii hsinv
        have hexp : (1/s) * (⟪y₀, P.b⟫ + s * (P.primalValue - ε))
            = (1/s) * ⟪y₀, P.b⟫ + (P.primalValue - ε) := by
          field_simp
        rw [hexp, mul_zero] at key
        linarith [key]
  -- Assemble: dualValue ≥ p* and dualValue ≤ p*.
  have hDne : {y | P.DualFeasible y}.Nonempty := by
    obtain ⟨y, hy, _⟩ := hB 1 (by norm_num)
    exact ⟨y, hy⟩
  -- dualValue ≤ primalValue
  have hle : P.dualValue ≤ P.primalValue := by
    rw [dualValue]
    refine csSup_le (hDne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hA y hy
  -- primalValue ≤ dualValue
  have hge : P.primalValue ≤ P.dualValue := by
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    obtain ⟨y, hy, hyval⟩ := hB ε hε
    have hbdd' : BddAbove ((fun y => ⟪P.b, y⟫) '' {y | P.DualFeasible y}) := by
      refine ⟨P.primalValue, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hA z hz
    have : ⟪P.b, y⟫ ≤ P.dualValue := le_csSup hbdd' ⟨y, hy, rfl⟩
    linarith
  linarith

end ConicProgram

/-!
## Module note — why the measure cone is out of scope (for now)

The genuinely non-Hilbert partial-ID programs are LPs over a cone of **measures**
paired with `C(X)` via `⟪μ, f⟫ = ∫ f dμ`.  Mathlib cannot yet express this as a
`ProperCone ℝ _`:

* `MeasureTheory.FiniteMeasure` is only a `Module ℝ≥0`, not a `Module ℝ`
  (no signed structure), so it is not an `ℝ`-vector space.
* it carries no `PartialOrder` / `IsOrderedAddMonoid` / `OrderClosedTopology`
  instances, so the nonnegative measures are not packaged as a cone.
* the weak-∗ topology (induced from `WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)`) is not an
  order topology.

Reaching the measure case therefore requires new infrastructure: a signed-measure
`ℝ`-module, its nonnegative `ProperCone`, and the `C(X)`-pairing as a continuous
perfect pairing (Riesz–Markov, `MeasureTheory.Integral.RieszMarkovKakutani`).
That is tracked as a separate effort.
-/

end PartialID
end Causalean
