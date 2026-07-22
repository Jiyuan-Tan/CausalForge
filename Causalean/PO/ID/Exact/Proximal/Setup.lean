/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Assumptions.IndepCF

/-! # Proximal Setup

This file defines the data layer for proximal average treatment effect
identification. `POProximalSystem` records a covariate, binary treatment,
treatment-side proxy, outcome-side proxy, real-valued outcome, and latent
confounder. The namespace then supplies the factual maps `X`, `A`, `Z`, `W`,
`Y`, and `U`; the treatment-specific potential outcome `YofA`; tuple-valued
conditioning targets `AZX`, `AUX`, `UX`, and `AZUX`; and the generated
sigma-algebras `σ_AZX`, `σ_AUX`, `σ_UX`, and `σ_AZUX` with their ambient
sub-sigma-algebra lemmas.

Assumption bundles and the identification theorem are kept in the companion
`Proximal.Assumptions` and `Proximal.Main` files. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A proximal ATE system with six distinguished potential-outcome variables:
covariate `Xvar`, binary treatment `Avar`, treatment-side proxy `Zvar`,
outcome-side proxy `Wvar`, real outcome `Yvar`, and latent confounder `Uvar`
(`def:po-proximal-system`). -/
structure POProximalSystem (P : POSystem)
    (γ_X γ_Z γ_W γ_U : Type*)
    [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
    [MeasurableSpace γ_W] [MeasurableSpace γ_U] where
  /-- Observed covariate variable. -/
  Xvar : POVar P γ_X
  /-- Binary treatment variable. -/
  Avar : POVar P Bool
  /-- Treatment-side proxy variable. -/
  Zvar : POVar P γ_Z
  /-- Outcome-side proxy variable. -/
  Wvar : POVar P γ_W
  /-- Real-valued outcome variable. -/
  Yvar : POVar P ℝ
  /-- Latent confounder variable. -/
  Uvar : POVar P γ_U

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]
  (S : POProximalSystem P γ_X γ_Z γ_W γ_U)

/-! ### Factual maps -/

/-- Factual covariate `X = Xvar(r∅)`. -/
noncomputable def X : P.Ω → γ_X := S.Xvar.factual

/-- Factual treatment `A = Avar(r∅)`. -/
noncomputable def A : P.Ω → Bool := S.Avar.factual

/-- Factual treatment-side proxy `Z = Zvar(r∅)`. -/
noncomputable def Z : P.Ω → γ_Z := S.Zvar.factual

/-- Factual outcome-side proxy `W = Wvar(r∅)`. -/
noncomputable def W : P.Ω → γ_W := S.Wvar.factual

/-- Factual outcome `Y = Yvar(r∅)`. -/
noncomputable def Y : P.Ω → ℝ := S.Yvar.factual

/-- Latent confounder `U = Uvar(r∅)`. -/
noncomputable def U : P.Ω → γ_U := S.Uvar.factual

/-! ### Measurability of factual maps -/

/-- The factual covariate is measurable. -/
lemma measurable_X : Measurable S.X := S.Xvar.measurable_factual
/-- The factual treatment is measurable. -/
lemma measurable_A : Measurable S.A := S.Avar.measurable_factual
/-- The factual treatment-side proxy is measurable. -/
lemma measurable_Z : Measurable S.Z := S.Zvar.measurable_factual
/-- The factual outcome-side proxy is measurable. -/
lemma measurable_W : Measurable S.W := S.Wvar.measurable_factual
/-- The factual outcome is measurable. -/
lemma measurable_Y : Measurable S.Y := S.Yvar.measurable_factual
/-- The factual latent confounder is measurable. -/
lemma measurable_U : Measurable S.U := S.Uvar.measurable_factual

/-! ### Counterfactual outcome under treatment -/

/-- Treatment-specific potential outcome `Y(a) := Yvar.cfUnder Avar a`. -/
noncomputable def YofA (a : Bool) : P.Ω → ℝ := S.Yvar.cfUnder S.Avar a

/-- The treatment-specific potential outcome is measurable. -/
lemma measurable_YofA (a : Bool) : Measurable (S.YofA a) :=
  S.Yvar.measurable_cfUnder S.Avar a

/-! ### Tuple maps (used as conditioning targets) -/

/-- `(A, Z, X) : P.Ω → Bool × γ_Z × γ_X`. -/
noncomputable def AZX : P.Ω → Bool × γ_Z × γ_X :=
  fun ω => (S.A ω, S.Z ω, S.X ω)

/-- `(A, U, X) : P.Ω → Bool × γ_U × γ_X`. -/
noncomputable def AUX : P.Ω → Bool × γ_U × γ_X :=
  fun ω => (S.A ω, S.U ω, S.X ω)

/-- `(U, X) : P.Ω → γ_U × γ_X`. -/
noncomputable def UX : P.Ω → γ_U × γ_X :=
  fun ω => (S.U ω, S.X ω)

/-- `(A, Z, U, X) : P.Ω → Bool × γ_Z × γ_U × γ_X`. -/
noncomputable def AZUX : P.Ω → Bool × γ_Z × γ_U × γ_X :=
  fun ω => (S.A ω, S.Z ω, S.U ω, S.X ω)

/-! ### Measurability of tuple maps -/

/-- The treatment, treatment-side proxy, and covariate tuple is measurable. -/
lemma measurable_AZX : Measurable S.AZX :=
  Measurable.prodMk S.measurable_A (Measurable.prodMk S.measurable_Z S.measurable_X)

/-- The treatment, latent confounder, and covariate tuple is measurable. -/
lemma measurable_AUX : Measurable S.AUX :=
  Measurable.prodMk S.measurable_A (Measurable.prodMk S.measurable_U S.measurable_X)

/-- The latent confounder and covariate tuple is measurable. -/
lemma measurable_UX : Measurable S.UX :=
  Measurable.prodMk S.measurable_U S.measurable_X

/-- The treatment, treatment-side proxy, latent confounder, and covariate tuple is
measurable. -/
lemma measurable_AZUX : Measurable S.AZUX :=
  Measurable.prodMk S.measurable_A
    (Measurable.prodMk S.measurable_Z (Measurable.prodMk S.measurable_U S.measurable_X))

/-! ### σ-algebra abbreviations -/

/-- σ-algebra generated by `(A, Z, X)`. -/
noncomputable def σ_AZX : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.AZX inferInstance

/-- σ-algebra generated by `(A, U, X)`. -/
noncomputable def σ_AUX : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.AUX inferInstance

/-- σ-algebra generated by `(U, X)`. -/
noncomputable def σ_UX : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.UX inferInstance

/-- σ-algebra generated by `(A, Z, U, X)`. -/
noncomputable def σ_AZUX : MeasurableSpace P.Ω :=
  MeasurableSpace.comap S.AZUX inferInstance

/-! ### σ-algebra sub-algebra lemmas -/

/-- The sigma-algebra generated by treatment, treatment-side proxy, and covariate
is a sub-sigma-algebra of the ambient space. -/
lemma σ_AZX_le : S.σ_AZX ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.measurable_AZX.comap_le

/-- The sigma-algebra generated by treatment, latent confounder, and covariate is
a sub-sigma-algebra of the ambient space. -/
lemma σ_AUX_le : S.σ_AUX ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.measurable_AUX.comap_le

/-- The sigma-algebra generated by latent confounder and covariate is a
sub-sigma-algebra of the ambient space. -/
lemma σ_UX_le : S.σ_UX ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.measurable_UX.comap_le

/-- The sigma-algebra generated by treatment, treatment-side proxy, latent
confounder, and covariate is a sub-sigma-algebra of the ambient space. -/
lemma σ_AZUX_le : S.σ_AZUX ≤ (inferInstance : MeasurableSpace P.Ω) :=
  S.measurable_AZUX.comap_le

end POProximalSystem

end PO
end Causalean
