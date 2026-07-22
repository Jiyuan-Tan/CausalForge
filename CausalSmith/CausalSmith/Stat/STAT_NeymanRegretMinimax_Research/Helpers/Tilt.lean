/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Local alternative paths: the linear-tilt construction and its validity

Stage-2 scaffold.  The local-path handle `IsLocalPath`, the linear-tilt path
validity lemma, path existence, and band-continuity of linear tilts.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.TiltScore

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics
open scoped BigOperators Topology

-- @node: def:local-path-handle
/-- Local-path handle `nu^(u,·)`: a **bounded-support** path `h ↦ p h` of laws on
`[0,1]²` through `nu` (`p 0 = nu`) that (0a) keeps every `p h` a probability measure
(a *law*, per the core's `nu^(u,h) ∈ laws on [0,1]²`), (0b) keeps every `p h`
supported on `[0,1]²` (so the potential outcomes stay bounded along the whole path —
the note's "bounded-support path"), (i) preserves each arm mean exactly, (ii)
perturbs the arm second moment as `m_a(h)² = m_a² + h u_a + o(h)`, and (iii) has KL
expansion `KL(nu_a^h, nu_a) = (h²/2) J_{a,nu}(u_a) + o(h²)`.  (Both the
probability-measure clause (0a) and the bounded-support clause (0b) are stated here
in the signature — together they pin `nu^(u,h)`'s space to laws on `[0,1]²` — not
merely carried at consumers, per the redirect.)
@realizes nu^(u,h)(local alternative law on [0,1]²: probability measure + supp ⊆ [0,1]²)
@realizes h(path amplitude) -/
def IsLocalPath (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ) (p : ℝ → Measure (ℝ × ℝ)) : Prop :=
  p 0 = nu
  -- @realizes nu^(u,h)(each p h a law: probability measure, total mass 1)
  ∧ (∀ h : ℝ, IsProbabilityMeasure (p h))
  -- @realizes Y_t(0), Y_t(1)(path supp ⊆ [0,1]²: potential outcomes bounded along nu^(u,h))
  ∧ (∀ h : ℝ, BoundedOutcomes (p h))
  ∧ (∀ (h : ℝ) (a : Fin 2),
      ∫ y, y ∂(armMarginal (p h) a) = ∫ y, y ∂(armMarginal nu a))
  ∧ (∀ a : Fin 2,
      (fun h => rootSecondMoment (p h) a ^ 2
          - (rootSecondMoment nu a ^ 2 + h * (if a = 0 then u.1 else u.2)))
        =o[𝓝 (0 : ℝ)] fun h => h)
  ∧ (∀ a : Fin 2,
      (fun h => (InformationTheory.klDiv (armMarginal (p h) a) (armMarginal nu a)).toReal
          - (h ^ 2 / 2) * armScoreCost nu a (if a = 0 then u.1 else u.2))
        =o[𝓝 (0 : ℝ)] fun h => h ^ 2)

/-- The EXPLICIT linear-tilt construction underlying `nu^(u,·)`: there are
moment-preserving measurable scores `s_a` (`∫ s_a = 0`, `∫ y s_a = 0`, realizing
the second-moment direction `∫ y² s_a = u_a`, bounded on `[0,1]`) and a radius `η > 0`
such that for `|h| ≤ η` each arm marginal of `p h` is the tilt
`dnu_a^h = (1 + h·s_a) dnu_a`.  This records the STATED linear-tilt construction
that `IsLocalPath` alone abstracts away (added per the redirect), and pins the
space of the local-alternative symbol `nu^(u,h)`.
@realizes nu^(u,h)(explicit tilt (1+h s_a) dnu_a) @realizes s_0, s_1(tilt scores) -/
def IsLinearTiltPath (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ) (p : ℝ → Measure (ℝ × ℝ)) : Prop :=
  ∃ (s : Fin 2 → ℝ → ℝ) (η : ℝ), 0 < η
    ∧ (∀ a : Fin 2,
        Measurable (s a)
        ∧ (∫ y, s a y ∂(armMarginal nu a) = 0)
        ∧ (∫ y, y * s a y ∂(armMarginal nu a) = 0)
        ∧ (∫ y, y ^ 2 * s a y ∂(armMarginal nu a) = (if a = 0 then u.1 else u.2))
        ∧ (∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |s a y| ≤ C))
    ∧ (∀ h : ℝ, |h| ≤ η → ∀ a : Fin 2,
        armMarginal (p h) a
          = (armMarginal nu a).withDensity (fun y => ENNReal.ofReal (1 + h * s a y)))

end CausalSmith.Stat.NeymanRegretMinimax
