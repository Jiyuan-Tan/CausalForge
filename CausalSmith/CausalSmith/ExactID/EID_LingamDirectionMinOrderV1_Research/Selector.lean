/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The global feasible-fiber decision formula, direction selector, separated
# model domain, and generic real information order

Statable population-level constructions.  The finite/evaluable *decision
procedure* content — the claim that `FeasFiber^b` and the selector `S_m` are
decidable by real quantifier elimination / sign-invariant cylindrical algebraic
decomposition — is the external interface `I-3` and is NOT encoded here: the
`def`s realize only the existential real Props and the two-branch relation.  The
atomic-witness ↔ real-source-realizability equivalence rests on the external
truncated Hamburger interface `I-4`.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic.Swaps
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory
open scoped BigOperators

/-- Coordinate index of the real structural parameter space (direct slope, the `m`
latent slopes, and the weight family `(j, r)`). -/
abbrev RealParamCoord (m : ℕ) : Type := Unit ⊕ Fin m ⊕ (Fin (m + 2) × ℕ)

/-- Evaluate the real parameter coordinates of `θ` at a coordinate index. -/
def realParamEval {m : ℕ} (θ : ParamSpace ℝ m) : RealParamCoord m → ℝ
  | Sum.inl _ => θ.1
  | Sum.inr (Sum.inl i) => θ.2.1 i
  | Sum.inr (Sum.inr jr) => θ.2.2 jr.1 jr.2

/-- A **proper real algebraic subset** of the parameter space: the (real) zero
locus of a nonzero real polynomial in the parameter coordinates.  Nonzeroness of
the polynomial makes it a proper subset (its complement is Zariski-dense), which
is the paper's genericity notion — deletion of a proper real algebraic subset. -/
def IsProperRealAlgebraicSubset {m : ℕ} (excl : Set (ParamSpace ℝ m)) : Prop :=
  ∃ P : MvPolynomial (RealParamCoord m) ℝ, P ≠ 0 ∧
    excl = { θ | MvPolynomial.eval (realParamEval θ) P = 0 }

/-- Causal direction value. -/
inductive Direction
  | forward
  | reverse
  deriving DecidableEq

/-- Raw moments `μ_r = B_r(0, k_2, …, k_r)` from a centered cumulant list `k`
(with `k 1 = 0` supplied by the caller), via the exponential/Bell set-partition
formula `μ_r = Σ_{π} ∏_{B∈π} k_{|B|}`. -/
def momentFromCumulants (k : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin r)), ∏ B ∈ π.parts, k B.card

/-- Finite atomic (Hankel-PSD / truncated Hamburger) certificate `Q_K(k)`: the
raw moments `μ_r(k)` (`1 ≤ r ≤ K`) are the moments of an `n`-atom probability law
with `μ_2 > 0`.  Its equivalence with real non-Gaussian finite-`K` source
realizability is the external interface `I-4`. -/
def atomicCertificate (n K : ℕ) (k : ℕ → ℝ) : Prop :=
  ∃ w z : Fin n → ℝ,
    (∑ h, w h = 1) ∧ (∀ h, 0 ≤ w h) ∧
    (∀ r, 1 ≤ r → r ≤ K → ∑ h, w h * (z h) ^ r = momentFromCumulants k r) ∧
    0 < momentFromCumulants k 2

/-- Global feasible-fiber **feasibility formula** `FeasFiber^b_m(t)` at order
`K = 2m + 2` (the existential-atomic-feasibility component of the bundled
`def:global-feasible-fiber-decision`, `feasibleFiberDecision` below).  Its truth
value is **exactly** the nonemptiness of
`R^b_{m,K}(t) ∩ F^b_{m,K}`: there exist `b`-loading and source-cumulant
coordinates `λ` that are real moment-feasible (`λ ∈ F^b_{m,K}`, which already
carries the nonzero direct slope, the pairwise-distinct finite slopes, the
finite-band cumulant coordinates, and the real non-Gaussian source realizability
whose finite atomic `Q_K` reformulation is interface `I-4`) with `Φ^b(λ) = t`.
By construction this def **is** the exact feasible-fiber equivalence; the atomic
`Q_K` reformulation is `atomicCertificate` below.

Deciding this formula — the real-QE / sign-invariant-CAD decision procedure with
the prescribed variable order `t, λ`, then witnesses, and the apolar rank-open
support-annihilator implementation — is the external interface `I-3`/`I-1` and is
NOT encoded here; only the existential feasibility Prop is realized.

Faithful to the paper's definition, the formula encodes the **atomic witnesses**
explicitly: there exist `b`-loading and source-cumulant coordinates `λ` with
`Φ^b(λ) = t`, nonzero direct slope, pairwise-distinct finite loading slopes, and,
for each source `j`, a finite atomic (Hankel-PSD) certificate `Q_K` on its cumulant
list — `atomicCertificate` — asserting `Σ_h w_{jh} = 1`, `w_{jh} ≥ 0`,
`Σ_h w_{jh} z_{jh}^r = μ_{jr}` for `1 ≤ r ≤ K` with `μ_{jr} = B_r(0, k_{j2}, …)`,
and `μ_{j2} > 0`.  Its equivalence with real non-Gaussian finite-`K` source
realizability (hence with `R^b_{m,K}(t) ∩ F^b_{m,K} ≠ ∅`) is the external truncated
Hamburger interface `I-4`.
@realizes S_m(feasibility of the arrow-`b` fiber over `t` = `R^b(t) ∩ F^b ≠ ∅`) -/
def feasibleFiberFormula (m : ℕ) (Φ : ParamSpace ℝ m → CumVec ℝ) (t : CumVec ℝ) : Prop :=
  ∃ lam : ParamSpace ℝ m,
    Φ lam = t ∧
    lam.1 ≠ 0 ∧
    Function.Injective (Fin.cons lam.1 lam.2.1 : Fin (m + 1) → ℝ) ∧
    ∀ j : Fin (m + 2),
      atomicCertificate (m + 2) (2 * m + 2)
        (fun r => if 2 ≤ r then lam.2.2 j r else 0)

/-- Signs used by a finite polynomial sign table. -/
inductive PolynomialSign
  | negative
  | zero
  | positive
  deriving DecidableEq

/-- Sign of a real number. -/
noncomputable def polynomialSign (x : ℝ) : PolynomialSign :=
  if x < 0 then .negative else if x = 0 then .zero else .positive

/-- A function on cumulant vectors is given by a finite semialgebraic sign table:
finitely many observable-coordinate polynomials are evaluated and their signs are
looked up in a finite table. -/
def IsFiniteSemialgebraicFunction {α : Type} (f : CumVec ℝ → α) : Prop :=
  ∃ tests : Finset (MvPolynomial (ℕ × ℕ) ℝ),
    ∃ table : (tests → PolynomialSign) → α,
      ∀ t, f t = table (fun P => polynomialSign
        (MvPolynomial.eval (fun ra => t ra.1 ra.2) P.1))

/-- The three variable blocks in the prescribed CAD order. -/
inductive FiberDecisionVariableBlock
  | observable
  | loadingAndCumulants
  | atomicWitnesses
  deriving DecidableEq

/-- The prescribed elimination order is `t`, then `λ`, then atomic witnesses. -/
def PrescribedFiberVariableOrder (before : FiberDecisionVariableBlock →
    FiberDecisionVariableBlock → Prop) : Prop :=
  before .observable .loadingAndCumulants ∧
  before .observable .atomicWitnesses ∧
  before .loadingAndCumulants .atomicWitnesses

/-- A stacked cumulant vector is **band-supported** when it vanishes off the retained
range `2 ≤ r ≤ 2m + 2`, `a ≤ r` — the only coordinates the order-`(2m+2)` truncation
records.  Every cumulant map `Φ^b_{m,2m+2}` lands here (it is defined to be `0` off the
band), so this is exactly the observable coordinate space the paper's decision procedure
ranges over.

Restricting the decision interfaces below to band-supported `t` is what makes them
SATISFIABLE, and it is faithful to the paper: a finite semialgebraic sign table reads
finitely many coordinates, so it can never certify the equation `Φ λ = t` at the
infinitely many out-of-band coordinates — an unrestricted `∀ t` iff would be vacuously
unsatisfiable and would silently collapse the decision Prop to `False`. -/
def BandSupported (m : ℕ) (t : CumVec ℝ) : Prop :=
  ∀ r a, ¬ (2 ≤ r ∧ r ≤ 2 * m + 2 ∧ a ≤ r) → t r a = 0

/-- A finite sign-table decision obtained by CAD using the paper's prescribed
`t`, then `λ`, then atomic-witness variable-block order, and deciding the stated
feasible-fiber formula on the band-supported observable coordinates.  Keeping the order
as an argument of the certificate ties it to this CAD decision rather than recording an
unrelated order witness. -/
def IsOrderedFeasibleFiberCADDecision (m : ℕ) (Φ : ParamSpace ℝ m → CumVec ℝ)
    (before : FiberDecisionVariableBlock → FiberDecisionVariableBlock → Prop)
    (decide : CumVec ℝ → Bool) : Prop :=
  PrescribedFiberVariableOrder before ∧
  IsFiniteSemialgebraicFunction decide ∧
  ∀ t, BandSupported m t → (decide t = true ↔ feasibleFiberFormula m Φ t)

/-- The fixed projective axis belonging to an arrow parameterization. -/
def fixedAxis : Direction → ℝ × ℝ
  | .forward => (0, 1)
  | .reverse => (1, 0)

/-- The direction-specific cumulant map used by the arrow certificate. -/
def directionCumulantMap (m : ℕ) : Direction → ParamSpace ℝ m → CumVec ℝ
  | .forward => forwardCumulantMap m (2 * m + 2)
  | .reverse => reverseCumulantMap m (2 * m + 2)

/-- A genuine polynomial rank-open locus: a nonempty principal open set cut out
by nonvanishing of a nonzero observable-coordinate minor. -/
def IsPolynomialRankOpen (rankOpen : Set (CumVec ℝ)) : Prop :=
  ∃ minor : MvPolynomial (ℕ × ℕ) ℝ,
    minor ≠ 0 ∧ rankOpen.Nonempty ∧
    rankOpen = { t | MvPolynomial.eval (fun ra => t ra.1 ra.2) minor ≠ 0 }

/-- The retained divided-power cumulant blocks of `t` admit the displayed
`m+2`-direction support with order-specific source weights. -/
def SupportExplainsCumulantBlocks (m : ℕ) (t : CumVec ℝ)
    (support : Fin (m + 2) → ℝ × ℝ) : Prop :=
  ∃ weights : Fin (m + 2) → ℕ → ℝ,
    ∀ r a, 2 ≤ r → r ≤ 2 * m + 2 → a ≤ r →
      t r a = ∑ j, weights j r * (support j).1 ^ (r - a) * (support j).2 ^ a

/-- Two nonzero affine representatives determine the same projective direction. -/
def ProjectivelyEquivalent (u v : ℝ × ℝ) : Prop :=
  u ≠ (0, 0) ∧ ∃ c : ℝ, c ≠ 0 ∧ v = (c * u.1, c * u.2)

/-- A support list has pairwise distinct projective directions. -/
def ProjectivelyDistinct {n : ℕ} (support : Fin n → ℝ × ℝ) : Prop :=
  ∀ i j, ProjectivelyEquivalent (support i) (support j) → i = j

/-- Equality of unordered supports in projective space, allowing an independent
nonzero rescaling of every displayed affine representative. -/
def SameProjectiveSupport {n : ℕ}
    (support support' : Fin n → ℝ × ℝ) : Prop :=
  ∀ z : ℝ × ℝ,
    (∃ i, ProjectivelyEquivalent z (support i)) ↔
      (∃ i, ProjectivelyEquivalent z (support' i))

/-- On the rank-open locus the support is recovered from the simultaneous
divided-power blocks: every other projectively distinct `m+2`-direction
decomposition has the same unordered projective support. -/
def IsRecoveredSupport (m : ℕ) (t : CumVec ℝ)
    (support : Fin (m + 2) → ℝ × ℝ) : Prop :=
  ProjectivelyDistinct support ∧ SupportExplainsCumulantBlocks m t support ∧
  ∀ support' : Fin (m + 2) → ℝ × ℝ,
    ProjectivelyDistinct support' → SupportExplainsCumulantBlocks m t support' →
      SameProjectiveSupport support' support

/-! #### The apolar route: divided-power blocks and their contractions

The note defines the arrow decision on the rank-open locus by *"factoring the recovered degree-`n`
support annihilator `Q_D` **from the contractions of the divided-power forms `f_{n+k}`**"*
(`def:global-feasible-fiber-decision`; `writeup.tex` §thm:generic-apolar-arrow-recovery).  `Q_D` is
therefore not just *some* squarefree product over a recovered support — it is *the generator of the
common contraction kernel*.  These three primitives let the certificate say exactly that, so the
definition carries the note's own characterization of `Q_D` rather than a downstream consequence of
it.  (They mirror `dividedPowerBlock` / `diffApply` / `supportAnnihilator` of
`Helpers/ApolarDefs.lean`, which are stated over `ℂ`; the certificate lives over `ℝ`.) -/

/-- Real divided-power binary form of the order-`r` cumulant block:
`f_r(x, y) = Σ_{a=0}^r C(r,a) t_{r,a} x^{r-a} y^a` (with `x = X 0`, `y = X 1`). -/
noncomputable def realDividedPowerBlock (t : CumVec ℝ) (r : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ a ∈ Finset.range (r + 1),
    MvPolynomial.C ((Nat.choose r a : ℝ) * t r a)
      * MvPolynomial.X 0 ^ (r - a) * MvPolynomial.X 1 ^ a

/-- The apolar **contraction** `q(∂) f` of a binary form `f` by the constant-coefficient
differential operator with symbol `q`. -/
noncomputable def realDiffApply (q f : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ d ∈ q.support,
    MvPolynomial.coeff d q •
      ((fun g => (MvPolynomial.pderiv (0 : Fin 2)) g)^[d 0]
        ((fun g => (MvPolynomial.pderiv (1 : Fin 2)) g)^[d 1] f))

/-- The squarefree degree-`n` support annihilator `Q_D = ∏_{ℓ ∈ D} ℓ^⊥` as a real binary form, in
the same sign convention as the evaluation-form product used by the certificate below. -/
noncomputable def realSupportAnnihilatorPoly {m : ℕ} (support : Fin (m + 2) → ℝ × ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  ∏ j : Fin (m + 2),
    (MvPolynomial.C (support j).1 * MvPolynomial.X 1 -
      MvPolynomial.C (support j).2 * MvPolynomial.X 0)

/-- The recovered squarefree support-annihilator certificate on the apolar
rank-open locus.  `Q_D` is characterized exactly as the note characterizes it — as the generator of
the **common kernel of the contractions** `q ↦ (q(∂) f_{n+k})_{0 ≤ k ≤ n-2}` of the divided-power
blocks, `n = m + 2` — and it is then factored into the `m+2` support directions, from which the
decision is read off membership of the arrow's fixed axis.

The `annihilator`/`kernel` conjuncts are what make this *the apolar* certificate: without them the
predicate would record only that *some* unique block-explaining support exists and that its product
form is the annihilator, which is a consequence of the note's contraction-kernel identity rather
than the identity itself. -/
def ApolarFiberDecisionCertificate (m : ℕ) (b : Direction)
    (Φ : ParamSpace ℝ m → CumVec ℝ) (decide : CumVec ℝ → Bool) : Prop :=
  Φ = directionCumulantMap m b ∧
  ∃ rankOpen : Set (CumVec ℝ),
    ∃ support : CumVec ℝ → Fin (m + 2) → ℝ × ℝ,
    ∃ annihilator : CumVec ℝ → ℝ × ℝ → ℝ,
      IsPolynomialRankOpen rankOpen ∧
      (∀ t ∈ rankOpen, IsRecoveredSupport m t (support t)) ∧
      (∀ t ∈ rankOpen, ∀ z,
        annihilator t z = ∏ j, ((support t j).1 * z.2 - (support t j).2 * z.1)) ∧
      -- `Q_D` is the evaluation of the degree-`n` binary form `realSupportAnnihilatorPoly`,
      (∀ t ∈ rankOpen, ∀ z : ℝ × ℝ,
        annihilator t z =
          MvPolynomial.eval ![z.1, z.2] (realSupportAnnihilatorPoly (support t))) ∧
      -- and that form SPANS the common kernel of the contractions of the divided-power blocks
      -- `f_{n+k}`, `0 ≤ k ≤ n-2` — the note's defining characterization of `Q_D`.
      (∀ t ∈ rankOpen, ∀ q : MvPolynomial (Fin 2) ℝ, q.IsHomogeneous (m + 2) →
        ((∀ k ≤ m, realDiffApply q (realDividedPowerBlock t (m + 2 + k)) = 0) ↔
          ∃ c : ℝ, q = c • realSupportAnnihilatorPoly (support t))) ∧
      (∀ t ∈ rankOpen, BandSupported m t →
        (decide t = true ↔
          feasibleFiberFormula m Φ t ∧
            ∃ j, ProjectivelyEquivalent (fixedAxis b) (support t j)))

/-- Operational structure required by the paper: a finite semialgebraic
real-QE/CAD decision, with the prescribed variable-block order, and its apolar
support-annihilator implementation on the rank-open locus. -/
def feasibleFiberDecisionInterfaces (m : ℕ) (b : Direction)
    (Φ : ParamSpace ℝ m → CumVec ℝ) : Prop :=
  ∃ cadDecide : CumVec ℝ → Bool,
    (∃ before, IsOrderedFeasibleFiberCADDecision m Φ before cadDecide) ∧
    ApolarFiberDecisionCertificate m b Φ cadDecide

/-- **Global feasible-fiber decision** `FeasFiber^b_m` — the full object the paper's
`def:global-feasible-fiber-decision` defines, bundled as a **pair** so the extracted
definition carries *both* the existential atomic feasibility formula **and** the paper's
operational decision structure (not only the existential Prop, which alone under-records
the paper):

* `.1` = the per-`t` **existential atomic feasibility formula**
  `feasibleFiberFormula m (Φ^b)` — the statable population predicate whose truth value at
  `t` is exactly `R^b_{m,K}(t) ∩ F^b_{m,K} ≠ ∅`;
* `.2` = the paper-defined **operational decision structure**
  `feasibleFiberDecisionInterfaces m b (Φ^b)` — the real-QE / sign-invariant-CAD decision
  with the prescribed variable order (`t, λ`, then the atomic witnesses) (`I-3`) and the
  apolar rank-open support-annihilator direct implementation (`I-1`).  These are the two
  operational clauses the note states (anchored, external, routed to `SUBSTRATE_DEBT`; not
  encoded as executable in-run).

The arrow map is **pinned by the arrow tag**: as in the note, `Φ^b` is *determined* by `b`
(`Φ^right = forwardCumulantMap`, `Φ^left = reverseCumulantMap`, i.e.
`directionCumulantMap m b`).  It is deliberately NOT an independent parameter: exposing a
free `Φ` would let the decision be read off an arrow map unrelated to the arrow tag `b`
whose fixed axis the apolar certificate consults.

The two components are held SEPARATELY, exactly as `directionSelectorWithDecision` holds
the selector map and its decision interfaces.  Conjoining the `t`-independent operational
structure *into* the per-`t` Prop (an earlier rendering) was unsound: it made
`FeasFiber^b_m(t)` entail the global existence of a finite semialgebraic decision, which
is unsatisfiable against an unrestricted `∀ t` iff, collapsing the predicate to `False`
instead of "true exactly when `R^b_{m,K}(t) ∩ F^b_{m,K} ≠ ∅`".
@realizes S_m(feasibility of the arrow-`b` fiber over `t` + its QE/CAD & apolar decision) -/
-- @node: def:global-feasible-fiber-decision
def feasibleFiberDecision (m : ℕ) (b : Direction) : (CumVec ℝ → Prop) × Prop :=
  (fun t => feasibleFiberFormula m (directionCumulantMap m b) t,
   feasibleFiberDecisionInterfaces m b (directionCumulantMap m b))

open Classical in
/-- Separate-fiber direction selector `S_m(t)` (the two-branch relational component of
the bundled `def:direction-selector`, `directionSelectorWithDecision` below): `forward`
when the forward
feasible-fiber formula holds and the reverse fails, `reverse` in the mirror case,
and undefined (`none`) otherwise.  The `Option`-valued map encodes only the
two-branch relation; any claim that `S_m` is an *evaluable finite semialgebraic
decision procedure* rests on the external interface `I-3` and is not encoded (the
definition is `noncomputable`, decided classically).
@realizes S_m(two-branch partial direction map) -/
noncomputable def directionSelector (m : ℕ) (t : CumVec ℝ) : Option Direction :=
  if feasibleFiberFormula m (forwardCumulantMap m (2 * m + 2)) t
      ∧ ¬ feasibleFiberFormula m (reverseCumulantMap m (2 * m + 2)) t then
    some Direction.forward
  else if feasibleFiberFormula m (reverseCumulantMap m (2 * m + 2)) t
      ∧ ¬ feasibleFiberFormula m (forwardCumulantMap m (2 * m + 2)) t then
    some Direction.reverse
  else
    none

/-- The separated observable domain on which exactly one feasible arrow remains. -/
def separatedSelectorDomain (m : ℕ) : Set (CumVec ℝ) :=
  { t | (feasibleFiberFormula m (forwardCumulantMap m (2 * m + 2)) t ∧
          ¬ feasibleFiberFormula m (reverseCumulantMap m (2 * m + 2)) t) ∨
        (feasibleFiberFormula m (reverseCumulantMap m (2 * m + 2)) t ∧
          ¬ feasibleFiberFormula m (forwardCumulantMap m (2 * m + 2)) t) }

/-- Operational selector structure: one finite semialgebraic procedure on the
declared separated domain, together with the two arrow-specific apolar
support-annihilator factorizations implementing its generic branches. -/
def directionSelectorDecisionInterfaces (m : ℕ) : Prop :=
  ∃ selDecide : CumVec ℝ → Option Direction,
    IsFiniteSemialgebraicFunction selDecide ∧
    (∀ t ∈ separatedSelectorDomain m, selDecide t = directionSelector m t) ∧
    (∃ forwardDecide reverseDecide : CumVec ℝ → Bool,
      ApolarFiberDecisionCertificate m .forward
        (forwardCumulantMap m (2 * m + 2)) forwardDecide ∧
      ApolarFiberDecisionCertificate m .reverse
        (reverseCumulantMap m (2 * m + 2)) reverseDecide ∧
      ∀ t ∈ separatedSelectorDomain m,
        selDecide t = if forwardDecide t then some .forward
          else if reverseDecide t then some .reverse else none)

/-- **Separate-fiber direction selector** `S_m` — the full object the paper's
`def:direction-selector` defines, bundled so the extracted definition carries *both*
the two-branch selection map **and** the paper's operational decision structure (not
only the weaker noncomputable classical two-branch relation):

* `.1` = the two-branch selection map `directionSelector m` (`forward` / `reverse` /
  `none`), the population selector relation;
* `.2` = the paper-defined **operational decision structure**
  `directionSelectorDecisionInterfaces m` — the globally finite semialgebraic decision
  procedure computing `S_m` (`I-3`) and its apolar support-annihilator direct generic
  implementation (`I-1`).  These are the operational clauses the note states as part of
  `S_m` and are here genuine **components** of the definition (anchored, external, routed
  to `SUBSTRATE_DEBT`; not encoded as executable in-run).
@realizes S_m(two-branch partial direction map + its finite semialgebraic / apolar decision) -/
-- @node: def:direction-selector
noncomputable def directionSelectorWithDecision (m : ℕ) :
    (CumVec ℝ → Option Direction) × Prop :=
  (directionSelector m, directionSelectorDecisionInterfaces m)

/-- **Structural-model witness** `M`: a bivariate LvLiNGAM structural model
carrying its observational law `P_M = law`, its directed edge `D(M) = edge`, and a
direction-specific real moment-feasible parameter list `param ∈ F^b_{m,K}` (with
`b = edge`) that realizes the truncated cumulant observation `T_K(P_M)` through
order `K`, together with the corresponding LvLiNGAM class membership.  This carries
the model / representation identity (`P_M` and its feasible parameters) that a bare
observational measure would lose.
@realizes M,P_M,D(M),M^{sep}_{m,K}(model `M`: law `P_M`, edge `D(M)`, feasible param) -/
structure StructuralModel (m K : ℕ) where
  /-- The observational law `P_M ∈ Laws(ℝ²)`. -/
  law : Measure (ℝ × ℝ)
  /-- The directed edge `D(M)`. -/
  edge : Direction
  /-- The model's own direction-specific real moment-feasible representation parameter. -/
  param : ParamSpace ℝ m
  /-- Real feasibility of `param` (nonzero edge, distinct slopes, source realizability). -/
  feasible : param ∈ realFeasibleRegion m K
  /-- `M` is a forward (resp. reverse) LvLiNGAM model represented by its own
  feasible parameter: the parameter's slopes and source-cumulant weights are
  exactly those of the sources generating `P_M`, and its simultaneous binary-form
  image is the truncated cumulant of `P_M`. -/
  realizes :
    (edge = Direction.forward →
        ForwardLvLiNGAMRep law m K param ∧
        forwardCumulantMap m K param = truncatedCumulant law Prod.fst Prod.snd K) ∧
    (edge = Direction.reverse →
        ReverseLvLiNGAMRep law m K param ∧
        reverseCumulantMap m K param = truncatedCumulant law Prod.fst Prod.snd K)

/-- Separated nonzero-edge structural-model domain `M^{sep}_{m,K}`, a `K`-explicit
set of **structural models** `M : StructuralModel m K` (each carrying its law
`P_M`, edge `D(M)`, and direction-specific feasible parameters).  Membership imposes
**opposite-arrow fiber emptiness at `T_K(P_M)`**: a forward model whose reverse
feasible fiber over `T_K(P_M)` is empty, or a reverse model whose forward feasible
fiber over `T_K(P_M)` is empty.  The domain retains the model / representation
identity and the explicit truncation order `K`.
@realizes M,P_M,D(M),M^{sep}_{m,K}(models `M` with empty opposite fiber at `T_K(P_M)`) -/
-- @node: def:separated-model-domain
def separatedModelDomain (m K : ℕ) : Set (StructuralModel m K) :=
  { M |
      (M.edge = Direction.forward ∧
        ¬ ∃ η ∈ realFeasibleRegion m K,
            reverseCumulantMap m K η = truncatedCumulant M.law Prod.fst Prod.snd K)
    ∨ (M.edge = Direction.reverse ∧
        ¬ ∃ θ ∈ realFeasibleRegion m K,
            forwardCumulantMap m K θ = truncatedCumulant M.law Prod.fst Prod.snd K) }

/-- Generic arrow separation at order `L`: off a **proper real algebraic subset**
of each real feasible region, no arrow value admits an opposite-region
representation.  The excluded set is constrained to be a proper real algebraic
subset (the zero locus of a nonzero real polynomial), matching the paper's
genericity notion; an arbitrary excluded set is not permitted.  Helper for
`def:information-order`. -/
def separatesAtOrder (m L : ℕ) : Prop :=
  (∃ excl : Set (ParamSpace ℝ m),
      IsProperRealAlgebraicSubset excl ∧
      (∃ θ ∈ realFeasibleRegion m L, θ ∉ excl) ∧
      ∀ θ ∈ realFeasibleRegion m L, θ ∉ excl →
        ¬ ∃ η ∈ realFeasibleRegion m L, forwardCumulantMap m L θ = reverseCumulantMap m L η)
  ∧ (∃ excl : Set (ParamSpace ℝ m),
      IsProperRealAlgebraicSubset excl ∧
      (∃ η ∈ realFeasibleRegion m L, η ∉ excl) ∧
      ∀ η ∈ realFeasibleRegion m L, η ∉ excl →
        ¬ ∃ θ ∈ realFeasibleRegion m L, reverseCumulantMap m L η = forwardCumulantMap m L θ)

/-- Generic real information order `K^star(m)`: the least `L ≥ 2` at which the
arrow is generically separated over both real feasible regions, and `⊤ = ∞` if no
such `L` exists.
@realizes K^star(m)(least separating truncation order) -/
-- @node: def:information-order
noncomputable def informationOrder (m : ℕ) : ℕ∞ :=
  sInf { L : ℕ∞ | ∃ L₀ : ℕ, L = (L₀ : ℕ∞) ∧ 2 ≤ L₀ ∧ separatesAtOrder m L₀ }

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
