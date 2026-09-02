/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Tactic.Attr
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.FunProp

/-!
# The `condexp_linearity` tactic

**What it does, in one sentence: it proves an almost-everywhere identity that says
"conditional expectation is linear", by taking the sum/difference/negation/scalar structure
of the goal's right-hand side apart and pushing the conditional expectation inside step by
step, proving the integrability side conditions on the way.**

Conditional-expectation linearity in Mathlib is `=ᵐ[μ]`-valued (`condExp_add`, `condExp_sub`,
…), so `simp` cannot traverse it: an a.e. equality is not a rewrite rule, and each step has to
be glued to the next with `Filter.EventuallyEq.trans`. That gluing, plus the `Integrable`
arguments the Mathlib lemmas demand, is what the library currently writes out by hand — a
`have` per `+`/`-` in the integrand, each restating two large conditional expectations, each
preceded by its own `Integrable` bookkeeping. This tactic builds that chain.

## How to use it

The goal (typically a `have`-target) must be an a.e. equality whose *conditioned* side is a
conditional expectation and whose *other* side already spells out the answer:

```
have h : μ[fun ω => a ω + b ω - c ω | m] =ᵐ[μ] μ[a | m] + μ[b | m] - μ[c | m] := by
  condexp_linearity
```

The right-hand side is the specification: the tactic follows *its* shape, so a product or a
constant multiple that the right-hand side keeps together is kept together, and a sum it
splits is split. Either side may be the conditional expectation (the symmetric goal is proved
by `.symm`). Project wrappers (`POVar.condExpGiven`, `POCFBundle.condExpGiven`, …) are
unwrapped first with `condexp_simps`, so wrapper-level goals are in scope.

Integrability side conditions are discharged by `first | assumption | fun_prop`, i.e. by the
Phase-1 side-condition layer; nothing needs to be named at the call site. When a witness
lives in an assumption bundle rather than in the local context — so that neither `assumption`
nor a `fun_prop` tag can reach it — hand it over in brackets, `filter_upwards`-style:
`condexp_linearity [As.integrable_Y d, As.integrable_Y z]`.

## What it does NOT do, and how it fails

It is a *linearity* tactic only. It never touches `condExp_mul_of_stronglyMeasurable_*`
("pull out what is known"), which carries a measurability side condition and real analytic
content, nor `condExp_congr_ae`, which is mathematics. Known limits:

* the finite-sum lemma is not driven by the tactic — use `condExp_finsetSum'` (or its wrapper
  analogues) directly;
* a scalar multiple is recognised only when the right-hand side writes it with `•`; a
  right-hand side spelled `fun ω => c * g ω` is treated as an opaque leaf;
* the right-hand side must be concrete — a metavariable gives it nothing to follow;
* it does not look inside a `calc`/`simpa`/`rwa` chain: it proves one whole a.e. equality.

**Failure is total and loud.** The proof term is assembled off to the side and assigned only
when it is complete, so a failed call leaves the goal exactly as it was — never a partial
rewrite. The error names the subterm that blocked: either the integrand that does not have
the shape the right-hand side asked for, or the leaf whose conditional expectation is not the
one the right-hand side states.

There is deliberately no `condexp_linearity?` variant: the tactic performs no lemma search —
the right-hand side determines the chain uniquely — so there is no choice to report.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
open MeasureTheory Filter

namespace Causalean.Tactic.CondexpLinearity

/-! ### Rewriting steps

Restatements of the Mathlib linearity lemmas with every piece of data explicit, so that the
tactic can build each step with `mkAppM` without depending on the order of Mathlib's implicit
binders. -/

section Lemmas

variable {α E : Type*} {m₀ : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Additivity step: the conditional expectation of a sum of [two integrable functions](hyp:hf,hg)
[splits into the sum of their conditional expectations](goal).
Data-explicit restatement of `MeasureTheory.condExp_add`. The measure is bound before the
conditioning σ-algebra so that its own σ-algebra is the ambient `m₀`, not `m`. -/
theorem condExp_add_aux (μ : Measure α) (m : MeasurableSpace α) (f g : α → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m] :=
  condExp_add hf hg m

/-- Difference step: the conditional expectation of a difference of integrable functions
splits. Data-explicit restatement of `MeasureTheory.condExp_sub`. -/
theorem condExp_sub_aux (μ : Measure α) (m : MeasurableSpace α) (f g : α → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m] :=
  condExp_sub hf hg m

/-- Negation step. Data-explicit restatement of `MeasureTheory.condExp_neg`. -/
theorem condExp_neg_aux (μ : Measure α) (m : MeasurableSpace α) (f : α → E) :
    μ[-f | m] =ᵐ[μ] -μ[f | m] :=
  condExp_neg f m

/-- Scalar step. Data-explicit restatement of `MeasureTheory.condExp_smul` at real
scalars. -/
theorem condExp_smul_aux (μ : Measure α) (m : MeasurableSpace α) (c : ℝ) (f : α → E) :
    μ[c • f | m] =ᵐ[μ] c • μ[f | m] :=
  condExp_smul c f m

omit [CompleteSpace E] in
/-- Constant leaf: on a finite measure a constant is its own conditional expectation.
Data-explicit, `=ᵐ[μ]`-valued restatement of `MeasureTheory.condExp_const`. -/
theorem condExp_const_aux (μ : Measure α) (m : MeasurableSpace α) [IsFiniteMeasure μ]
    (hm : m ≤ m₀) (c : E) :
    μ[fun _ => c | m] =ᵐ[μ] fun _ => c :=
  EventuallyEq.of_eq (condExp_const hm c)

end Lemmas

/-! ### The elaborator -/

/-- The ambient data of the conditional expectation being normalized: enough to rebuild
`μ[· | m]` and the a.e.-equality relation at new arguments. -/
private structure Ctx where
  /-- `μ[· | m]` as a partially applied `MeasureTheory.condExp`, awaiting the integrand. -/
  condExpFn : Expr
  /-- The a.e.-equality relation, awaiting its two sides. -/
  eqFn : Expr
  /-- The filter the equality is taken along (`MeasureTheory.ae μ`). -/
  l : Expr
  /-- The conditioning σ-algebra. -/
  m : Expr
  /-- The ambient σ-algebra the measure lives on. -/
  m₀ : Expr
  /-- The measure. -/
  μ : Expr

private def Ctx.condExpOf (ctx : Ctx) (f : Expr) : Expr := mkApp ctx.condExpFn f

private def Ctx.eqOf (ctx : Ctx) (a b : Expr) : Expr := mkApp2 ctx.eqFn a b

/-- Eta-expand a function-valued term to a one-binder lambda, so that pointwise-written and
function-level-written expressions can be matched by the same code. -/
private def etaExpand1 (e : Expr) : MetaM Expr := do
  if e.isLambda then return e
  match ← whnf (← inferType e) with
  | .forallE n d _ bi => withLocalDecl n bi d fun x => do mkLambdaFVars #[x] (mkApp e x)
  | _ => return e

/-- The two operands of a head application of the binary operation `op`, if `e` is one. -/
private def headBin (e₀ : Expr) (op : Name) : Option (Expr × Expr) :=
  let e := e₀.consumeMData
  let args := e.getAppArgs
  if e.isAppOf op && args.size == 6 then some (args[4]!, args[5]!) else none

/-- The operand of a head application of `Neg.neg`, if `e` is one. -/
private def headNeg (e₀ : Expr) : Option Expr :=
  let e := e₀.consumeMData
  let args := e.getAppArgs
  if e.isAppOf ``Neg.neg && args.size == 3 then some args[2]! else none

/-- Run `k` on `e`, and if it does not match, once more on `e`'s weak-head normal form. A
`set`-introduced abbreviation for the integrand is thereby seen through. -/
private def withDelta {β : Type} (e₀ : Expr) (k : Expr → MetaM (Option β)) :
    MetaM (Option β) := do
  let e := (← instantiateMVars e₀).consumeMData
  if let some r ← k e then return some r
  let e' := (← whnf e).consumeMData
  if e' == e then return none else k e'

/-- Split `e` as `f₁ op f₂` for `op` one of `HAdd.hAdd`/`HSub.hSub`, whether it is written at
the function level (`f₁ + f₂`) or pointwise (`fun x => f₁ x + f₂ x`). -/
private def splitBin (e : Expr) (op : Name) : MetaM (Option (Expr × Expr)) :=
  withDelta e fun e => do
    if let some r := headBin e op then return some r
    let e' ← etaExpand1 e
    unless e'.isLambda do return none
    lambdaBoundedTelescope e' 1 fun xs body => do
      match headBin body op with
      | some (a, b) => return some ((← mkLambdaFVars xs a).eta, (← mkLambdaFVars xs b).eta)
      | none => return none

/-- Split `e` as `-f`, written either at the function level or pointwise. -/
private def splitNeg (e : Expr) : MetaM (Option Expr) :=
  withDelta e fun e => do
    if let some r := headNeg e then return some r
    let e' ← etaExpand1 e
    unless e'.isLambda do return none
    lambdaBoundedTelescope e' 1 fun xs body => do
      match headNeg body with
      | some a => return some (← mkLambdaFVars xs a).eta
      | none => return none

/-- Split `e` as `c • f` with the scalar `c` independent of the point, written either at the
function level or pointwise. -/
private def splitSMul (e : Expr) : MetaM (Option (Expr × Expr)) :=
  withDelta e fun e => do
    if let some r := headBin e ``HSMul.hSMul then return some r
    let e' ← etaExpand1 e
    unless e'.isLambda do return none
    lambdaBoundedTelescope e' 1 fun xs body => do
      match headBin body ``HSMul.hSMul with
      | some (c, a) =>
        if c.containsFVar xs[0]!.fvarId! then return none
        return some (c, (← mkLambdaFVars xs a).eta)
      | none => return none

/-- The constant value of `e`, if `e` is a function that ignores its argument. -/
private def constValue (e : Expr) : MetaM (Option Expr) := do
  let e' ← etaExpand1 (← instantiateMVars e).consumeMData
  unless e'.isLambda do return none
  lambdaBoundedTelescope e' 1 fun xs body => do
    if body.containsFVar xs[0]!.fvarId! then return none else return some body

/-- Try to prove `goalType` with `tac`, returning the proof term on success and restoring the
tactic state on failure. Used for the tactic's side conditions, which must never leak into
the user's goal list. -/
private def trySide (goalType : Expr) (tac : TSyntax `tactic) : TacticM (Option Expr) := do
  let mv ← mkFreshExprMVar goalType
  let s ← saveState
  try
    let remaining ← Lean.Elab.Tactic.run mv.mvarId! (evalTactic tac)
    if remaining.isEmpty then
      let pf ← instantiateMVars mv
      if pf.hasExprMVar then s.restore; return none else return some pf
    else
      s.restore; return none
  catch _ => s.restore; return none

/-- Prove `Integrable f μ`, or fail with a message naming `f`. -/
private def dischargeIntegrable (ctx : Ctx) (f : Expr) : TacticM Expr := do
  let ty ← mkAppM ``MeasureTheory.Integrable #[f, ctx.μ]
  match ← trySide ty (← `(tactic| first | assumption | fun_prop)) with
  | some pf => return pf
  | none =>
    throwError "condexp_linearity: blocked at{indentExpr f}\n\
      splitting the conditional expectation here needs{indentExpr ty}\n\
      which neither `assumption` nor `fun_prop` could prove. Supply it as a hypothesis, or \
      keep this step as a named `condExp_add`/`condExp_sub` call."

/-- Build the linearity chain proving `μ[f | m] =ᵐ[μ] rhs`, following the shape of `rhs`.

Each constructor of `rhs` (`+`, `-`, `-·`, `•`) consumes the matching constructor of the
integrand `f` through the corresponding Mathlib lemma and recurses; a leaf is discharged by
reflexivity or, for a constant integrand, by `condExp_const`. Throws — never returns a
partial result — when `f` does not have the shape `rhs` asks for. -/
private partial def build (ctx : Ctx) (f rhs : Expr) : TacticM Expr := do
  let rhs := (← instantiateMVars rhs).consumeMData
  let expected := ctx.eqOf (ctx.condExpOf f) rhs
  -- difference
  if let some (a, b) ← splitBin rhs ``HSub.hSub then
    let some (f₁, f₂) ← splitBin f ``HSub.hSub
      | throwError "condexp_linearity: blocked at{indentExpr f}\n\
          the goal's other side is a difference, but this integrand is not."
    let hf ← dischargeIntegrable ctx f₁
    let hg ← dischargeIntegrable ctx f₂
    let step ← mkAppM ``condExp_sub_aux #[ctx.μ, ctx.m, f₁, f₂, hf, hg]
    let rest ← mkAppM ``Filter.EventuallyEq.sub #[← build ctx f₁ a, ← build ctx f₂ b]
    return ← hint (← mkAppM ``Filter.EventuallyEq.trans #[step, rest]) expected
  -- sum
  if let some (a, b) ← splitBin rhs ``HAdd.hAdd then
    let some (f₁, f₂) ← splitBin f ``HAdd.hAdd
      | throwError "condexp_linearity: blocked at{indentExpr f}\n\
          the goal's other side is a sum, but this integrand is not."
    let hf ← dischargeIntegrable ctx f₁
    let hg ← dischargeIntegrable ctx f₂
    let step ← mkAppM ``condExp_add_aux #[ctx.μ, ctx.m, f₁, f₂, hf, hg]
    let rest ← mkAppM ``Filter.EventuallyEq.add #[← build ctx f₁ a, ← build ctx f₂ b]
    return ← hint (← mkAppM ``Filter.EventuallyEq.trans #[step, rest]) expected
  -- negation
  if let some a ← splitNeg rhs then
    let some f₁ ← splitNeg f
      | throwError "condexp_linearity: blocked at{indentExpr f}\n\
          the goal's other side is a negation, but this integrand is not."
    let step ← mkAppM ``condExp_neg_aux #[ctx.μ, ctx.m, f₁]
    let rest ← mkAppM ``Filter.EventuallyEq.neg #[← build ctx f₁ a]
    return ← hint (← mkAppM ``Filter.EventuallyEq.trans #[step, rest]) expected
  -- scalar multiple
  if let some (c, a) ← splitSMul rhs then
    let some (c', f₁) ← splitSMul f
      | throwError "condexp_linearity: blocked at{indentExpr f}\n\
          the goal's other side is a scalar multiple, but this integrand is not."
    unless ← isDefEq c c' do
      throwError "condexp_linearity: blocked at{indentExpr f}\n\
        the scalar here is{indentExpr c'}\nbut the goal's other side scales by{indentExpr c}"
    let step ← mkAppM ``condExp_smul_aux #[ctx.μ, ctx.m, c', f₁]
    let rest ← mkAppM ``Filter.EventuallyEq.const_smul #[← build ctx f₁ a, c']
    return ← hint (← mkAppM ``Filter.EventuallyEq.trans #[step, rest]) expected
  -- leaf: the two sides must already agree
  if ← isDefEq (ctx.condExpOf f) rhs then
    return ← hint (← mkAppM ``Filter.EventuallyEq.refl #[ctx.l, ctx.condExpOf f]) expected
  -- leaf: a constant integrand
  if let some c ← constValue f then
    let leType ← mkAppM ``LE.le #[ctx.m, ctx.m₀]
    let leTac ← `(tactic|
      first | assumption | exact le_rfl | exact Measurable.comap_le (by fun_prop))
    if let some hm ← trySide leType leTac then
      if let some step ← observing? (mkAppM ``condExp_const_aux #[ctx.μ, ctx.m, hm, c]) then
        if ← isDefEq (← inferType step) expected then
          return ← hint step expected
  throwError "condexp_linearity: blocked at{indentExpr f}\n\
    its conditional expectation{indentExpr (ctx.condExpOf f)}\n\
    is not the term the goal's other side states here:{indentExpr rhs}\n\
    This tactic only rearranges `+`, `-`, unary `-` and `•`; anything else must match on the \
    nose (up to definitional equality)."
where
  /-- Re-type a completed step at the shape the caller asked for, so that the chain's
  intermediate types stay the ones the user wrote. -/
  hint (e ty : Expr) : TacticM Expr := do
    if ← isDefEq (← inferType e) ty then mkExpectedTypeHint e ty else return e

/-- Decompose an application of `MeasureTheory.condExp` into its ambient data and the
integrand. -/
private def asCondExp (eqFn l e₀ : Expr) : Option (Ctx × Expr) := do
  let e := e₀.consumeMData
  let args := e.getAppArgs
  guard (e.isAppOf ``MeasureTheory.condExp && args.size == 8)
  let ctx : Ctx :=
    { condExpFn := e.appFn!, eqFn := eqFn, l := l, m := args[2]!, m₀ := args[3]!,
      μ := args[6]! }
  some (ctx, args[7]!)

/--
Prove an a.e. linearity identity for conditional expectation, following the shape of the
goal's non-conditioned side.

```
have h : μ[fun ω => a ω + b ω - c ω | m] =ᵐ[μ] μ[a | m] + μ[b | m] - μ[c | m] := by
  condexp_linearity
```

`+`, `-`, unary `-` and `•` are pushed through `condExp` by chaining Mathlib's
`condExp_add`/`condExp_sub`/`condExp_neg`/`condExp_smul` with `Filter.EventuallyEq.trans`;
integrability side conditions are discharged by `first | assumption | fun_prop`; a constant
integrand is closed by `condExp_const`. Project conditioning wrappers are unwrapped first
with the `condexp_simps` set.

An integrability fact that lives in a bundle rather than in the local context can be handed
over in brackets, `filter_upwards`-style — the terms are added to the context before the
chain is built, where `assumption` finds them:

```
condexp_linearity [As.integrable_Y d, As.integrable_Y z]
```

Not in scope: pull-out (`condExp_mul_of_stronglyMeasurable_*`), a.e. congruence
(`condExp_congr_ae`), and finite sums (use `condExp_finsetSum'`). Failure is total: the goal
is left untouched and the error names the blocking subterm. See the file's module docstring
for the full list of limits.
-/
syntax (name := condexpLinearity) "condexp_linearity"
  (" [" withoutPosition(term,*) "]")? : tactic

elab_rules : tactic
  | `(tactic| condexp_linearity $[[$facts?,*]]?) => withMainContext do
    if let some facts := facts? then
      for t in facts.getElems do
        evalTactic (← `(tactic| have := $t))
    evalTactic (← `(tactic| try simp only [condexp_simps]))
    let goal ← getMainGoal
    goal.withContext do
      let ty := (← instantiateMVars (← goal.getType)).consumeMData
      let args := ty.getAppArgs
      unless ty.isAppOf ``Filter.EventuallyEq && args.size == 5 do
        throwError "condexp_linearity: the goal is not an almost-everywhere equality \
          `f =ᵐ[μ] g`:{indentExpr ty}"
      let eqFn := mkAppN ty.getAppFn args[:3]
      let lhs := args[3]!
      let rhs := args[4]!
      let pf ←
        if let some (ctx, f) := asCondExp eqFn args[2]! lhs then
          build ctx f rhs
        else if let some (ctx, f) := asCondExp eqFn args[2]! rhs then
          mkAppM ``Filter.EventuallyEq.symm #[← build ctx f lhs]
        else
          throwError "condexp_linearity: neither side of the goal is a conditional \
            expectation (after unwrapping with `condexp_simps`):{indentExpr ty}"
      unless ← isDefEq (← inferType pf) ty do
        throwError "condexp_linearity: built the linearity chain{indentExpr (← inferType pf)}\n\
          which is not the goal{indentExpr ty}"
      goal.assign pf

end Causalean.Tactic.CondexpLinearity

/-! ### Worked examples and regression tests

These also pin the tactic's contract: a total success or a loud, located failure. -/

section Examples

open MeasureTheory

variable {α : Type*} {m m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}

/-- Plain difference, with the integrability witnesses in context. -/
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by condexp_linearity

/-- The integrand may be written pointwise rather than at the function level. -/
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun x => f x + g x | m] =ᵐ[μ] μ[f | m] + μ[g | m] := by condexp_linearity

/-- A three-term chain: one call replaces two `have`s and their integrability scaffolding. -/
example (a b c : α → ℝ) (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) :
    μ[fun x => a x + b x - c x | m] =ᵐ[μ] μ[a | m] + μ[b | m] - μ[c | m] := by
  condexp_linearity

/-- Either orientation of the goal works. -/
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f | m] - μ[g | m] =ᵐ[μ] μ[fun x => f x - g x | m] := by condexp_linearity

/-- Negation and scalar multiples need no integrability at all. -/
example (c : ℝ) (f : α → ℝ) : μ[-(c • f) | m] =ᵐ[μ] -(c • μ[f | m]) := by
  condexp_linearity

/-- A constant leaf is closed by `condExp_const` on a finite measure. -/
example [IsFiniteMeasure μ] (f : α → ℝ) (k : ℝ) (hf : Integrable f μ) (hm : m ≤ m₀) :
    μ[fun x => f x - k | m] =ᵐ[μ] μ[f | m] - fun _ => k := by condexp_linearity

/-- A witness that lives in a bundle can be handed over in brackets. -/
example (S : { f : α → ℝ // Integrable f μ }) (g : α → ℝ) (hg : Integrable g μ) :
    μ[fun x => S.1 x - g x | m] =ᵐ[μ] μ[S.1 | m] - μ[g | m] := by
  condexp_linearity [S.2]

/-- Products the right-hand side keeps together are kept together: the tactic follows the
right-hand side's shape rather than normalizing blindly. -/
example (y d h : α → ℝ)
    (h1 : Integrable (fun x => y x * d x) μ) (h2 : Integrable (fun x => h x * d x) μ) :
    μ[fun x => y x * d x - h x * d x | m]
      =ᵐ[μ] μ[fun x => y x * d x | m] - μ[fun x => h x * d x | m] := by
  condexp_linearity

section Wrapper

/-- A stand-in for the project's conditioning wrappers (`POVar.condExpGiven` and friends),
used only to check that `condexp_simps` unwrapping happens before normalization. -/
private noncomputable def mockCondExp (m : MeasurableSpace α) (μ : @Measure α m₀)
    (f : α → ℝ) : α → ℝ := μ[f | m]

/-- Simp-shaped defining equation of `mockCondExp`. -/
private lemma mockCondExp_eq (m : MeasurableSpace α) (μ : @Measure α m₀) (f : α → ℝ) :
    mockCondExp m μ f = μ[f | m] := rfl

attribute [local condexp_simps] mockCondExp_eq

/-- Wrapper-level goals are in scope: `condexp_simps` unwraps first. -/
example (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    mockCondExp m μ (fun x => f x - g x) =ᵐ[μ] mockCondExp m μ f - mockCondExp m μ g := by
  condexp_linearity

end Wrapper

-- Loud failure, case 1: the integrability of a summand cannot be established.
/--
error: condexp_linearity: blocked at
  f
splitting the conditional expectation here needs
  Integrable f μ
which neither `assumption` nor `fun_prop` could prove. Supply it as a hypothesis, or keep this step as a named `condExp_add`/`condExp_sub` call.
-/
#guard_msgs in
example (f g : α → ℝ) : μ[fun x => f x - g x | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by
  condexp_linearity

/-- Loud failure, case 2: a leaf the right-hand side states wrongly. The goal is left
untouched — there is no partial rewrite to clean up. -/
example (f g _h : α → ℝ) (_hf : Integrable f μ) (_hg : Integrable g μ) : True := by
  fail_if_success
    (have : μ[fun x => f x - g x | m] =ᵐ[μ] μ[f | m] - μ[_h | m] := by condexp_linearity)
  trivial

end Examples
