import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.CircleSchedule

/-!
# Certified finite complex programs

This module defines certified complex interval maps with a structural operation
count and executable composition combinators.  The same map evaluation, error
modulus, and operation count are consumed by contour schedules and by the
width proof; no caller-supplied node-width conclusion is part of this API.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A certified complex map packages [an exact complex function](hyp:value) with [an executable
interval-evaluation program over rational input rectangles and a fuel level](hyp:eval) whose
[primitive-operation count is recorded](hyp:operationCount), proved [sound — every executable
result contains the exact value at every enclosed input](hyp:sound). Increasing fuel [refines the
enclosure to a subrectangle of the previous one](hyp:fuel_nested), and refining the input
rectangle [cannot enlarge the output enclosure](hyp:input_mono). The map carries [a nonnegative
Lipschitz bound on how input width amplifies into output width](hyp:amplification,
amplification_nonneg) and [a nonincreasing sequence of algorithmic-error bounds in the
fuel](hyp:algorithmError,algorithmError_nonneg,algorithmError_antitone), such that [the evaluated
width never exceeds the algorithmic error plus the amplified input width](hyp:width_le), together
with [a computable fuel rule](hyp:errorModulus) [meeting any requested positive algorithmic-error
target](hyp:error_at_modulus). -/
structure CertifiedComplexMap where
  /-- The exact function described by the interval program. -/
  value : ℂ → ℂ
  /-- Executable interval evaluation at a rational input rectangle and fuel. -/
  eval : ComplexRatInterval → ℕ → ComplexRatInterval
  /-- The number of primitive arithmetic operations performed by one evaluation. -/
  operationCount : ℕ
  /-- Every executable result encloses the function at every enclosed input. -/
  sound : ∀ {I z}, I.Contains z → ∀ fuel, (eval I fuel).Contains (value z)
  /-- Increasing fuel produces an adjacent subrectangle for a fixed input. -/
  fuel_nested : ∀ I fuel, (eval I (fuel + 1)).Subinterval (eval I fuel)
  /-- Refining the input rectangle cannot enlarge the interval extension. -/
  input_mono : ∀ {I J}, I.Subinterval J → ∀ fuel,
    (eval I fuel).Subinterval (eval J fuel)
  /-- A nonnegative rational Lipschitz amplification bound for input width. -/
  amplification : ℚ
  /-- The input-width amplification is nonnegative. -/
  amplification_nonneg : 0 ≤ amplification
  /-- Remaining rational algorithmic width at each fuel. -/
  algorithmError : ℕ → ℚ
  /-- Algorithmic error is nonnegative at every fuel. -/
  algorithmError_nonneg : ∀ fuel, 0 ≤ algorithmError fuel
  /-- Algorithmic error does not increase when fuel increases. -/
  algorithmError_antitone : Antitone algorithmError
  /-- Width is bounded by algorithmic error plus amplified input diameter. -/
  width_le : ∀ I fuel,
    (eval I fuel).width ≤ algorithmError fuel + amplification * I.width
  /-- Executable fuel meeting each positive algorithmic-error target. -/
  errorModulus : PosRat → ℕ
  /-- The algorithmic error meets the requested target at its selected fuel. -/
  error_at_modulus : ∀ ε, algorithmError (errorModulus ε) ≤ ε.1

namespace CertifiedComplexMap

/-- The identity interval program performs no primitive arithmetic and has
unit input amplification with zero algorithmic error. -/
def identity : CertifiedComplexMap where
  value := id
  eval := fun I _ => I
  operationCount := 0
  sound := by intro I z hz fuel; exact hz
  fuel_nested := by
    intro I fuel
    exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  input_mono := by intro I J hIJ fuel; exact hIJ
  amplification := 1
  amplification_nonneg := by norm_num
  algorithmError := fun _ => 0
  algorithmError_nonneg := by intro fuel; norm_num
  algorithmError_antitone := by intro a b hab; rfl
  width_le := by intro I fuel; simp
  errorModulus := fun _ => 0
  error_at_modulus := by intro ε; exact ε.2.le

/-- A rational complex constant is a zero-operation certified program returning
the same point rectangle for every input and fuel. -/
def constant (x y : ℚ) : CertifiedComplexMap where
  value := fun _ => (x : ℝ) + (y : ℝ) * Complex.I
  eval := fun _ _ => ComplexRatInterval.point x y
  operationCount := 0
  sound := by intro I z hz fuel; exact ComplexRatInterval.point_sound x y
  fuel_nested := by
    intro I fuel
    exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  input_mono := by
    intro I J hIJ fuel
    exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  amplification := 0
  amplification_nonneg := by norm_num
  algorithmError := fun _ => 0
  algorithmError_nonneg := by intro fuel; norm_num
  algorithmError_antitone := by intro a b hab; rfl
  width_le := by
    intro I fuel
    simp [ComplexRatInterval.width, ComplexRatInterval.point,
      RatInterval.width, RatInterval.point]
  errorModulus := fun _ => 0
  error_at_modulus := by intro ε; exact ε.2.le

/-- Pointwise addition composes two certified interval programs, adds their
width amplifications and algorithmic errors, and records one new operation. -/
def add (f g : CertifiedComplexMap) : CertifiedComplexMap := by
  let δ : PosRat → PosRat := fun ε => ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
  exact {
    value := fun z => f.value z + g.value z
    eval := fun I fuel => (f.eval I fuel).add (g.eval I fuel)
    operationCount := f.operationCount + g.operationCount + 1
    sound := by
      intro I z hz fuel
      exact ComplexRatInterval.add_sound (f.sound hz fuel) (g.sound hz fuel)
    fuel_nested := by
      intro I fuel
      exact ⟨RatInterval.add_mono (f.fuel_nested I fuel).1 (g.fuel_nested I fuel).1,
        RatInterval.add_mono (f.fuel_nested I fuel).2 (g.fuel_nested I fuel).2⟩
    input_mono := by
      intro I J hIJ fuel
      exact ⟨RatInterval.add_mono (f.input_mono hIJ fuel).1 (g.input_mono hIJ fuel).1,
        RatInterval.add_mono (f.input_mono hIJ fuel).2 (g.input_mono hIJ fuel).2⟩
    amplification := f.amplification + g.amplification
    amplification_nonneg := add_nonneg f.amplification_nonneg g.amplification_nonneg
    algorithmError := fun fuel => f.algorithmError fuel + g.algorithmError fuel
    algorithmError_nonneg := fun fuel =>
      add_nonneg (f.algorithmError_nonneg fuel) (g.algorithmError_nonneg fuel)
    algorithmError_antitone := fun a b hab =>
      add_le_add (f.algorithmError_antitone hab) (g.algorithmError_antitone hab)
    width_le := by
      intro I fuel
      rw [ComplexRatInterval.width_add]
      have hf := f.width_le I fuel
      have hg := g.width_le I fuel
      have hfre := (le_max_left (f.eval I fuel).re.width
        (f.eval I fuel).im.width).trans hf
      have hfim := (le_max_right (f.eval I fuel).re.width
        (f.eval I fuel).im.width).trans hf
      have hgre := (le_max_left (g.eval I fuel).re.width
        (g.eval I fuel).im.width).trans hg
      have hgim := (le_max_right (g.eval I fuel).re.width
        (g.eval I fuel).im.width).trans hg
      exact max_le (by nlinarith) (by nlinarith)
    errorModulus := fun ε => max (f.errorModulus (δ ε)) (g.errorModulus (δ ε))
    error_at_modulus := by
      intro ε
      have hf := (f.algorithmError_antitone
        (show f.errorModulus (δ ε) ≤
          max (f.errorModulus (δ ε)) (g.errorModulus (δ ε)) from
            le_max_left _ _)).trans (f.error_at_modulus (δ ε))
      have hg := (g.algorithmError_antitone
        (show g.errorModulus (δ ε) ≤
          max (f.errorModulus (δ ε)) (g.errorModulus (δ ε)) from
            le_max_right _ _)).trans (g.error_at_modulus (δ ε))
      dsimp [δ] at hf hg ⊢
      linarith }

/-- Pointwise subtraction is a certified operation combinator with the same
width accounting as addition and one newly counted primitive operation. -/
def sub (f g : CertifiedComplexMap) : CertifiedComplexMap := by
  let δ : PosRat → PosRat := fun ε => ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
  exact {
    value := fun z => f.value z - g.value z
    eval := fun I fuel => (f.eval I fuel).sub (g.eval I fuel)
    operationCount := f.operationCount + g.operationCount + 1
    sound := by
      intro I z hz fuel
      exact ComplexRatInterval.sub_sound (f.sound hz fuel) (g.sound hz fuel)
    fuel_nested := by
      intro I fuel
      exact ⟨RatInterval.sub_mono (f.fuel_nested I fuel).1 (g.fuel_nested I fuel).1,
        RatInterval.sub_mono (f.fuel_nested I fuel).2 (g.fuel_nested I fuel).2⟩
    input_mono := by
      intro I J hIJ fuel
      exact ⟨RatInterval.sub_mono (f.input_mono hIJ fuel).1 (g.input_mono hIJ fuel).1,
        RatInterval.sub_mono (f.input_mono hIJ fuel).2 (g.input_mono hIJ fuel).2⟩
    amplification := f.amplification + g.amplification
    amplification_nonneg := add_nonneg f.amplification_nonneg g.amplification_nonneg
    algorithmError := fun fuel => f.algorithmError fuel + g.algorithmError fuel
    algorithmError_nonneg := fun fuel =>
      add_nonneg (f.algorithmError_nonneg fuel) (g.algorithmError_nonneg fuel)
    algorithmError_antitone := fun a b hab =>
      add_le_add (f.algorithmError_antitone hab) (g.algorithmError_antitone hab)
    width_le := by
      intro I fuel
      change max ((f.eval I fuel).re.sub (g.eval I fuel).re).width
          ((f.eval I fuel).im.sub (g.eval I fuel).im).width ≤ _
      rw [RatInterval.width_sub, RatInterval.width_sub]
      have hf := f.width_le I fuel
      have hg := g.width_le I fuel
      have hfre := (le_max_left (f.eval I fuel).re.width
        (f.eval I fuel).im.width).trans hf
      have hfim := (le_max_right (f.eval I fuel).re.width
        (f.eval I fuel).im.width).trans hf
      have hgre := (le_max_left (g.eval I fuel).re.width
        (g.eval I fuel).im.width).trans hg
      have hgim := (le_max_right (g.eval I fuel).re.width
        (g.eval I fuel).im.width).trans hg
      exact max_le (by nlinarith) (by nlinarith)
    errorModulus := fun ε => max (f.errorModulus (δ ε)) (g.errorModulus (δ ε))
    error_at_modulus := by
      intro ε
      have hf := (f.algorithmError_antitone
        (show f.errorModulus (δ ε) ≤
          max (f.errorModulus (δ ε)) (g.errorModulus (δ ε)) from
            le_max_left _ _)).trans (f.error_at_modulus (δ ε))
      have hg := (g.algorithmError_antitone
        (show g.errorModulus (δ ε) ≤
          max (f.errorModulus (δ ε)) (g.errorModulus (δ ε)) from
            le_max_right _ _)).trans (g.error_at_modulus (δ ε))
      dsimp [δ] at hf hg ⊢
      linarith }

/-- Multiplication composes two certified programs when uniform executable
magnitude bounds are supplied; its error and amplification use the standard
product-width propagation formula and its operation count is structural. -/
def mulWithBounds (f g : CertifiedComplexMap) (Bf Bg : ℚ)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hf : ∀ I fuel, (f.eval I fuel).maxAbs ≤ Bf)
    (hg : ∀ I fuel, (g.eval I fuel).maxAbs ≤ Bg) : CertifiedComplexMap := by
  let δf : PosRat → PosRat := fun ε =>
    ⟨ε.1 / (4 * (Bg + 1)), by
      exact div_pos ε.2 (mul_pos (by norm_num) (by linarith))⟩
  let δg : PosRat → PosRat := fun ε =>
    ⟨ε.1 / (4 * (Bf + 1)), by
      exact div_pos ε.2 (mul_pos (by norm_num) (by linarith))⟩
  exact {
    value := fun z => f.value z * g.value z
    eval := fun I fuel => (f.eval I fuel).mul (g.eval I fuel)
    operationCount := f.operationCount + g.operationCount + 1
    sound := by
      intro I z hz fuel
      exact ComplexRatInterval.mul_sound (f.sound hz fuel) (g.sound hz fuel)
    fuel_nested := by
      intro I fuel
      have hfuel := f.fuel_nested I fuel
      have gfuel := g.fuel_nested I fuel
      exact ⟨
        RatInterval.sub_mono (RatInterval.mul_mono hfuel.1 gfuel.1)
          (RatInterval.mul_mono hfuel.2 gfuel.2),
        RatInterval.add_mono (RatInterval.mul_mono hfuel.1 gfuel.2)
          (RatInterval.mul_mono hfuel.2 gfuel.1)⟩
    input_mono := by
      intro I J hIJ fuel
      have hfuel := f.input_mono hIJ fuel
      have gfuel := g.input_mono hIJ fuel
      exact ⟨
        RatInterval.sub_mono (RatInterval.mul_mono hfuel.1 gfuel.1)
          (RatInterval.mul_mono hfuel.2 gfuel.2),
        RatInterval.add_mono (RatInterval.mul_mono hfuel.1 gfuel.2)
          (RatInterval.mul_mono hfuel.2 gfuel.1)⟩
    amplification := 2 * (Bf * g.amplification + Bg * f.amplification)
    amplification_nonneg := by
      have hga := g.amplification_nonneg
      have hfa := f.amplification_nonneg
      nlinarith [mul_nonneg hBf hga, mul_nonneg hBg hfa]
    algorithmError := fun fuel =>
      2 * (Bf * g.algorithmError fuel + Bg * f.algorithmError fuel)
    algorithmError_nonneg := by
      intro fuel
      have hge := g.algorithmError_nonneg fuel
      have hfe := f.algorithmError_nonneg fuel
      nlinarith [mul_nonneg hBf hge, mul_nonneg hBg hfe]
    algorithmError_antitone := by
      intro a b hab
      have hfa := f.algorithmError_antitone hab
      have hga := g.algorithmError_antitone hab
      nlinarith [mul_le_mul_of_nonneg_left hfa hBg,
        mul_le_mul_of_nonneg_left hga hBf]
    width_le := by
      intro I fuel
      have hout := ComplexRatInterval.mul_width (f.eval I fuel) (g.eval I fuel)
      have hfw := f.width_le I fuel
      have hgw := g.width_le I fuel
      have hfA := hf I fuel
      have hgA := hg I fuel
      have hfA0 : 0 ≤ (f.eval I fuel).maxAbs :=
        (abs_nonneg (f.eval I fuel).re.lo).trans
          ((le_max_left _ _).trans (le_max_left _ _))
      have hgA0 : 0 ≤ (g.eval I fuel).maxAbs :=
        (abs_nonneg (g.eval I fuel).re.lo).trans
          ((le_max_left _ _).trans (le_max_left _ _))
      have hfw0 : 0 ≤ (f.eval I fuel).width :=
        (RatInterval.width_nonneg (f.eval I fuel).re).trans (le_max_left _ _)
      have hgw0 : 0 ≤ (g.eval I fuel).width :=
        (RatInterval.width_nonneg (g.eval I fuel).re).trans (le_max_left _ _)
      have hp1 := mul_le_mul hfA hgw hgw0 hBf
      have hp2 := mul_le_mul hgA hfw hfw0 hBg
      exact hout.trans (by nlinarith)
    errorModulus := fun ε => max (f.errorModulus (δf ε)) (g.errorModulus (δg ε))
    error_at_modulus := by
      intro ε
      have hfe := (f.algorithmError_antitone
        (show f.errorModulus (δf ε) ≤
          max (f.errorModulus (δf ε)) (g.errorModulus (δg ε)) from
            le_max_left _ _)).trans (f.error_at_modulus (δf ε))
      have hge := (g.algorithmError_antitone
        (show g.errorModulus (δg ε) ≤
          max (f.errorModulus (δf ε)) (g.errorModulus (δg ε)) from
            le_max_right _ _)).trans (g.error_at_modulus (δg ε))
      have hBg1 : 0 < Bg + 1 := by linarith
      have hBf1 : 0 < Bf + 1 := by linarith
      dsimp [δf, δg] at hfe hge ⊢
      have hfp : Bg * f.algorithmError
          (max (f.errorModulus
            ⟨ε.1 / (4 * (Bg + 1)), div_pos ε.2 (mul_pos (by norm_num) hBg1)⟩)
            (g.errorModulus ⟨ε.1 / (4 * (Bf + 1)),
              div_pos ε.2 (mul_pos (by norm_num) hBf1)⟩)) ≤ ε.1 / 4 := by
        calc
          _ ≤ Bg * (ε.1 / (4 * (Bg + 1))) :=
            mul_le_mul_of_nonneg_left hfe hBg
          _ ≤ ε.1 / 4 := by
            rw [show Bg * (ε.1 / (4 * (Bg + 1))) =
              (Bg * ε.1) / (4 * (Bg + 1)) by ring]
            apply (div_le_iff₀ (mul_pos (by norm_num) hBg1)).2
            calc
              Bg * ε.1 ≤ (Bg + 1) * ε.1 :=
                mul_le_mul_of_nonneg_right (by linarith) ε.2.le
              _ = ε.1 / 4 * (4 * (Bg + 1)) := by ring
      have hgp : Bf * g.algorithmError
          (max (f.errorModulus
            ⟨ε.1 / (4 * (Bg + 1)), div_pos ε.2 (mul_pos (by norm_num) hBg1)⟩)
            (g.errorModulus ⟨ε.1 / (4 * (Bf + 1)),
              div_pos ε.2 (mul_pos (by norm_num) hBf1)⟩)) ≤ ε.1 / 4 := by
        calc
          _ ≤ Bf * (ε.1 / (4 * (Bf + 1))) :=
            mul_le_mul_of_nonneg_left hge hBf
          _ ≤ ε.1 / 4 := by
            rw [show Bf * (ε.1 / (4 * (Bf + 1))) =
              (Bf * ε.1) / (4 * (Bf + 1)) by ring]
            apply (div_le_iff₀ (mul_pos (by norm_num) hBf1)).2
            calc
              Bf * ε.1 ≤ (Bf + 1) * ε.1 :=
                mul_le_mul_of_nonneg_right (by linarith) ε.2.le
              _ = ε.1 / 4 * (4 * (Bf + 1)) := by ring
      nlinarith }

/-- **Fuel sufficiency bound.** For [a certified complex-map evaluation algorithm](hyp:f) and
[a requested positive rational error tolerance](hyp:ε), if [the number of iterations
supplied is at least the algorithm's certified error modulus at that tolerance](hyp:fuel,h),
then [running the algorithm for that many iterations yields an approximation whose error is at
most the requested tolerance](goal). -/
theorem algorithmError_le_of_modulus {f : CertifiedComplexMap} {ε : PosRat} {fuel : ℕ}
    (h : f.errorModulus ε ≤ fuel) : f.algorithmError fuel ≤ ε.1 := by
  exact (f.algorithmError_antitone h).trans (f.error_at_modulus ε)

end CertifiedComplexMap

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
