import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.List.GetD

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

/-- Defines hybrid Term Index, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable abbrev hybridTermIndex := factorialExpansionIndex

/-! ### A verified tree-to-straight-line compiler -/

/-- Syntax trees over exactly the operations admitted by
`RealArithmeticInstruction`. -/
inductive RealArithmeticExpression (ι : Type*) where
  | input (i : ι)
  | const (x : ℝ)
  | add (x y : RealArithmeticExpression ι)
  | sub (x y : RealArithmeticExpression ι)
  | mul (x y : RealArithmeticExpression ι)
  | div (x y : RealArithmeticExpression ι)
  | branchNonpos (test yes no : RealArithmeticExpression ι)

namespace RealArithmeticExpression

noncomputable def eval {ι : Type*} (input : ι → ℝ) : RealArithmeticExpression ι → ℝ
  | .input i => input i
  | .const x => x
  | .add x y => eval input x + eval input y
  | .sub x y => eval input x - eval input y
  | .mul x y => eval input x * eval input y
  | .div x y => eval input x / eval input y
  | .branchNonpos test yes no =>
      if eval input test ≤ 0 then eval input yes else eval input no

/-- Defines node Count, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def nodeCount {ι : Type*} : RealArithmeticExpression ι → ℕ
  | .input _ | .const _ => 1
  | .add x y | .sub x y | .mul x y | .div x y => nodeCount x + nodeCount y + 1
  | .branchNonpos t y n => nodeCount t + nodeCount y + nodeCount n + 1

/-- Defines operation Count, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def operationCount {ι : Type*} : RealArithmeticExpression ι → ℕ
  | .input _ | .const _ => 0
  | .add x y | .sub x y | .mul x y | .div x y =>
      operationCount x + operationCount y + 1
  | .branchNonpos t y n =>
      operationCount t + operationCount y + operationCount n + 1

/-- Establishes the stated property of node Count pos in the discrete average-treatment-effect construction. -/
lemma nodeCount_pos {ι : Type*} (e : RealArithmeticExpression ι) : 0 < nodeCount e := by
  cases e <;> simp [nodeCount]

/-- Compile an expression after `offset` already occupied registers. -/
def codeAt {ι : Type*} (offset : ℕ) :
    RealArithmeticExpression ι → List (RealArithmeticInstruction ι)
  | .input i => [.input i]
  | .const x => [.const x]
  | .add x y => codeAt offset x ++ codeAt (offset + nodeCount x) y ++
      [.add (offset + nodeCount x - 1) (offset + nodeCount x + nodeCount y - 1)]
  | .sub x y => codeAt offset x ++ codeAt (offset + nodeCount x) y ++
      [.sub (offset + nodeCount x - 1) (offset + nodeCount x + nodeCount y - 1)]
  | .mul x y => codeAt offset x ++ codeAt (offset + nodeCount x) y ++
      [.mul (offset + nodeCount x - 1) (offset + nodeCount x + nodeCount y - 1)]
  | .div x y => codeAt offset x ++ codeAt (offset + nodeCount x) y ++
      [.div (offset + nodeCount x - 1) (offset + nodeCount x + nodeCount y - 1)]
  | .branchNonpos t y n =>
      codeAt offset t ++ codeAt (offset + nodeCount t) y ++
      codeAt (offset + nodeCount t + nodeCount y) n ++
      [.branchNonpos (offset + nodeCount t - 1)
        (offset + nodeCount t + nodeCount y - 1)
        (offset + nodeCount t + nodeCount y + nodeCount n - 1)]

/-- The compiled instruction list for an expression has exactly one instruction per node of its expression tree. -/
@[simp] lemma length_codeAt {ι : Type*} (offset : ℕ)
    (e : RealArithmeticExpression ι) : (codeAt offset e).length = nodeCount e := by
  induction e generalizing offset with
  | input i => simp [codeAt, nodeCount]
  | const x => simp [codeAt, nodeCount]
  | add x y ihx ihy => simp [codeAt, nodeCount, ihx, ihy] <;> omega
  | sub x y ihx ihy => simp [codeAt, nodeCount, ihx, ihy] <;> omega
  | mul x y ihx ihy => simp [codeAt, nodeCount, ihx, ihy] <;> omega
  | div x y ihx ihy => simp [codeAt, nodeCount, ihx, ihy] <;> omega
  | branchNonpos t y n iht ihy ihn =>
      simp [codeAt, nodeCount, iht, ihy, ihn] <;> omega

/-- Defines run From, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def runFrom {ι : Type*} (input : ι → ℝ) (registers : List ℝ)
    (code : List (RealArithmeticInstruction ι)) : List ℝ :=
  code.foldl (fun rs instruction => rs ++
    [RealArithmeticProgram.instructionValue input rs instruction]) registers

/-- Establishes the stated property of run From append in the discrete average-treatment-effect construction. -/
lemma runFrom_append {ι : Type*} (input : ι → ℝ) (registers : List ℝ)
    (xs ys : List (RealArithmeticInstruction ι)) :
    runFrom input registers (xs ++ ys) = runFrom input (runFrom input registers xs) ys := by
  simp [runFrom, List.foldl_append]

/-- Establishes the stated equality relating run From eq append. -/
lemma runFrom_eq_append {ι : Type*} (input : ι → ℝ) (registers : List ℝ)
    (code : List (RealArithmeticInstruction ι)) :
    ∃ tail, runFrom input registers code = registers ++ tail := by
  induction code generalizing registers with
  | nil => exact ⟨[], by simp [runFrom]⟩
  | cons i code ih =>
      rcases ih (registers ++
        [RealArithmeticProgram.instructionValue input registers i]) with ⟨tail, htail⟩
      refine ⟨RealArithmeticProgram.instructionValue input registers i :: tail, ?_⟩
      rw [show runFrom input registers (i :: code) =
        runFrom input (registers ++
          [RealArithmeticProgram.instructionValue input registers i]) code by rfl]
      rw [htail]
      simp

/-- Establishes the stated property of run From get D of lt in the discrete average-treatment-effect construction. -/
lemma runFrom_getD_of_lt {ι : Type*} (input : ι → ℝ) (registers : List ℝ)
    (code : List (RealArithmeticInstruction ι)) (i : ℕ) (hi : i < registers.length) :
    (runFrom input registers code).getD i 0 = registers.getD i 0 := by
  rcases runFrom_eq_append input registers code with ⟨tail, htail⟩
  rw [htail, List.getD_append _ _ _ _ hi]

/-- Executing a list of instructions appends exactly one register value for each instruction, leaving the initial registers in place. -/
@[simp] lemma length_runFrom {ι : Type*} (input : ι → ℝ) (registers : List ℝ)
    (code : List (RealArithmeticInstruction ι)) :
    (runFrom input registers code).length = registers.length + code.length := by
  induction code generalizing registers with
  | nil => simp [runFrom]
  | cons i code ih =>
      rw [show runFrom input registers (i :: code) =
        runFrom input (registers ++
          [RealArithmeticProgram.instructionValue input registers i]) code by rfl]
      rw [ih]
      simp
      omega

/-- Establishes the stated upper bound for get D append singleton length. -/
lemma getD_append_singleton_length (xs : List ℝ) (x : ℝ) :
    (xs ++ [x]).getD xs.length 0 = x := by simp

/-- Establishes the stated property of code At correct in the discrete average-treatment-effect construction. -/
lemma codeAt_correct {ι : Type*} (input : ι → ℝ) (registers : List ℝ)
    (e : RealArithmeticExpression ι) :
    (runFrom input registers (codeAt registers.length e)).getD
      (registers.length + nodeCount e - 1) 0 = eval input e := by
  induction e generalizing registers with
  | input i => simp [codeAt, nodeCount, runFrom, eval,
      RealArithmeticProgram.instructionValue]
  | const x => simp [codeAt, nodeCount, runFrom, eval,
      RealArithmeticProgram.instructionValue]
  | add x y ihx ihy =>
      rw [codeAt, runFrom_append, runFrom_append]
      let rx := runFrom input registers (codeAt registers.length x)
      have hrx : rx.length = registers.length + nodeCount x := by simp [rx]
      let ry := runFrom input rx (codeAt (registers.length + nodeCount x) y)
      have hry : ry.length = registers.length + nodeCount x + nodeCount y := by
        simp [ry, hrx]
      change (runFrom input ry [RealArithmeticInstruction.add
        (registers.length + nodeCount x - 1)
        (registers.length + nodeCount x + nodeCount y - 1)]).getD _ 0 = _
      simp only [runFrom, List.foldl_cons, List.foldl_nil]
      simp only [nodeCount, eval]
      rw [show registers.length + (nodeCount x + nodeCount y + 1) - 1 = ry.length by omega]
      rw [getD_append_singleton_length]
      simp only [RealArithmeticProgram.instructionValue]
      have hx := ihx registers
      have hy := ihy rx
      rw [show rx.length = registers.length + nodeCount x from hrx] at hy
      have hx' : ry.getD (registers.length + nodeCount x - 1) 0 = eval input x := by
        have hpos := nodeCount_pos x
        rw [runFrom_getD_of_lt input rx _ _ (by rw [hrx]; omega)]
        exact hx
      exact congrArg₂ (· + ·) hx' hy
  | sub x y ihx ihy =>
      rw [codeAt, runFrom_append, runFrom_append]
      let rx := runFrom input registers (codeAt registers.length x)
      have hrx : rx.length = registers.length + nodeCount x := by simp [rx]
      let ry := runFrom input rx (codeAt (registers.length + nodeCount x) y)
      have hry : ry.length = registers.length + nodeCount x + nodeCount y := by
        simp [ry, hrx]
      change (runFrom input ry [RealArithmeticInstruction.sub
        (registers.length + nodeCount x - 1)
        (registers.length + nodeCount x + nodeCount y - 1)]).getD _ 0 = _
      simp only [runFrom, List.foldl_cons, List.foldl_nil]
      simp only [nodeCount, eval]
      rw [show registers.length + (nodeCount x + nodeCount y + 1) - 1 = ry.length by omega]
      rw [getD_append_singleton_length]
      simp only [RealArithmeticProgram.instructionValue]
      have hx := ihx registers
      have hy := ihy rx
      rw [show rx.length = registers.length + nodeCount x from hrx] at hy
      have hx' : ry.getD (registers.length + nodeCount x - 1) 0 = eval input x := by
        have hpos := nodeCount_pos x
        rw [runFrom_getD_of_lt input rx _ _ (by rw [hrx]; omega)]
        exact hx
      exact congrArg₂ (· - ·) hx' hy
  | mul x y ihx ihy =>
      rw [codeAt, runFrom_append, runFrom_append]
      let rx := runFrom input registers (codeAt registers.length x)
      have hrx : rx.length = registers.length + nodeCount x := by simp [rx]
      let ry := runFrom input rx (codeAt (registers.length + nodeCount x) y)
      have hry : ry.length = registers.length + nodeCount x + nodeCount y := by
        simp [ry, hrx]
      change (runFrom input ry [RealArithmeticInstruction.mul
        (registers.length + nodeCount x - 1)
        (registers.length + nodeCount x + nodeCount y - 1)]).getD _ 0 = _
      simp only [runFrom, List.foldl_cons, List.foldl_nil]
      simp only [nodeCount, eval]
      rw [show registers.length + (nodeCount x + nodeCount y + 1) - 1 = ry.length by omega]
      rw [getD_append_singleton_length]
      simp only [RealArithmeticProgram.instructionValue]
      have hx := ihx registers
      have hy := ihy rx
      rw [show rx.length = registers.length + nodeCount x from hrx] at hy
      have hx' : ry.getD (registers.length + nodeCount x - 1) 0 = eval input x := by
        have hpos := nodeCount_pos x
        rw [runFrom_getD_of_lt input rx _ _ (by rw [hrx]; omega)]
        exact hx
      exact congrArg₂ (· * ·) hx' hy
  | div x y ihx ihy =>
      rw [codeAt, runFrom_append, runFrom_append]
      let rx := runFrom input registers (codeAt registers.length x)
      have hrx : rx.length = registers.length + nodeCount x := by simp [rx]
      let ry := runFrom input rx (codeAt (registers.length + nodeCount x) y)
      have hry : ry.length = registers.length + nodeCount x + nodeCount y := by
        simp [ry, hrx]
      change (runFrom input ry [RealArithmeticInstruction.div
        (registers.length + nodeCount x - 1)
        (registers.length + nodeCount x + nodeCount y - 1)]).getD _ 0 = _
      simp only [runFrom, List.foldl_cons, List.foldl_nil]
      simp only [nodeCount, eval]
      rw [show registers.length + (nodeCount x + nodeCount y + 1) - 1 = ry.length by omega]
      rw [getD_append_singleton_length]
      simp only [RealArithmeticProgram.instructionValue]
      have hx := ihx registers
      have hy := ihy rx
      rw [show rx.length = registers.length + nodeCount x from hrx] at hy
      have hx' : ry.getD (registers.length + nodeCount x - 1) 0 = eval input x := by
        have hpos := nodeCount_pos x
        rw [runFrom_getD_of_lt input rx _ _ (by rw [hrx]; omega)]
        exact hx
      exact congrArg₂ (· / ·) hx' hy
  | branchNonpos t y n iht ihy ihn =>
      rw [codeAt, runFrom_append, runFrom_append, runFrom_append]
      let rt := runFrom input registers (codeAt registers.length t)
      have hrt : rt.length = registers.length + nodeCount t := by simp [rt]
      let ry := runFrom input rt (codeAt (registers.length + nodeCount t) y)
      have hry : ry.length = registers.length + nodeCount t + nodeCount y := by
        simp [ry, hrt]
      let rn := runFrom input ry
        (codeAt (registers.length + nodeCount t + nodeCount y) n)
      have hrn : rn.length =
          registers.length + nodeCount t + nodeCount y + nodeCount n := by
        simp [rn, hry]
      change (runFrom input rn [RealArithmeticInstruction.branchNonpos
        (registers.length + nodeCount t - 1)
        (registers.length + nodeCount t + nodeCount y - 1)
        (registers.length + nodeCount t + nodeCount y + nodeCount n - 1)]).getD _ 0 = _
      simp only [runFrom, List.foldl_cons, List.foldl_nil]
      simp only [nodeCount, eval]
      rw [show registers.length +
          (nodeCount t + nodeCount y + nodeCount n + 1) - 1 = rn.length by omega]
      rw [getD_append_singleton_length]
      simp only [RealArithmeticProgram.instructionValue]
      have ht := iht registers
      have hy := ihy rt
      have hn := ihn ry
      rw [show rt.length = registers.length + nodeCount t from hrt] at hy
      rw [show ry.length = registers.length + nodeCount t + nodeCount y from hry] at hn
      have ht' : rn.getD (registers.length + nodeCount t - 1) 0 = eval input t := by
        have htpos := nodeCount_pos t
        rw [runFrom_getD_of_lt input ry _ _ (by rw [hry]; omega)]
        rw [runFrom_getD_of_lt input rt _ _ (by rw [hrt]; omega)]
        exact ht
      have hy' : rn.getD (registers.length + nodeCount t + nodeCount y - 1) 0 =
          eval input y := by
        have htpos := nodeCount_pos t
        have hypos := nodeCount_pos y
        rw [runFrom_getD_of_lt input ry _ _ (by rw [hry]; omega)]
        exact hy
      rw [ht', hy', hn]

/-- Defines program, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def program {ι : Type*} (e : RealArithmeticExpression ι) :
    RealArithmeticProgram ι := (codeAt 0 e, nodeCount e - 1)

/-- Establishes the stated property of eval program in the discrete average-treatment-effect construction. -/
lemma eval_program {ι : Type*} (e : RealArithmeticExpression ι) (input : ι → ℝ) :
    (program e).eval input = eval input e := by
  simpa [program, RealArithmeticProgram.eval, RealArithmeticProgram.run, runFrom]
    using codeAt_correct input [] e

/-- Establishes the stated property of operation Count code At in the discrete average-treatment-effect construction. -/
lemma operationCount_codeAt {ι : Type*} (offset : ℕ)
    (e : RealArithmeticExpression ι) :
    ((codeAt offset e).map RealArithmeticProgram.instructionCost).sum = operationCount e := by
  induction e generalizing offset with
  | input i => simp [codeAt, operationCount, RealArithmeticProgram.instructionCost]
  | const x => simp [codeAt, operationCount, RealArithmeticProgram.instructionCost]
  | add x y ihx ihy =>
      simp [codeAt, operationCount, ihx, ihy, RealArithmeticProgram.instructionCost] <;> omega
  | sub x y ihx ihy =>
      simp [codeAt, operationCount, ihx, ihy, RealArithmeticProgram.instructionCost] <;> omega
  | mul x y ihx ihy =>
      simp [codeAt, operationCount, ihx, ihy, RealArithmeticProgram.instructionCost] <;> omega
  | div x y ihx ihy =>
      simp [codeAt, operationCount, ihx, ihy, RealArithmeticProgram.instructionCost] <;> omega
  | branchNonpos t y n iht ihy ihn =>
      simp [codeAt, operationCount, iht, ihy, ihn,
        RealArithmeticProgram.instructionCost] <;> omega

/-- Establishes the stated property of operation Count program in the discrete average-treatment-effect construction. -/
lemma operationCount_program {ι : Type*} (e : RealArithmeticExpression ι) :
    (program e).operationCount = operationCount e := by
  simp [program, RealArithmeticProgram.operationCount, operationCount_codeAt]

end RealArithmeticExpression

open RealArithmeticExpression

/-- Defines expression Sum, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def expressionSum {ι : Type*} :
    List (RealArithmeticExpression ι) → RealArithmeticExpression ι
  | [] => .const 0
  | x :: xs => .add x (expressionSum xs)

/-- Defines expression Product, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def expressionProduct {ι : Type*} :
    List (RealArithmeticExpression ι) → RealArithmeticExpression ι
  | [] => .const 1
  | x :: xs => .mul x (expressionProduct xs)

/-- Establishes the stated equality relating list range sum eq finset sum. -/
lemma list_range_sum_eq_finset_sum {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ihm => simp [List.range_succ, Finset.sum_range_succ, ihm]

/-- Evaluating the expression formed by summing a list gives the sum of the separately evaluated expressions. -/
@[simp] lemma eval_expressionSum {ι : Type*} (input : ι → ℝ)
    (xs : List (RealArithmeticExpression ι)) :
    eval input (expressionSum xs) = (xs.map (eval input)).sum := by
  induction xs <;> simp [expressionSum, eval, *]

/-- Evaluating the expression formed by multiplying a list gives the product of the separately evaluated expressions. -/
@[simp] lemma eval_expressionProduct {ι : Type*} (input : ι → ℝ)
    (xs : List (RealArithmeticExpression ι)) :
    eval input (expressionProduct xs) = (xs.map (eval input)).prod := by
  induction xs <;> simp [expressionProduct, eval, *]

/-- The cost of a summed expression is the sum of the component costs plus one addition for every list entry. -/
@[simp] lemma operationCount_expressionSum {ι : Type*}
    (xs : List (RealArithmeticExpression ι)) :
    operationCount (expressionSum xs) =
      (xs.map operationCount).sum + xs.length := by
  induction xs <;> simp [expressionSum, operationCount, *] <;> omega

/-- The cost of a product expression is the sum of the component costs plus one multiplication for every list entry. -/
@[simp] lemma operationCount_expressionProduct {ι : Type*}
    (xs : List (RealArithmeticExpression ι)) :
    operationCount (expressionProduct xs) =
      (xs.map operationCount).sum + xs.length := by
  induction xs <;> simp [expressionProduct, operationCount, *] <;> omega

/-- Real-arithmetic implementation of truncated natural subtraction, on
natural-valued inputs. -/
def natSubExpression {ι : Type*} (x : RealArithmeticExpression ι) (i : ℕ) :
    RealArithmeticExpression ι :=
  .branchNonpos (.sub x (.const i)) (.const 0) (.sub x (.const i))

lemma eval_natSubExpression {ι : Type*} (input : ι → ℝ)
    (x : RealArithmeticExpression ι) (z i : ℕ) (hx : eval input x = z) :
    eval input (natSubExpression x i) = (z - i : ℕ) := by
  simp only [natSubExpression, eval, hx]
  by_cases h : z ≤ i
  · have hcast : (z : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr h
    have hr : (z : ℝ) - (i : ℝ) ≤ 0 := sub_nonpos.mpr hcast
    rw [if_pos hr]
    simp [Nat.sub_eq_zero_of_le h]
  · have hlt : i < z := Nat.lt_of_not_ge h
    have hle : i ≤ z := Nat.le_of_lt hlt
    have hcast : (i : ℝ) < (z : ℝ) := Nat.cast_lt.mpr hlt
    have hr : ¬(z : ℝ) - (i : ℝ) ≤ 0 := not_le.mpr (sub_pos.mpr hcast)
    rw [if_neg hr]
    exact (Nat.cast_sub hle).symm

/-- Defines falling Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def fallingExpression {ι : Type*} (x : RealArithmeticExpression ι) :
    ℕ → RealArithmeticExpression ι
  | 0 => .const 1
  | r + 1 => .mul (natSubExpression x r) (fallingExpression x r)

/-- Establishes the stated property of eval falling Expression in the discrete average-treatment-effect construction. -/
lemma eval_fallingExpression {ι : Type*} (input : ι → ℝ)
    (x : RealArithmeticExpression ι) (z r : ℕ) (hx : eval input x = z) :
    eval input (fallingExpression x r) = (z.descFactorial r : ℕ) := by
  induction r with
  | zero => simp [fallingExpression, eval]
  | succ r ihr =>
      simp only [fallingExpression, eval, eval_natSubExpression input x z r hx, ihr,
        Nat.descFactorial_succ, Nat.cast_mul]

/-- Establishes the stated property of operation Count nat Sub Expression in the discrete average-treatment-effect construction. -/
lemma operationCount_natSubExpression {ι : Type*}
    (x : RealArithmeticExpression ι) (i : ℕ) :
    operationCount (natSubExpression x i) = 2 * operationCount x + 3 := by
  simp [natSubExpression, operationCount]
  omega

/-- Establishes the stated property of operation Count falling Expression in the discrete average-treatment-effect construction. -/
lemma operationCount_fallingExpression {ι : Type*}
    (x : RealArithmeticExpression ι) (r : ℕ) :
    operationCount (fallingExpression x r) =
      r * (2 * operationCount x + 4) := by
  induction r with
  | zero => simp [fallingExpression, operationCount]
  | succ r ihr =>
      simp only [fallingExpression, operationCount, operationCount_natSubExpression, ihr]
      ring

/-- Defines hybrid Cell List, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def hybridCellList : List Cell := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- Establishes the stated summation identity or bound for hybrid Cell List sum. -/
lemma hybridCellList_sum (f : Cell → ℝ) :
    (hybridCellList.map f).sum = ∑ ay : Cell, f ay := by
  rw [Fintype.sum_prod_type]
  simp [hybridCellList, Fin.sum_univ_two]
  ring

/-- Establishes the stated property of hybrid Cell List prod in the discrete average-treatment-effect construction. -/
lemma hybridCellList_prod (f : Cell → ℝ) :
    (hybridCellList.map f).prod = ∏ ay : Cell, f ay := by
  rw [Fintype.prod_prod_type]
  simp [hybridCellList, Fin.prod_univ_two]
  ring

/-- Establishes the stated equality relating split Category Count eq sum cell. -/
lemma splitCategoryCount_eq_sum_cell {n d : ℕ} (sample : Fin n → Obs d)
    (j : Fin 2) (k : Fin d) :
    splitCategoryCount sample j k = ∑ a : Fin 2, ∑ y : Fin 2,
      splitCellCount sample j k a y := by
  classical
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [splitCategoryCount, splitCellCount, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hobs : sample i with ⟨k', a', y'⟩
  simp only [hobs, Prod.fst]
  by_cases hk : k' = k
  · subst k'
    fin_cases a' <;> fin_cases y' <;> simp [finTwoEquiv]
  · simp [hk]

/-- Defines split Count Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def splitCountExpression {d : ℕ} (j : Fin 2) (k : Fin d) (ay : Cell) :
    RealArithmeticExpression (HybridCountInput d) := .input (j, k, ay.1, ay.2)

/-- Defines category Count Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def categoryCountExpression {d : ℕ} (j : Fin 2) (k : Fin d) :
    RealArithmeticExpression (HybridCountInput d) :=
  expressionSum (hybridCellList.map (splitCountExpression j k))

/-- Establishes the stated property of eval split Count Expression in the discrete average-treatment-effect construction. -/
lemma eval_splitCountExpression {n d : ℕ} (sample : Fin n → Obs d)
    (j : Fin 2) (k : Fin d) (ay : Cell) :
    eval (hybridCountVector sample) (splitCountExpression j k ay) =
      splitCellCount sample j k ay.1 ay.2 := by
  rfl

/-- Establishes the stated property of eval category Count Expression in the discrete average-treatment-effect construction. -/
lemma eval_categoryCountExpression {n d : ℕ} (sample : Fin n → Obs d)
    (j : Fin 2) (k : Fin d) :
    eval (hybridCountVector sample) (categoryCountExpression j k) =
      splitCategoryCount sample j k := by
  simp only [categoryCountExpression, eval_expressionSum, List.map_map,
    Function.comp_apply, eval_splitCountExpression, hybridCellList_sum]
  rw [splitCategoryCount_eq_sum_cell]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- Defines factorial Monomial Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def factorialMonomialExpression {n d : ℕ} (k : Fin d) (r : MultiIndex) :
    RealArithmeticExpression (HybridCountInput d) :=
  .div
    (expressionProduct (hybridCellList.map fun ay =>
      fallingExpression (splitCountExpression 1 k ay) (r ay)))
    (.const (fallingFactorial (splitSize n 1) (multiDegree r) : ℝ))

/-- Establishes the stated property of eval factorial Monomial Expression in the discrete average-treatment-effect construction. -/
lemma eval_factorialMonomialExpression {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (r : MultiIndex) :
    eval (hybridCountVector sample) (factorialMonomialExpression (n := n) k r) =
      factorialMonomial sample k r := by
  simp only [factorialMonomialExpression, eval, eval_expressionProduct,
    List.map_map, Function.comp_apply]
  rw [hybridCellList_prod]
  apply congrArg (fun x : ℝ => x /
    (fallingFactorial (splitSize n 1) (multiDegree r) : ℝ))
  apply Finset.prod_congr rfl
  intro ay hay
  exact eval_fallingExpression _ _ _ _ (eval_splitCountExpression sample 1 k ay)

/-- Establishes the stated property of operation Count split Count Expression in the discrete average-treatment-effect construction. -/
lemma operationCount_splitCountExpression {d : ℕ} (j : Fin 2)
    (k : Fin d) (ay : Cell) : operationCount (splitCountExpression j k ay) = 0 := rfl

/-- Establishes the stated property of operation Count factorial Monomial Expression in the discrete average-treatment-effect construction. -/
lemma operationCount_factorialMonomialExpression {n d : ℕ}
    (k : Fin d) (r : MultiIndex) :
    operationCount (factorialMonomialExpression (n := n) k r) =
      4 * multiDegree r + 5 := by
  simp [factorialMonomialExpression, operationCount, hybridCellList,
    operationCount_fallingExpression, operationCount_splitCountExpression]
  rw [show multiDegree r =
      r (0, 0) + r (0, 1) + r (1, 0) + r (1, 1) by
    simp only [multiDegree]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    omega]
  omega

/-- Defines arm Factorial Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def armFactorialExpression (n : ℕ) {d : ℕ} (k : Fin d) (a : Fin 2) :
    RealArithmeticExpression (HybridCountInput d) :=
  let M := polynomialDegree n
  let B := bandwidth n
  expressionSum ((List.range (M - 1)).map fun j =>
    expressionSum ((List.range (j + 1)).map fun t =>
      expressionSum (hybridCellList.map fun ay =>
        .mul
          (.const (B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)))
          (factorialMonomialExpression (n := n) k (hybridTermIndex a ay j t)))))

/-- Defines light Cell Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def lightCellExpression (n : ℕ) {d : ℕ} (k : Fin d) :
    RealArithmeticExpression (HybridCountInput d) :=
  .sub (armFactorialExpression n k 1) (armFactorialExpression n k 0)

/-- Establishes the stated property of eval arm Factorial Expression in the discrete average-treatment-effect construction. -/
lemma eval_armFactorialExpression {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (a : Fin 2) :
    eval (hybridCountVector sample) (armFactorialExpression n k a) =
      ∑ j ∈ Finset.range (polynomialDegree n - 1),
        ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
          ((bandwidth n)⁻¹ * gCoefficient (polynomialDegree n) j *
              (bandwidth n)⁻¹ ^ j * (Nat.choose j t : ℝ)) *
            factorialMonomial sample k (hybridTermIndex a ay j t) := by
  simp only [armFactorialExpression, eval_expressionSum, List.map_map]
  rw [list_range_sum_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp_apply, eval_expressionSum, List.map_map]
  rw [list_range_sum_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Function.comp_apply, eval_expressionSum, List.map_map, eval]
  rw [hybridCellList_sum]
  apply Finset.sum_congr rfl
  intro ay hay
  simp [Function.comp_apply, eval, eval_factorialMonomialExpression]

/-- Establishes the stated property of eval light Cell Expression in the discrete average-treatment-effect construction. -/
lemma eval_lightCellExpression {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    eval (hybridCountVector sample) (lightCellExpression n k) =
      factorialPolynomialContribution sample k := by
  simp only [lightCellExpression, eval, factorialPolynomialContribution]
  rw [eval_armFactorialExpression, eval_armFactorialExpression]

/-- Establishes the stated property of multi Degree hybrid Term Index in the discrete average-treatment-effect construction. -/
lemma multiDegree_hybridTermIndex (a : Fin 2) (ay : Cell) (j t : ℕ)
    (ht : t ≤ j) : multiDegree (hybridTermIndex a ay j t) = j + 2 := by
  unfold hybridTermIndex factorialExpansionIndex multiDegree
  rw [Finsupp.sum_add_index (by simp) (by simp),
    Finsupp.sum_add_index (by simp) (by simp),
    Finsupp.sum_add_index (by simp) (by simp)]
  simp only [Finsupp.sum_single_index]
  omega

/-- Establishes the stated property of operation Count factorial Term in the discrete average-treatment-effect construction. -/
lemma operationCount_factorialTerm {n d : ℕ} (k : Fin d) (a : Fin 2)
    (ay : Cell) (j t : ℕ) (ht : t ≤ j) (c : ℝ) :
    operationCount (.mul (.const c)
      (factorialMonomialExpression (n := n) k (hybridTermIndex a ay j t))) =
      4 * j + 14 := by
  simp [operationCount, operationCount_factorialMonomialExpression,
    multiDegree_hybridTermIndex a ay j t ht]
  omega

/-- Establishes the stated upper bound for list sum map le length mul. -/
lemma list_sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, f y ≤ C := by
        intro y hy
        exact h y (by simp [hy])
      have := ih hxs
      nlinarith

/-- Establishes the stated upper bound for operation Count arm Factorial Expression le. -/
lemma operationCount_armFactorialExpression_le {n d : ℕ} (k : Fin d) (a : Fin 2)
    (hM : 2 ≤ polynomialDegree n) :
    operationCount (armFactorialExpression n k a) ≤
      52 * polynomialDegree n ^ 3 := by
  let M := polynomialDegree n
  have hM' : 2 ≤ M := hM
  have hcell : ∀ j ∈ List.range (M - 1), ∀ t ∈ List.range (j + 1),
      operationCount (expressionSum (hybridCellList.map fun ay =>
        RealArithmeticExpression.mul
          (.const ((bandwidth n)⁻¹ * gCoefficient M j *
            (bandwidth n)⁻¹ ^ j * (Nat.choose j t : ℝ)))
          (factorialMonomialExpression (n := n) k (hybridTermIndex a ay j t)))) ≤
        50 * M := by
    intro j hj t ht
    have hjM : j < M := by
      have : j < M - 1 := List.mem_range.mp hj
      omega
    have htj : t ≤ j := by
      have : t < j + 1 := List.mem_range.mp ht
      omega
    simp only [operationCount_expressionSum, List.map_map, hybridCellList,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    rw [operationCount_factorialTerm k a (0, 0) j t htj,
      operationCount_factorialTerm k a (0, 1) j t htj,
      operationCount_factorialTerm k a (1, 0) j t htj,
      operationCount_factorialTerm k a (1, 1) j t htj]
    omega
  have htlevel : ∀ j ∈ List.range (M - 1),
      operationCount (expressionSum ((List.range (j + 1)).map fun t =>
        expressionSum (hybridCellList.map fun ay =>
          RealArithmeticExpression.mul
            (.const ((bandwidth n)⁻¹ * gCoefficient M j *
              (bandwidth n)⁻¹ ^ j * (Nat.choose j t : ℝ)))
            (factorialMonomialExpression (n := n) k (hybridTermIndex a ay j t))))) ≤
        51 * M ^ 2 := by
    intro j hj
    simp only [operationCount_expressionSum, List.map_map, Function.comp_apply,
      List.length_range]
    apply le_trans (Nat.add_le_add
      (list_sum_map_le_length_mul (List.range (j + 1)) _ (50 * M)
        (fun t ht => hcell j hj t ht)) (le_refl _))
    have hjM : j + 1 ≤ M := by
      have : j < M - 1 := List.mem_range.mp hj
      omega
    simp only [List.length_range, List.length_map]
    nlinarith
  simp only [armFactorialExpression, operationCount_expressionSum, List.map_map,
    Function.comp_apply, List.length_range]
  apply le_trans (Nat.add_le_add
    (list_sum_map_le_length_mul (List.range (M - 1)) _ (51 * M ^ 2) htlevel)
    (le_refl _))
  simp only [List.length_range, List.length_map]
  dsimp [M] at *
  nlinarith [Nat.sub_le (polynomialDegree n) 1]

/-- Establishes the stated upper bound for operation Count light Cell Expression le. -/
lemma operationCount_lightCellExpression_le {n d : ℕ} (k : Fin d)
    (hM : 2 ≤ polynomialDegree n) :
    operationCount (lightCellExpression n k) ≤ 105 * polynomialDegree n ^ 4 := by
  simp only [lightCellExpression, operationCount]
  have h1 := operationCount_armFactorialExpression_le k (1 : Fin 2) hM
  have h0 := operationCount_armFactorialExpression_le k (0 : Fin 2) hM
  have hM1 : 1 ≤ polynomialDegree n := le_trans (by omega) hM
  have hpow : polynomialDegree n ^ 3 ≤ polynomialDegree n ^ 4 := by
    exact Nat.pow_le_pow_right hM1 (by omega)
  have hpow1 : 1 ≤ polynomialDegree n ^ 4 := by
    exact one_le_pow₀ hM1
  omega

/-- Defines heavy Cell Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def heavyCellExpression (n : ℕ) {d : ℕ} (k : Fin d) :
    RealArithmeticExpression (HybridCountInput d) :=
  let Nk := categoryCountExpression 1 k
  let N1 := .add (splitCountExpression 1 k (1, 0))
    (splitCountExpression 1 k (1, 1))
  let N0 := .add (splitCountExpression 1 k (0, 0))
    (splitCountExpression 1 k (0, 1))
  .mul (.div Nk (.const (splitSize n 1)))
    (.sub (.div (splitCountExpression 1 k (1, 1)) N1)
      (.div (splitCountExpression 1 k (0, 1)) N0))

/-- Establishes the stated property of eval heavy Cell Expression in the discrete average-treatment-effect construction. -/
lemma eval_heavyCellExpression {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    eval (hybridCountVector sample) (heavyCellExpression n k) =
      empiricalRatioCell sample k := by
  simp [heavyCellExpression, empiricalRatioCell, eval,
    eval_categoryCountExpression, eval_splitCountExpression]

/-- Establishes the stated property of operation Count heavy Cell Expression in the discrete average-treatment-effect construction. -/
lemma operationCount_heavyCellExpression {n d : ℕ} (k : Fin d) :
    operationCount (heavyCellExpression n k) = 11 := by
  simp [heavyCellExpression, categoryCountExpression, hybridCellList,
    operationCount, operationCount_splitCountExpression]

/-- Defines selected Cell Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def selectedCellExpression (n : ℕ) {d : ℕ} (k : Fin d) :
    RealArithmeticExpression (HybridCountInput d) :=
  if n < calibrationCutoff then heavyCellExpression n k else
    .branchNonpos
      (.sub (categoryCountExpression 0 k) (.const (lambda0 * logScale n)))
      (lightCellExpression n k) (heavyCellExpression n k)

/-- Establishes the stated upper bound for eval selected Cell Expression. -/
lemma eval_selectedCellExpression {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    eval (hybridCountVector sample) (selectedCellExpression n k) =
      if k ∈ heavyCells sample then empiricalRatioCell sample k
      else factorialPolynomialContribution sample k := by
  by_cases hn : n < calibrationCutoff
  · simp [selectedCellExpression, heavyCells, hn, eval_heavyCellExpression]
  · simp only [selectedCellExpression, hn, ↓reduceIte, eval,
      eval_categoryCountExpression, eval_lightCellExpression,
      eval_heavyCellExpression, heavyCells, Finset.mem_filter, Finset.mem_univ,
      true_and]
    by_cases hk : (lambda0 : ℝ) * logScale n < splitCategoryCount sample 0 k
    · rw [if_neg, if_pos hk]
      linarith
    · rw [if_pos, if_neg hk]
      linarith

/-- Establishes the stated upper bound for polynomial Degree two le. -/
lemma polynomialDegree_two_le (n : ℕ) : 2 ≤ polynomialDegree n := by
  simp [polynomialDegree]

/-- Establishes the stated upper bound for operation Count selected Cell Expression le. -/
lemma operationCount_selectedCellExpression_le (n : ℕ) {d : ℕ} (k : Fin d) :
    operationCount (selectedCellExpression n k) ≤ 110 * polynomialDegree n ^ 4 := by
  have hM := polynomialDegree_two_le n
  have hMpow : 16 ≤ polynomialDegree n ^ 4 := by
    norm_num [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact Nat.pow_le_pow_left hM 4
  by_cases hn : n < calibrationCutoff
  · simp [selectedCellExpression, hn, operationCount_heavyCellExpression]
    omega
  · simp only [selectedCellExpression, hn, ↓reduceIte, operationCount,
      operationCount_heavyCellExpression]
    have hlight := operationCount_lightCellExpression_le k hM
    have hcat : operationCount (categoryCountExpression 0 k) = 4 := by
      simp [categoryCountExpression, operationCount, hybridCellList,
        operationCount_splitCountExpression]
    rw [hcat]
    omega

/-- Defines untruncated Hybrid Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def untruncatedHybridExpression (n d : ℕ) :
    RealArithmeticExpression (HybridCountInput d) :=
  expressionSum (List.ofFn fun k : Fin d => selectedCellExpression n k)

/-- Defines clamp Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def clampExpression {ι : Type*} (x : RealArithmeticExpression ι) :
    RealArithmeticExpression ι :=
  let minOne := .branchNonpos (.sub (.const 1) x) (.const 1) x
  .branchNonpos (.add minOne (.const 1)) (.const (-1)) minOne

/-- Defines hybrid Expression, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def hybridExpression (n d : ℕ) : RealArithmeticExpression (HybridCountInput d) :=
  clampExpression (untruncatedHybridExpression n d)

/-- Establishes the stated equality relating heavy add light eq selected sum. -/
lemma heavy_add_light_eq_selected_sum {n d : ℕ} (sample : Fin n → Obs d) :
    heavyContribution sample + lightContribution sample =
      ∑ k : Fin d, if k ∈ heavyCells sample then empiricalRatioCell sample k
        else factorialPolynomialContribution sample k := by
  classical
  rw [heavyContribution, lightContribution, lightCells_eq_compl, Finset.sum_ite]
  have hheavy : Finset.univ.filter (fun k => k ∈ heavyCells sample) =
      heavyCells sample := by
    ext k
    simp
  have hlight : Finset.univ.filter (fun k => k ∉ heavyCells sample) =
      (heavyCells sample)ᶜ := by
    ext k
    simp
  rw [hheavy, hlight]

/-- Establishes the stated property of eval untruncated Hybrid Expression in the discrete average-treatment-effect construction. -/
lemma eval_untruncatedHybridExpression {n d : ℕ} (sample : Fin n → Obs d) :
    eval (hybridCountVector sample) (untruncatedHybridExpression n d) =
      heavyContribution sample + lightContribution sample := by
  simp only [untruncatedHybridExpression, eval_expressionSum]
  rw [← List.ofFn_comp']
  rw [List.sum_ofFn]
  simp only [eval_selectedCellExpression]
  rw [heavy_add_light_eq_selected_sum]

/-- Establishes the stated property of eval clamp Expression in the discrete average-treatment-effect construction. -/
lemma eval_clampExpression {ι : Type*} (input : ι → ℝ)
    (x : RealArithmeticExpression ι) :
    eval input (clampExpression x) = max (-1) (min 1 (eval input x)) := by
  simp only [clampExpression, eval]
  let m : ℝ := if 1 - eval input x ≤ 0 then 1 else eval input x
  have hm : m = min 1 (eval input x) := by
    dsimp [m]
    by_cases h : 1 - eval input x ≤ 0
    · rw [if_pos h, min_eq_left (by linarith)]
    · rw [if_neg h, min_eq_right (by linarith)]
  change (if m + 1 ≤ 0 then -1 else m) = _
  rw [hm]
  by_cases h : min 1 (eval input x) ≤ -1
  · rw [if_pos (by linarith), max_eq_left h]
  · rw [if_neg (by linarith), max_eq_right (le_of_not_ge h)]

/-- Establishes the stated property of eval hybrid Expression in the discrete average-treatment-effect construction. -/
lemma eval_hybridExpression {n d : ℕ} (sample : Fin n → Obs d) :
    eval (hybridCountVector sample) (hybridExpression n d) = hybridEstimator sample := by
  simp [hybridExpression, eval_clampExpression, eval_untruncatedHybridExpression,
    hybridEstimator]

/-- Establishes the stated upper bound for operation Count untruncated Hybrid Expression le. -/
lemma operationCount_untruncatedHybridExpression_le (n d : ℕ) :
    operationCount (untruncatedHybridExpression n d) ≤
      111 * d * polynomialDegree n ^ 4 := by
  rw [untruncatedHybridExpression, operationCount_expressionSum]
  rw [← List.ofFn_comp']
  rw [List.sum_ofFn, List.length_ofFn]
  have hsum : (∑ k : Fin d, operationCount (selectedCellExpression n k)) ≤
      ∑ _k : Fin d, 110 * polynomialDegree n ^ 4 := by
    apply Finset.sum_le_sum
    intro k hk
    exact operationCount_selectedCellExpression_le n k
  calc
    (∑ k : Fin d, operationCount (selectedCellExpression n k)) + d
        ≤ (∑ _k : Fin d, 110 * polynomialDegree n ^ 4) + d :=
          Nat.add_le_add_right hsum d
    _ = d * (110 * polynomialDegree n ^ 4) + d := by simp
    _ ≤ 111 * d * polynomialDegree n ^ 4 := by
      have hM : 1 ≤ polynomialDegree n ^ 4 := by
        exact one_le_pow₀ (le_trans (by omega) (polynomialDegree_two_le n))
      nlinarith

/-- Establishes the stated property of operation Count clamp Expression in the discrete average-treatment-effect construction. -/
lemma operationCount_clampExpression {ι : Type*} (x : RealArithmeticExpression ι) :
    operationCount (clampExpression x) = 4 * operationCount x + 6 := by
  simp [clampExpression, operationCount]
  omega

/-- Establishes the stated upper bound for operation Count hybrid Expression le. -/
lemma operationCount_hybridExpression_le (n d : ℕ) (hd : 0 < d) :
    operationCount (hybridExpression n d) ≤ 450 * d * polynomialDegree n ^ 4 := by
  rw [hybridExpression, operationCount_clampExpression]
  have hu := operationCount_untruncatedHybridExpression_le n d
  have hM : 1 ≤ polynomialDegree n ^ 4 := by
    exact one_le_pow₀ (le_trans (by omega) (polynomialDegree_two_le n))
  have hdM : 1 ≤ d * polynomialDegree n ^ 4 := by
    exact Nat.mul_pos hd (lt_of_lt_of_le Nat.zero_lt_one hM)
  nlinarith

/-- The requested straight-line program.  The zero-alphabet branch is a
zero-cost constant; otherwise it is the verified compilation of the exact
count expression above. -/
noncomputable def hybridArithmeticProgram (n d : ℕ) :
    RealArithmeticProgram (HybridCountInput d) :=
  if d = 0 then RealArithmeticExpression.program (.const 0)
  else RealArithmeticExpression.program (hybridExpression n d)

lemma hybridArithmeticProgram_eval {n d : ℕ} (sample : Fin n → Obs d) :
    (hybridArithmeticProgram n d).eval (hybridCountVector sample) =
      hybridEstimator sample := by
  by_cases hd : d = 0
  · subst d
    have hfinset (s : Finset (Fin 0)) : s = ∅ := by
      ext i
      exact Fin.elim0 i
    simp [hybridArithmeticProgram, RealArithmeticExpression.eval_program,
      RealArithmeticExpression.eval, hybridEstimator, heavyContribution,
      lightContribution, hfinset]
  · simp [hybridArithmeticProgram, hd, RealArithmeticExpression.eval_program,
      eval_hybridExpression]

/-- Establishes the stated property of hybrid Arithmetic Program operation Count in the discrete average-treatment-effect construction. -/
lemma hybridArithmeticProgram_operationCount (n d : ℕ) :
    (hybridArithmeticProgram n d).operationCount ≤
      450 * d * polynomialDegree n ^ 4 := by
  by_cases hd : d = 0
  · subst d
    simp [hybridArithmeticProgram, RealArithmeticExpression.operationCount_program,
      RealArithmeticExpression.operationCount]
  · rw [hybridArithmeticProgram, if_neg hd,
      RealArithmeticExpression.operationCount_program]
    exact operationCount_hybridExpression_le n d (Nat.pos_of_ne_zero hd)

/-- Exact computability and the uniform `O(d M(n)^4)` operation certificate. -/
theorem hybridEstimatorComputable : HybridEstimatorComputable := by
  refine ⟨450, by norm_num, ?_⟩
  intro n d
  exact ⟨hybridArithmeticProgram n d, hybridArithmeticProgram_operationCount n d,
    fun sample => hybridArithmeticProgram_eval sample⟩

end CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- Compiling an input expression at a given register offset produces the one-instruction program
that reads that input into the next register. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.RealArithmeticExpression.codeAt.eq_def

/-- Evaluating an input expression returns the real number assigned to that input. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.RealArithmeticExpression.eval.eq_def

/-- An input or constant expression tree contains exactly one node. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.RealArithmeticExpression.nodeCount.eq_def

/-- An input or constant expression tree requires no arithmetic operations. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.RealArithmeticExpression.operationCount.eq_def

/-- The product expression for an empty list is the constant one, and for a nonempty list it
multiplies the first expression by the product expression for the remaining list. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.expressionProduct.eq_def

/-- The sum expression for an empty list is the constant zero, and for a nonempty list it adds
the first expression to the sum expression for the remaining list. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.expressionSum.eq_def

/-- The zero-order falling-factorial expression is one; each higher order multiplies the previous
one by the input expression minus the preceding integer. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.fallingExpression.eq_def
