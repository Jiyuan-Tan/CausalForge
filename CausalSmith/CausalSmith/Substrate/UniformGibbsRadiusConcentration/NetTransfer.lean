import Mathlib.Analysis.RCLike.Basic

/-!
# Exact transfer from a finite net

Relative comparisons on net points transfer to the full class with exactly
three times the population/empirical approximation error.
-/

namespace CausalSmith.Substrate

/-- A two-sided relative comparison transfers across simultaneous population
and empirical perturbations of size `eps`, costing exactly `3*eps`. -/
theorem relative_comparison_transfer
    {p q pn qn remainder eps : ℝ}
    (hpop : |p - q| ≤ eps) (hemp : |pn - qn| ≤ eps)
    (hforward : q ≤ 2 * qn + remainder)
    (hreverse : qn ≤ 2 * q + remainder) :
    p ≤ 2 * pn + remainder + 3 * eps ∧
    pn ≤ 2 * p + remainder + 3 * eps := by
  rw [abs_le] at hpop hemp
  constructor <;> linarith

/-- If every member of a class has a net representative whose population and
empirical values are each within `eps`, simultaneous relative comparisons on
the net transfer to the whole class with remainder enlarged by `3*eps`. -/
theorem relative_comparison_transfer_of_net
    {K Q : Type*} (A : Set K) (N : Finset Q)
    (pop emp : K → ℝ) (netPop netEmp : Q → ℝ)
    (remainder eps : ℝ)
    (hnet : ∀ k ∈ A, ∃ q ∈ N,
      |pop k - netPop q| ≤ eps ∧ |emp k - netEmp q| ≤ eps)
    (hgood : ∀ q ∈ N,
      netPop q ≤ 2 * netEmp q + remainder ∧
      netEmp q ≤ 2 * netPop q + remainder) :
    ∀ k ∈ A,
      pop k ≤ 2 * emp k + remainder + 3 * eps ∧
      emp k ≤ 2 * pop k + remainder + 3 * eps := by
  intro k hk
  obtain ⟨q, hq, hpop, hemp⟩ := hnet k hk
  exact relative_comparison_transfer hpop hemp
    (hgood q hq).1 (hgood q hq).2

end CausalSmith.Substrate
