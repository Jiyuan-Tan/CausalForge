# Substrate requirement: finite_entropy_core

## Goal
Build the finite-alphabet Shannon entropy of a probability mass function and its
maximum-entropy bound `H(p) ≤ log (card α)` — the entropy layer Mathlib lacks.

## Provides (API contract)
A single module exposing, over a `Fintype α`:
- `entropy (p : α → ℝ) : ℝ` — Shannon entropy in nats, `∑ i, Real.negMulLog (p i)`.
  (Define on any real-valued `p`; the pmf hypotheses enter the lemmas, not the def.)
- `entropy_nonneg : (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) → 0 ≤ entropy p`.
- `entropy_le_log_card : [Nonempty α] → (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
    entropy p ≤ Real.log (Fintype.card α)`  — the maximum-entropy (Gibbs) bound; the headline.
- `entropy_const_eq_log_card : [Nonempty α] →
    entropy (fun _ => (Fintype.card α : ℝ)⁻¹) = Real.log (Fintype.card α)`
    — the uniform pmf attains the bound (witnesses non-vacuity / sharpness).

## Statement / milestones
1. Definition `entropy p := ∑ i, Real.negMulLog (p i)` over `Fintype α`.
2. `entropy_nonneg`: each summand `negMulLog (p i) ≥ 0` when `0 ≤ p i ≤ 1`
   (`Real.negMulLog_nonneg`), so the finite sum is `≥ 0`.
3. `entropy_le_log_card` (maximum entropy): for a pmf `p` on a nonempty finite α
   with `n = Fintype.card α`, `entropy p ≤ log n`. Elementary Gibbs route via
   `log x ≤ x − 1`: on the support, `p_i · log (1 / (n · p_i)) ≤ p_i · (1/(n p_i) − 1)
   = 1/n − p_i`; sum over α (zero terms contribute 0) to get `entropy p − log n ≤ 0`.
4. `entropy_const_eq_log_card`: substitute `p_i = 1/n`; `negMulLog (1/n) = (1/n) log n`,
   summed `n` times gives `log n`. Confirms the bound is tight (sharp), not vacuous.

## Standard reference
Cover & Thomas, *Elements of Information Theory* (2e), §2.1 (entropy), Thm 2.6.4
(maximum entropy of a distribution on a finite alphabet, `H ≤ log |𝒳|`, equality iff
uniform). Standard textbook material; `H(p) ≤ log n` is the canonical statement.

## Intended reuse
The prerequisite layer for Fano's inequality (the multi-hypothesis minimax lower
bound), which is itself a planned follow-up `--study` run consuming this module:
Fano upper-bounds the error entropy by `log 2` and the prior entropy by `log M`
over `M` uniform hypotheses. More broadly, any information-theoretic argument
(max-entropy priors, mutual-information bounds, capacity arguments) needs this
finite-entropy core. Must be stated generically over an arbitrary `Fintype α`,
NOT specialized to `Fin M`, `Bool`, or any caller's index type.

## May assume / must derive
- MAY assume (as lemma hypotheses, fair to take as given): `p` is a pmf — pointwise
  `0 ≤ p i` and `∑ i, p i = 1`; `Nonempty α` where the count `log (card α)` is used.
- MUST derive (do NOT assume as a gate, do NOT take Gibbs/Jensen as a black box):
  `entropy_le_log_card` itself — prove it from Mathlib's `Real.log_le_sub_one_of_pos`
  (or log concavity), not by citing an unproven max-entropy axiom. No `sorry`.

## Non-goals
- Do NOT re-prove the binary-entropy maximum `binEntropy p ≤ log 2`; Mathlib already
  has `Real.binEntropy_le_log_two`. (Fano will cite it directly.)
- No KL divergence / relative entropy module, no mutual information, no Fano here —
  those are separate follow-ups. This run delivers ONLY the finite-entropy core.
- No continuous/differential entropy.

## Known building blocks
- `Real.negMulLog` (`= fun x => -x * log x`), `Real.negMulLog_nonneg` (`0≤x→x≤1→0≤negMulLog x`),
  `Real.negMulLog_def`.
- `Real.log_le_sub_one_of_pos : 0 < x → log x ≤ x - 1` — the elementary Gibbs lever.
- `Finset.sum_le_sum`, `Finset.sum_div`, `Fintype.card` / `Finset.card_univ`.
- For the equality case: `Real.log_inv`, basic `Finset.sum_const`.
