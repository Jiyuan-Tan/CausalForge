# Substrate requirement: fano_inequality

## Goal
Build the classical Fano inequality: relate the conditional Shannon entropy of a
finite random variable to the probability of incorrectly estimating it.

## Provides (API contract)
Over finite types (`Fintype`), reusing the existing entropy core
`Causalean.Mathlib.InformationTheory.entropy` (`= ∑ i, Real.negMulLog (p i)`):
- `condEntropy (p : α × β → ℝ) : ℝ` — conditional Shannon entropy `H(X ∣ Y)` of a
  joint pmf `p` on `α × β`, defined via the chain rule `H(X ∣ Y) = H(X,Y) − H(Y)`
  (i.e. `entropy p − entropy (yMarginal p)`, where `yMarginal p y = ∑ x, p (x,y)`).
- `fano_inequality` — for a joint pmf `p` on `α × β` with `2 ≤ Fintype.card α`, and
  error probability `Pe := ∑ (x,y) with x ≠ decode y, p (x,y)` (for a decoder
  `decode : β → α`), the bound
      `condEntropy p ≤ Real.binEntropy Pe + Pe * Real.log (Fintype.card α - 1)`.
  (Cover–Thomas Thm 2.10.1; `Real.binEntropy` is the Mathlib binary entropy.)
- `fano_error_lower_bound` — the standard weakened corollary giving a usable lower
  bound on `Pe`:  `Pe ≥ (condEntropy p − Real.log 2) / Real.log (Fintype.card α)`
  (from `binEntropy Pe ≤ log 2` and `log (card α − 1) ≤ log (card α)`).

## Statement / milestones
1. `yMarginal p y := ∑ x, p (x, y)`; `condEntropy p := entropy p − entropy (yMarginal p)`.
2. Supporting facts (reuse `entropy`/`entropy_le_log_card` from the entropy core):
   the "conditioning ≤ unconditioned within a block" / max-entropy-per-block bound
   `H(X ∣ E, X̂) ≤ Pe · log (card α − 1)` and `H(E ∣ X̂) ≤ H_b(Pe)`.
3. `fano_inequality` via the standard indicator/chain-rule argument: let
   `E = 𝟙{X ≠ decode Y}`. Chain rule both ways on `H(E, X ∣ X̂)`:
   `H(X ∣ X̂) + H(E ∣ X, X̂) = H(E ∣ X̂) + H(X ∣ E, X̂)`. Since `E` is a function of
   `(X, X̂)`, `H(E ∣ X, X̂) = 0`; then `H(E ∣ X̂) ≤ H_b(Pe)` and
   `H(X ∣ E, X̂) ≤ Pe · log(card α − 1)` (max entropy on the error block, which has
   ≤ `card α − 1` candidates; the correct-block conditional entropy is 0).
4. `fano_error_lower_bound`: rearrange `fano_inequality` using `binEntropy ≤ log 2`.

(The milestones above sketch ONE proof route — the textbook chain-rule/indicator
argument — and are NOT mandatory. The deliverable is the Fano THEOREM and its
corollary (plus clean reusable defs), NOT any particular proof structure. ANY sound,
sorry-free proof of the headline statements that reuses the entropy core is fully
acceptable — in particular the single reference-distribution Gibbs / cross-entropy
argument (choose a reference law that puts `1−Pe` on the decoded symbol and `Pe`
spread over the other `card α − 1` symbols), which yields the IDENTICAL sharp bound
with strictly less machinery, is a correct and preferred encoding. The exact Lean
encoding and the decoder (`decode : β → α`, the standard textbook setting) are the
scaffolder's call.)

## Standard reference
Cover & Thomas, *Elements of Information Theory* (2e), §2.10, Theorem 2.10.1 (Fano's
inequality) and its proof (the indicator-variable + chain-rule argument). FETCH and
read this proof to get the exact statement, hypotheses, and the `card α − 1` term
right (the `−1` is the crux that distinguishes Fano from a trivial bound).

## Intended reuse
The converse engine for minimax lower bounds over finite/discrete parameter sets
(the multi-hypothesis testing lower bound): given a packing of `M` hypotheses, Fano
turns a mutual-information / conditional-entropy bound into a lower bound on the
minimax error. Complements the existing two-point/Le Cam tools in
`Causalean/Stat/Minimax/`. Must be generic over arbitrary finite `α`, `β`.

## May assume / must derive
- MAY assume: `p` is a pmf (`0 ≤ p`, `∑ = 1`); `2 ≤ Fintype.card α`; the decoder is a
  given `decode : β → α`.
- MUST derive (no `sorry`, no assumed Fano gate): `condEntropy` from the entropy core,
  and the headline `fano_inequality` (with the genuine `card α − 1` term) plus
  `fano_error_lower_bound`, proven from first principles together with the entropy core
  — using whatever intermediate lemmas the chosen proof route needs. Do NOT assume Fano,
  the chain rule, or the `card−1` bound as a black-box hypothesis. The proof route itself
  (chain-rule vs. reference-distribution Gibbs vs. other) is NOT prescribed.

## Non-goals
- No continuous/differential entropy; no general mutual-information theory beyond what
  the proof needs; no minimax application here (that is a downstream consumer).
- Do NOT re-prove `binEntropy ≤ log 2` — Mathlib has `Real.binEntropy_le_log_two`.
- Do NOT re-prove the unconditional entropy core — import it.

## Known building blocks
- `Causalean.Mathlib.InformationTheory.entropy`, `entropy_nonneg`, `entropy_le_log_card`,
  `entropy_const_eq_log_card` (the just-built entropy core — import it).
- `Real.negMulLog`, `Real.negMulLog_nonneg`, `Real.log_le_sub_one_of_pos`.
- `Real.binEntropy`, `Real.binEntropy_le_log_two`, `Real.binEntropy_nonneg` (Mathlib).
- `Finset.sum_*` (`sum_le_sum`, `sum_sub_distrib`, `sum_product`, `Fintype.sum_prod_type`),
  `Fintype.card`.

## Target module (optional)
Causalean.Mathlib.InformationTheory.Fano
