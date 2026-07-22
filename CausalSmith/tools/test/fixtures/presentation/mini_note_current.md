# NL Formalization — fixture (current causalsmith F1 dialect)

## 0. Lean-feasibility verdict

`formalizable-now`.

## 4. P-block (definitions / structures — all build-inline, typed)

**P-1 (Observable law).** A probability space and maps `Y : Ω → ℝ` with `0 ≤ Y ≤ 1`.
Build-inline definitional object.

**P-2 (Overlap tail).** `PolyTail P U κ t₀`, requiring `0 < κ`. A definitional setup
object referenced by hypotheses but presented only in prose (no Lean anchor).

## 5. L-block (lemmas / helpers)

**L-1 (Oracle mean decomposition).** *(helper)*
- **Hypotheses.** P-1, P-2.
- **Conclusion.** `𝔼[ψ] = τ + B(λ)`.

## 6. T-block (theorem-level statements)

### T-block: t1 — Corrected upper bound

**Statement.** Under A1–A2, the corrected estimator's risk obeys `O(n^{-(1+κ)/(2+κ)})`.

**Load-bearing hypotheses.**
- H1 (A1 Identification, `.tex` ≈ 10–20, P-1): P-1 with consistency.
- H2 (A2 Overlap tail, `.tex` ≈ 21–30, P-2): P-2 with `0 < κ`.

**Conclusion (typed).** `Risk(estimator) ≤ C * n^{-(1+κ)/(2+κ)}`.

**Intuition.** Margin localization plus overlap control.
