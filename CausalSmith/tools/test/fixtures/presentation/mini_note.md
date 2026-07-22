## 4. P-block

### P-1. Observable law and measurable structure.
- **Signature.** A probability space `(Ω, mΩ, P)`, maps `Y : Ω → ℝ`.
- **Conditions.** `0 ≤ Y ≤ 1` a.s.
- **Reuse.** `AutoID.Stat.WeakOverlap.OverlapSetup`.

### P-2. One-sided polynomial overlap tail.
- **Signature.** `PolyTail P U κ t₀ c_- c_+`.
- **Conditions.** `0 < κ`.

## 5. L-block

### L-1. Oracle mean decomposition.
- **Hypotheses.** P-1, P-2.
- **Conclusion.** `𝔼[ψ] = τ + B(λ)`.
- **.tex line range.** Section "Upper bound".

## 6. T-block

### T-1. Corrected upper bound.

#### Load-bearing hypotheses.
- **H1 (A1 Identification).** P-1 with consistency.
- **H2 (A2 Overlap tail).** P-2 with `0 < κ`.

#### Conclusion.
- Risk of the estimator is `O(n^{-(1+κ)/(2+κ)})`.
