## Done
- `PartialMatching.lean`: finite partial matchings, size/merged-index facts, fixed-size family, cardinality `choose r h * choose s h * h!`, and size partition are proved; added the missing public-instance docstring.
- `Statistic.lean`: normalized finite-coordinate and ordered-product statistics, injective-tuple count, `uStatisticOrder` compatibility, and unbiasedness are proved.
- `Expansion.lean`: unequal-order pointwise product expansion, merged product-law moment identity, and covariance expansion with the `h = 0` correction explicit are proved.
- `Bounds.lean`: `factorialMatchingRatio_le`, `matchingNormalization_le`, `factorialDisjointCorrection_le`, and `emptyMatchingNormalization_sub_one_le` are proved with the required symmetric hypotheses.
- Ground-truth verification completed: all five source files pass Lean diagnostics and direct checking; the umbrella target builds; source grep finds no `sorry`, `admit`, `native_decide`, custom axiom, forbidden research import, paper theorem, or `6^(2*K)` conclusion.
- Axiom audit of the headline declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Retain the generic merged-kernel integrability interface: it directly accommodates indicator labels and an L2 mark without importing paper-specific assumptions; the optional selector specialization is unnecessary for the four required APIs.
- Keep the symmetric bounds under only `r,s ≤ R`, `4 * R^2 ≤ n`, and the matching-size condition.
- Library search confirmed reuse of `Nat.pow_sub_le_descFactorial`, `Nat.descFactorial_le_pow`, `Nat.descFactorial_mul_descFactorial`, and `Fintype.card_equiv`; no existing unequal-order covariance expansion was found.
- Hoeffding’s 1948 primary journal record and bibliographic/full-text endpoints were checked; accessible metadata confirms the canonical U-statistic source, while the original full text remained access-limited.