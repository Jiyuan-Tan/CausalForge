## Done

- `PartialMatching.lean`: partial-matching representation, fixed-size cardinality, size bounds, and size partition are proved; source is hole-free.
- `Statistic.lean`: finite injective-tuple count, `uStatisticOrder` compatibility, and unbiasedness are proved; source is hole-free.
- `Expansion.lean`: unequal-order pointwise product expansion, merged product-law moments, and the centered identity with the empty matching exposed are proved; source is hole-free.
- The umbrella and `Bounds.lean` type-check; the umbrella build succeeds with exactly the four expected `Bounds.lean` sorry warnings.
- Searched Causalean and Mathlib: no existing mixed-order bound was found; relevant reusable lemmas include `Nat.pow_sub_le_descFactorial`, `Nat.descFactorial_le_pow`, `one_add_mul_le_pow`, and `Real.log_le_sub_one_of_pos`. [Hoeffding (1948)'s primary journal record](https://www.jstor.org/stable/2235637) was checked; the full Project Euclid text was access-blocked.

## Remaining

- `Bounds.lean`: prove `factorialMatchingRatio_le` and its wrapper `matchingNormalization_le`.
- `Bounds.lean`: prove `factorialDisjointCorrection_le` and its wrapper `emptyMatchingNormalization_sub_one_le`.

## Blocked

- None.

## Decisions

- Keep partial matchings as equivalences between selected finite subsets and keep the generic finite-index statistic for merged coordinate types.
- Preserve the genuine symmetric API with only `r,s ≤ R`, `4 * R^2 ≤ n`, and the matching-size condition; do not add an order comparison or paper-specific assumptions.
- Neutralize the sibling `factorial_ratio_bound` / `factorial_cross_ratio_bound` arguments locally by ordering `r,s` inside each proof and enlarging the resulting maximum-order bound to `R`; never import the research module.
- Use one filler because all four holes are in the same coupled file/import closure; the two wrapper proofs should follow only after their respective core inequality.
