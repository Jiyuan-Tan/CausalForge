## Done
- Promoted the zero-sorry theorem tree to `Causalean/Stat/Concentration/VarianceAdaptiveVCExpectedMaximal/` with umbrella module and imports from `Causalean.Stat.Concentration` and `Causalean.lean`.
- Verified `import Causalean` resolves `varianceAdaptiveExpectedMaximal_le` and its `HasPolynomialL2Cover` wrapper.
- Reworked `vcEntropy_chaining_bound` to apply the promoted primitive; it is now proved and `VCExpectedMaximal.lean` builds against it.
- `lake build Causalean` and targeted CausalSmith builds succeed. Promoted sources contain no `sorry`, `admit`, `native_decide`, new axiom, or research import.
- `#print axioms` for the Rademacher and expected-maximal theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Regenerated library index/API docs/headline metadata and both embedding views; `doc:check` and `lint:embeddings` pass. Search now returns the promoted theorem as the top result.
- Rechecked arXiv:1212.6885 TeX: the VC-type corollary uses `A ≥ e`, `v ≥ 1`, a σ-leading term, and the envelope second-order term.

## Remaining
- No proof obligations remain in the promoted substrate or `vcEntropy_chaining_bound`.
- Pre-existing paper-local sorries remain in `EntropyChaining.lean` (`winsorizedScore_hasVCUniformEntropy`), `Separability.lean`, and `WinsorizedScoreMaximal.lean`; they are downstream score/separability work, not part of the requested promotion/adapter fix.

## Blocked
- None.

## Decisions
- Preserve the countable-index API, `log (max e (A U / σ))` normalization, and constant 16384.
- Strengthen the paper-local entropy bundle to carry the canonical normalizations, measurability, population L² radius, and enumeration-level empirical-cover data required by the genuine promoted theorem; the former single-population-measure cover was insufficient for empirical chaining.
- Keep the tightly coupled localization/chaining proof together despite its size; splitting can follow separately without changing the public API.
- No filler subagents are needed because the promoted module and requested adapter are fully proved and verified.