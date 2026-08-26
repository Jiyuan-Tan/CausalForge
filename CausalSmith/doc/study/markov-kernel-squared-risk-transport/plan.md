## Done

- `Core.lean`: all boundedness, kernel mean, affine pullback, tower, conditional/integrated Jensen, risk comparison, and quantified hardness declarations are proved.
- `FiniteProduct.lean`: `finProductKernel`, its fibre and product-channel laws, product risk comparison, and quantified theorem (including `n = 0`) are proved.
- The umbrella module exports both layers; imports stay within Mathlib, Causalean, and this substrate tree.
- Re-ran Causalean retrieval searches and checked [Blackwell's 1951 primary paper](https://digicoll.lib.berkeley.edu/record/112749) for the garbling/risk-order convention.
- Directly checked all three Lean sources and ran `lake build CausalSmith.Substrate.MarkovKernelSquaredRiskTransport`; all pass.
- Lean-source scans contain no `sorry`, `admit`, `native_decide`, custom `axiom`, paper/research import, or forbidden paper-local concept.
- `#print axioms` for every theorem/instance reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None; ready for review.

## Blocked

- None.

## Decisions

- Use `K ∘ₘ P` as Mathlib's standard measure–kernel composition notation.
- `UniformlyBounded` stores a nonnegative absolute bound; source admissibility is proved for the constructed pullback rather than assumed.
- Define a genuine independent `Fin n` kernel via binary parallel composition and measurable `Fin`-product equivalences; do not restrict source spaces to countable types.
- Keep core and product proofs separate, with the product layer importing completed core.
- No filler subagents are needed because ground truth has zero open proofs.