## Done

- Round 3 ground truth: direct `lake env lean` on `Saddle.lean` and the targeted Lake build both succeed; source grep finds no `sorry`, `admit`, `native_decide`, or declared axiom.
- Axiom audit: all three saddle-layer theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- `Core.lean`: procedure/risk API, feasibility, compactness, convexity, continuity, risk-image compactness, and Causalean API bridges are proved.
- `Mixing.lean`: conditional mixing/Jensen, convex-hull recovery, and compactness of the convex risk hull are proved.
- `Saddle.lean`: Sion saddle attainment, equality with `minimaxValue`, and `finite_bounded_squared_loss_has_saddle` are proved.
- Causalean library search and Sion (1958), Theorem 3.4 were rechecked.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Retain the general hypotheses: no normalization of `P`, observation nonemptiness, or target bounds are required.
- Continue using Causalean's `FiniteDesign`, `FiniteDesign.E`, and `minimaxValue`; `Procedure` only packages the requested design/rule pair.
- The verified tree is review-ready, so no filler subagents are needed.