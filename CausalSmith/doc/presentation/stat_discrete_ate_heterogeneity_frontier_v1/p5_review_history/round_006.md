# Referee review

**Recommendation:** major_revision
**Overall score:** 6.5/10 — The verified mathematical contribution is substantial, but the manuscript needs significant prose, scope, and presentation repair before it reads as a publishable econometrics submission.

The paper establishes a finite-sample minimax bracket for scalar ATE estimation with finite discrete adjustment, real outcomes, fixed overlap, known outcome scale, and a known heterogeneity radius. The main contribution is a constructive selector combining polynomial and collision estimators with lower benchmarks transported from binary source experiments. The results are credible under the provided verification contract, but the manuscript overstates or awkwardly frames some scope claims and is difficult to read as a journal article because much of the formal artifact is copied into the paper.

## Strengths
- The main upper and lower benchmarks are stated for the same real-outcome model class and the same clipped-estimator risk criterion.
- The radius-indexed formulation cleanly connects exact homogeneity, unrestricted heterogeneity, and intermediate fixed-radius regimes.
- The paper engages the closest discrete-adjustment competitor and gives explicit rate comparisons.
- The verification note and crosswalk discipline make the formal scope unusually transparent.

## Findings
- **[major·prose] Introduction** — The paragraph beginning "It is worth being precise about what is and is not delivered" violates the affirmative contribution framing contract outside a titled Limitations, Future Work, or Open Questions section, especially: "What is not delivered is a rate valid uniformly in \(\sigma\)" and "its minimax rate is left open."
  - *Fix:* Move the genuine non-coverage material to the existing Limitations or Future Work subsection, and rewrite the introduction affirmatively: state that the paper provides an all-parameter bracket and exact-order rates in the endpoint, fixed-positive-radius, saturation, and elbow regimes, with the residual shrinking-radius frontier identified by the regime theorem.
- **[major·prose] Introduction** — The sentence "this paper determines the minimax rate for discrete-adjustment ATE estimation everywhere except in an explicitly delimited shrinking-radius wedge" is stronger than the verified global statement as written. The verified results provide exact-order equivalence in named regimes and show that benchmark divergence implies membership in the residual wedge; they do not by themselves present a complete pointwise partition theorem proving exact minimax rates for every point outside a geometrically defined wedge.
  - *Fix:* Replace the sentence with a precise statement tied to the theorem: "The bracket gives exact-order rates at the endpoints, fixed positive radii, saturation, and the stated parametric-dominance elbows; any divergence of the displayed upper-to-lower benchmark ratio is confined to the residual shrinking-radius wedge characterized in \cref{obj:thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d}."
- **[major·prose] Verification note** — The sentence "The auxiliary comparison in \cref{obj:thm:published-binary-collision-comparison} is machine-checked conditionally on the published binary collision guarantee" is partly stale or ambiguous relative to the current contract: the theorem itself is unconditional except for the explicit hypothesis `ZengBinaryCollisionUpper epsilon`, and the surrounding source lemmas are discharged checked declarations rather than maintained assumptions.
  - *Fix:* Update the note to distinguish the discharged binary source lemmas from the theorem-local assumption in the published-collision comparison. For example: "The binary source lemmas displayed above are checked declarations in this artifact, with citations supplying attribution and statistical context. The separate comparison proposition is checked as a conditional implication from the published binary collision guarantee displayed in its statement."
- **[major·structure] Proofs and appendices** — The paper includes extremely long proof scripts and implementation-level formal derivations in the main submission, making the manuscript hard to evaluate as an econometrics article. The appendix reads more like a formal artifact dump than a mathematical exposition.
  - *Fix:* Move routine proof-audit details, low-level constants, and Lean-oriented derivation traces to a supplemental verification appendix or artifact. Keep in the paper the definitions, theorem statements, proof sketches, key reductions, and enough detail for a statistical reader to understand the mechanisms.
- **[minor·structure] Setup and assumptions** — Benchmark notation is introduced twice: first in a table after the minimax risk definition and then again in the paragraph titled "Benchmark notation, once and for all." This creates avoidable redundancy and increases the risk of notation drift.
  - *Fix:* Keep one benchmark-notation block, preferably the table plus a short explanatory paragraph, and remove the duplicate definitions.
- **[minor·prose] global** — Several displayed statements in the manuscript use `\nu_{n,d}` in the verification-contract rendering where the manuscript uses `u_{n,d}`. Even if this is extraction noise, a reader-facing manuscript must keep one symbol for the polynomial benchmark.
  - *Fix:* Audit the source and generated crosswalk so every reader-facing occurrence uses `u_{n,d}` for the polynomial remainder, and reserve Greek nu only if it denotes a distinct object.
- **[minor·structure] Discussion and limitations** — The subsection title "Binary collision comparison" sits under "Discussion and limitations" even though it is a substantive positioning result against the nearest competitor. This buries an important comparison late in the paper.
  - *Fix:* Move the binary collision comparison into the related-work section or a dedicated early comparison subsection, while leaving genuine limitations and future-work material in the closing section.
- **[minor·other] Estimators and upper bounds** — The polynomial estimator is described mathematically, but the practical estimator depends on known \(M\), known \(\sigma\), a calibration handle, clipping, and a heavy-light split. The computational paragraph is helpful but still does not give enough implementation-level pseudocode for empirical reproducibility.
  - *Fix:* Add a compact pseudocode block or implementation note specifying inputs, outputs, fallback branches, and how the falling-factorial terms are computed from aggregated counts.
- **[nit·prose] abstract** — The first use of \(\epsilon\) appears as "fixed overlap parameter \(\epsilon\)" and the first use of \(d\) appears as "alphabet size \(d\), the number of adjustment cells," which satisfies the gloss requirement. The first use of \(M\) is also clear, but the phrase "known outcome scale \(M\)" would be clearer before "interval of radius \(M/2\)."
  - *Fix:* Change the abstract phrase to "the known outcome scale \(M\), with conditional means in an interval of radius \(M/2\)."

## Questions for authors
- Can the paper give a concise non-formal proof roadmap for the polynomial estimator that explains why the real-outcome second-moment condition suffices?
- Is the known-radius assumption intended as a practical estimator input or primarily as a minimax oracle benchmark?
- Will the journal submission include the Lean artifact and crosswalk as supplementary material rather than as long in-paper proof text?

