# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The paper delivers a substantial and technically credible minimax bracket, with strong claim fidelity overall, but needs targeted prose, scope, and reproducibility edits before publication.

The submission develops finite-sample minimax upper and lower benchmarks for scalar ATE estimation with finite discrete adjustment, real outcomes under conditional second moments, arbitrary cell masses, fixed overlap, and a known heterogeneity radius. The main contribution is a constructive known-radius selector combining polynomial, collision, and zero branches, together with same-class lower benchmarks and a regime theorem identifying where the bracket is tight. The verified statements support the central claims, including the residual shrinking-radius wedge, but several presentation choices overstate or blur scope and some verification metadata is stale.

## Strengths
- The main statistical contribution is clear and nontrivial: a radius-indexed same-class bracket for real-outcome discrete adjustment under weak second-moment control.
- The paper engages the closest binary discrete-adjustment work with explicit rates and conditions rather than only citing it generically.
- The estimator construction is constructive and the main regime theorem carefully distinguishes matched regions from the residual shrinking-radius wedge.
- The manuscript is unusually explicit about formal verification scope and separates the same-class bracket from the conditional binary-collision comparison.

## Findings
- **[major·other] Verification note** — The verification metadata is stale: the manuscript says, "verified ... at verification contract commit \texttt{d110bd64f2651b9ae5401ca84bbb269b5a579546}," while the current verification contract supplied for review is commit \texttt{462a124d29ae27887f711787ac2bc60f6b7e6e2f}.
  - *Fix:* Update the verification note, author footnote if needed, and any bundled crosswalk references to the current contract commit and make the stated build command point to that exact artifact.
- **[major·prose] abstract** — The abstract violates the affirmative contribution framing rule by ending with non-coverage prose: "Adaptation to unknown \(M\) or \(\sigma\), and inference, are outside the estimation bracket studied here." Page-facing prose has no limitations section and should state the delivered scope affirmatively.
  - *Fix:* Rewrite the final scope sentence affirmatively, e.g. state that the bracket is for point-estimation MSE with fixed overlap and known \(M\) and \(\sigma\), and move the adaptation/inference non-coverage to the Limitations section.
- **[minor·prose] Related work** — The application paragraph uses absent-deliverable framing outside a limitations/future-work section: "This paper proves risk bounds rather than conducting that application."
  - *Fix:* Rewrite affirmatively, e.g. "The paper uses that empirical setting to motivate the real-outcome risk bounds for sparse discrete adjustment."
- **[minor·prose] Related work** — The comparison table row "Same class? & upper and lower differ & yes, one class both sides" is too compressed and risks implying that the closest competitor lacks same-model conclusions in a broad sense, rather than that this paper's radius-indexed upper and lower benchmarks are stated over one common real-outcome class.
  - *Fix:* Replace the row with a more precise description, such as "Radius-indexed same-class bracket" and explain in text that the novelty is a single real-outcome class indexed by \(\sigma\) with both benchmarks at the same indices.
- **[minor·prose] Related work** — The sentence "The last row is the sharpest difference: the upper and lower bounds here are proved over the same model class at the same indices, so their ratio is a statement about the minimax risk itself" overstates what a bracket ratio identifies. The ratio bounds the remaining gap between two benchmarks sandwiching the minimax risk; it is not itself the minimax risk.
  - *Fix:* Rewrite to say that the ratio measures the benchmark gap for the same minimax problem and becomes a rate statement precisely in the regimes where the benchmarks are comparable.
- **[minor·prose] Setup and assumptions** — The prose says, "Bounded outcomes give sub-Gaussian concentration for free; a second moment does not," which is too broad because a second-moment condition still gives Chebyshev-type tail control, just not bounded/sub-Gaussian concentration.
  - *Fix:* Rewrite as "a second-moment envelope supplies variance control but not bounded or sub-Gaussian concentration."
- **[minor·structure] Setup and assumptions** — The paper uses the label "frontier" for \(r_{n,d,\sigma}\) and for theorem titles such as "All-alphabet frontier upper bound." Although the manuscript later clarifies the intended meaning, the term can still suggest a globally sharp minimax frontier in the residual shrinking-radius region.
  - *Fix:* Rename the benchmark in prose and theorem titles to "selector benchmark" or "selector upper benchmark," or move the clarification before the first theorem-title use and repeat it near the abstract/introduction summary.
- **[minor·structure] Discussion and limitations** — The Limitations section is substantively useful but arrives after many earlier scope caveats. This makes the abstract and introduction carry limitation-like material in ordinary prose.
  - *Fix:* Keep non-coverage statements about unknown \(M\), unknown \(\sigma\), inference, deteriorating overlap, and adaptation in the Limitations/Future work sections; in the abstract and introduction, state the fixed-known-radius point-estimation scope affirmatively.
- **[nit·prose] global** — Notation occasionally alternates between the conceptual benchmark names and raw formulas in a way that burdens the reader, especially around \(u_{n,d}\), \(h_{n,d,\sigma}\), \(q_{n,d,\sigma}\), \(r_{n,d,\sigma}\), and \(\ell_{n,d,\sigma}\).
  - *Fix:* Keep the benchmark table, then consistently use the table names in prose and reserve formula expansions for theorem statements and first use within each section.

## Questions for authors
- Will the public replication artifact include the exact verification contract, presentation crosswalk, and Lean source at commit 462a124d29ae27887f711787ac2bc60f6b7e6e2f?
- Do you intend "frontier" to remain a term of art for the selector benchmark, or would a less loaded name better protect the residual-wedge scope?

