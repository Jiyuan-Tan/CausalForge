# Minimax ATE Estimation With Many Discrete Cells

TL;DR: Under fixed overlap, bounded real outcomes/moments, and known cell-effect heterogeneity radius \(\sigma\), the paper gives finite-sample minimax benchmarks and clipped estimators for average treatment effect (ATE) estimation with the sample size \(n\) and number of cells \(d\) both visible in the rate.

---

## The paper gives a rate map for sparse discrete adjustment

- The target is a scalar ATE with a finite adjustment variable.
- Cell masses may be arbitrary, so many cells can be rare.
- The heterogeneity radius \(\sigma\), the maximal cell-effect deviation in outcome-scale units, indexes the difficulty.
- The estimator chooses among a rare-cell polynomial branch, a crossed-cell collision branch, and a clipped zero branch.
- The minimax risk is at least a lower benchmark and at most the selector benchmark.

@informal thm:two-sided-minimax-bracket-all-d: Under the stated fixed-overlap and real-outcome envelope conditions, minimax mean-squared risk is at least the capped converse benchmark and at most the known-radius selector benchmark.

---

## Sparse cells make ordinary adjustment fragile

- Think of a 401(k)-style program evaluation with discrete adjustment profiles.
- A profile might combine income bin, age bin, firm size, tenure, and prior savings.
- Fixed overlap says each supported profile has treated and control units in population.
- Finite samples still leave many profiles with one arm missing.
- The question is how much ATE accuracy is possible when \(d\) grows with \(n\).

---

## The radius says how much cells can disagree

- Exact homogeneity means each cell has the same treatment effect as the population ATE.
- Larger \(\sigma\) permits larger cell-level departures from the ATE.
- In the 401(k) example, \(\sigma\) bounds the largest supported-profile effect deviation.
- Small \(\sigma\) makes borrowing across cells valuable.
- Large \(\sigma\) makes within-cell treated-control contrasts more valuable.

@formal ass:approximate-homogeneity

---

## Three assumptions carry the estimation problem

- The overlap parameter \(\epsilon\) keeps treatment probabilities away from zero and one inside supported cells.
- The outcome scale \(M\) bounds supported arm-cell conditional means.
- The second central moment envelope keeps real-outcome noise on the same scale.
- Consistency and conditional exchangeability give the usual observed-data identification of the ATE.

@formal ass:overlap

@formal ass:second-central-moment

---

## The estimator compares two ways to borrow information

- Heavy cells are empirically common enough for direct treated-control contrasts.
- Light cells are rare enough that a polynomial approximation is used instead.
- Crossed cells are cells where the sample contains both treatment arms.
- The known-radius selector compares the polynomial scale \(u_{n,d}\) and collision scale \(h_{n,d,\sigma}\).
- The zero branch is useful when the outcome-scale bound itself dominates.

@figure estimator-pipeline: Boxes show observed data, pilot heavy-light split, polynomial branch, crossed-cell collision branch, known-radius branch comparison, and clipped ATE estimate, with arrows from data to branches and from branches to selector.

---

## The rare-cell branch replaces missing contrasts with moments

- A direct plug-in contrast pays for cells where one arm is absent.
- The polynomial branch splits the sample before classification and estimation.
- Heavy cells use ordinary cell contrasts on the estimation block.
- Light cells use one-mark factorial statistics calibrated by shifted-Chebyshev coefficients.
- The gain is the rare-cell polynomial scale \(d^2/[n^2\log^2(en)]\), matching the large-alphabet logic.

---

## The two constructive bounds are complementary

@informal thm:robust-upper-construction-resolution-all-d: Uniformly over the model class, the polynomial estimator has risk at most the parametric term plus the rare-cell polynomial remainder, and the collision estimator has risk at most the parametric term plus \(\sigma^2+d/n^2\).

@formal thm:robust-upper-construction-resolution-all-d

---

## The known-radius selector attains the upper frontier

- The selector uses the known \(\sigma\) only to choose a branch.
- Collision is chosen when the crossed-cell scale is best.
- Polynomial is chosen when rare-cell approximation is best.
- The zero branch is chosen when the outcome-scale cap is best.

@informal thm:frontier-upper-all-d: For every \(n,d,M,\sigma\) in the stated ranges, the known-radius selector has worst-case mean-squared risk at most \(C_\epsilon M^2 r_{n,d,\sigma}\).

@formal thm:frontier-upper-all-d

---

## The closest benchmark is binary discrete adjustment

- Zeng, Balakrishnan, Han, and Kennedy study binary outcomes with discrete confounders.
- Their unrestricted binary benchmark has the sparse-alphabet term \(d^2/(n^2\log^2 n)\).
- Their exact-homogeneity benchmark has the collision term \(d/n^2\).
- This paper transfers binary hard experiments into a real-outcome class.
- The selector and lower bound are stated on the same radius-indexed class.

@informal thm:published-binary-collision-comparison: Under the stated published binary collision guarantee, the selector benchmark is at most the binary collision scale, and it is asymptotically smaller under the stated comparison conditions.

---

## The lower bound comes from two embedded hard families

- The affine route rescales binary outcomes into real outcomes with scale \(M\).
- The exact-homogeneity route supplies the collision baseline.
- The radius route attenuates binary alternatives by \(\sigma/2\).
- The attenuation keeps transported alternatives inside the \(\sigma M\) heterogeneity radius.
- Data processing preserves the hardness of the source experiments.

@figure lower-bound-transport: Boxes show binary exact-homogeneity source, affine real-outcome embedding, exact baseline lower bound, binary radius source, attenuating channel, real-outcome radius family, and radius-channel lower bound, with arrows from sources through embeddings to lower benchmarks.

---

## Binary transfers become same-class converses

@informal prop:zeng-class-inclusion-and-lower-transfer: The affine binary-to-real embedding places the relevant binary source classes inside the real-outcome classes and transfers exact-homogeneity and radius-channel lower bounds onto the \(M\)-scaled risk.

@informal lem:scaled-binary-exact-lower-transfer-all-d: For all alphabet sizes, the exact-homogeneity binary transfer gives minimax risk at least a constant times \(M^2\{n^{-1}+\min(1,d/n^2)\}\).

@informal thm:radius-channel-converse-all-d: For all \(n,d,M,\sigma\) in the stated ranges, minimax risk is at least the exact baseline plus the radius-channel term \(M^2\sigma^2\min\{1,d^2/[n^2\log^2(en)]\}\).

@formal thm:radius-channel-converse-all-d

---

## The bracket is the main finite-sample benchmark

- The lower side combines exact-homogeneity collisions and radius-channel rare cells.
- The upper side is constructive through the known-radius selector.
- Constants depend only on the fixed overlap parameter \(\epsilon\).
- The statement applies for every positive \(n\) and \(d\).

@informal thm:two-sided-minimax-bracket-all-d: Under fixed overlap, bounded real-outcome moments, and radius \(0\le\sigma\le2\), minimax risk lies between the lower benchmark and the selector upper benchmark up to overlap-dependent constants.

@formal thm:two-sided-minimax-bracket-all-d

---

## The endpoints recover the familiar regimes

- At exact homogeneity, the matched scale is \(M^2\{n^{-1}+\min(1,d/n^2)\}\).
- At radius two, the class matches the unrestricted-radius class.
- The unrestricted endpoint has scale \(M^2\{n^{-1}+\min(1,d^2/[n^2\log^2(en)])\}\).
- These endpoint reductions anchor the radius interpretation.

@informal prop:endpoint-reductions-all-d: The exact-homogeneity endpoint is comparable to the collision baseline, and the radius-two endpoint is comparable to the unrestricted polynomial benchmark.

@formal prop:endpoint-reductions-all-d

---

## Most regimes are matched by the selector benchmark

- Every fixed positive radius is matched up to constants.
- Saturated alphabets are matched through the outcome-scale cap.
- Small alphabets are matched when the exact-homogeneity baseline dominates the polynomial term.
- Small radii are matched when \(\sigma^2\) is dominated by the same baseline.
- The residual shrinking-radius wedge is localized by the theorem.

@informal thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d: For fixed positive radii and the stated saturation or parametric-dominance elbows, minimax risk is between constant multiples of the selector benchmark; remaining benchmark separation lies in the specified shrinking-radius wedge.

@formal thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d

---

## The proof is a short chain of reductions

- Identification turns the ATE into a finite weighted sum of cell contrasts.
- The polynomial upper bound treats heavy cells by direct contrasts and light cells by factorial moments.
- The collision upper bound averages observed crossed-cell contrasts and charges uncrossed cells to \(\sigma\).
- The exact lower bound embeds a uniform binary homogeneous collision problem.
- The radius lower bound sends binary alternatives through a \(\sigma/2\) channel before real-outcome scaling.

---

## Also in the paper

@informal thm:robust-upper-construction-resolution: On the restricted alphabet range, the two constructive estimators satisfy the same at-most risk bounds used before the all-alphabet packaging.

@informal thm:frontier-upper: On the restricted alphabet range, the known-radius selector has risk at most the restricted frontier benchmark.

@informal thm:radius-channel-converse: On the restricted alphabet range, minimax risk is at least the parametric, exact, and radius-channel lower benchmark.

@informal thm:two-sided-minimax-bracket: On the restricted alphabet range, minimax risk is bracketed between the finite-range lower and selector upper benchmarks.

@informal prop:endpoint-reductions: The finite-range endpoint algebra identifies the exact-homogeneity and radius-two benchmark reductions.

@informal thm:fixed-interior-tightness-and-shrinking-radius-gap: The finite-range regime algebra gives the fixed-radius, elbow, and residual-wedge conclusions before the all-alphabet extension.

---

## The contribution is a radius-indexed minimax picture

- The model is a real-outcome finite-cell observational experiment with fixed overlap.
- The target is the scalar ATE under arbitrary cell masses.
- The heterogeneity radius \(\sigma\) organizes exact homogeneity, fixed positive radius, and unrestricted-radius behavior.
- The estimators are clipped, finite-sample procedures with explicit branch logic.
- The result gives a same-class lower and upper benchmark, plus the regimes where they agree in order.
