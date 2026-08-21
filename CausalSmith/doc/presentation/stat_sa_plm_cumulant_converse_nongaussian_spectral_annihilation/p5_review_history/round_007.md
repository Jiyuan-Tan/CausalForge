# Referee review

**Recommendation:** major_revision
**Overall score:** 6.4/10 — The verified formal core is substantial and mostly represented faithfully, but the manuscript needs major prose and scope repairs before it is publishable as an econometrics paper.

The paper develops a contour-transform estimator for partially linear models with fixed non-Gaussian cumulant separation and proves fixed-code root-n minimax MSE guarantees, plus ACE and Gaussian benchmark comparisons. The contribution is technically novel and potentially interesting, especially the transform-zero identification and fixed-code risk construction. As written, however, the paper is difficult to read, sometimes overstates comparison claims, and includes several stale or misleading descriptions of what is verified or implemented.

## Strengths
- The main fixed-separation theorem is precise and verified, with explicit fixed-code conditioning and treatment-code radius gates.
- The contour identification mechanism is mathematically interesting and clearly tied to observable residual transforms.
- The ACE comparison is mostly careful about being an upper-guarantee comparison and carries the required theorem-local formalization-scope footnote.
- The Gaussian degeneracy and mixture benchmarks help delimit the scope of the fixed-separation result.

## Findings
- **[major·structure] abstract** — The abstract is too dense and mixes the main statistical contribution with implementation machinery in a way that obscures the econometric contribution. In particular, the sentence beginning "The represented-data construction is a conditional reproducibility layer..." foregrounds compiled adapters before the reader understands the estimator.
  - *Fix:* Rewrite the abstract around three affirmative points: the contour identification result, the fixed-code root-n/minimax risk result under fixed cumulant separation and the displayed L1 treatment-code gate, and the ACE/Gaussian benchmark implications. Move the represented-data sentence to one short final sentence or omit it from the abstract.
- **[major·prose] intro** — The sentence "Second, the fixed-code minimax theorem gives \(\Theta(n^{-1})\) MSE and lower \((1-\gamma)\)-quantile control on the broad non-Gaussian spectral class and the aligned Jin--Mackey--Syrgkanis ACE class" compresses several different claims and can be read as saying the quantile result is minimax or matched, while the theorem verifies an estimator upper quantile bound and matched MSE minimax bounds.
  - *Fix:* Separate the claims: state that the theorem gives matched \(c/n\) and \(C/n\) MSE minimax bounds, and separately that the same contour statistic has a generalized lower-quantile upper bound of order \((\gamma n)^{-1/2}\).
- **[major·prose] main fixed-separation result** — The sentence "Once a valid circle is selected, the empirical transforms behave like averages of bounded-envelope exponential statistics, so the contour ratio inherits the parametric variance order familiar from regular semiparametric estimation..." makes the result sound like a standard regular semiparametric variance calculation. The verified result is a fixed-code upper risk bound from empirical transform concentration and deterministic perturbation, not an efficiency or asymptotic normality statement.
  - *Fix:* Replace with an affirmative description of the verified argument: empirical transform concentration on the fixed bank and the selected-contour perturbation bound yield the \(C/n\) MSE upper bound under fixed primitive constants.
- **[major·prose] certified construction and executable correspondence** — The computational material is presented at a level that reads like an implemented reproducibility deliverable, while the verified statements are conditional on a compiled bounded spectral adapter satisfying the full canonical build-and-compilation specification.
  - *Fix:* Add a short paragraph at the start of the appendix stating affirmatively that the paper specifies a conditional executable correspondence theorem for implementations satisfying the displayed build contract. Avoid language that suggests an actual distributed implementation or independent executable artifact unless one is provided.
- **[major·structure] global** — The paper is not yet self-contained enough for an econometrics audience: key objects such as the certified bank, represented records, canonical adapters, and fixed-code base records appear in the main theorem before the reader has enough intuition for their statistical role.
  - *Fix:* Move most represented-data details to the appendix and add a concise main-text subsection explaining only the statistical estimator: pilot bank selection, evaluation contour ratio, clipping, and fixed-code conditioning. Keep implementation contracts out of the theorem discussion except for a clearly labeled reproducibility clause.
- **[major·statement] setup and assumptions** — The sample indexing is inconsistent for readers. The text writes samples as \(O_1,\ldots,O_n\), but defines folds by \(I_0=\{i:i<\lfloor n/2\rfloor\}\) and \(I_1=\{i:i\ge\lfloor n/2\rfloor\}\), which is natural for zero-based indices and confusing for one-based samples.
  - *Fix:* Define the sample index set explicitly, preferably as \(\{0,\ldots,n-1\}\), and then use that convention consistently in all empirical averages and fold definitions, or rewrite the folds for one-based indexing.
- **[minor·structure] related work** — The related-work section is broad and well cited, but it reads partly as a citation catalogue. The closest comparison, Jin--Mackey--Syrgkanis ACE, is discussed mathematically, while the paper gives less direct explanation of which assumptions differ and why an applied econometrician would prefer the contour construction in the fixed-code setting.
  - *Fix:* Add a compact comparison paragraph or table contrasting contour and ACE by input assumptions, code-radius requirements, target error criterion, fixed-separation dependence, and what is being compared.
- **[minor·prose] comparison with ACE and Gaussian benchmarks** — The title and repeated phrase "Gaussian class degeneracy" may sound pejorative or broader than the verified result. The theorem characterizes the bounded-outcome Gaussian JMS intersection by forcing \(\theta_0=0\) and zero risks when the fixed-code intersection is nonempty.
  - *Fix:* Rename the result and prose to something like "Bounded-outcome Gaussian diagnostic" or "Bounded-outcome Gaussian intersection" and state the positive characterization directly.
- **[minor·prose] verification scope and crosswalk** — The sentence "The theorem statements and proofs corresponding to the displayed formal environments are machine-checked in Lean 4..." is broad. The contract shows all listed declarations are sorry-free and faithful, but one external ACE dependency is verified only as a reduction/application conditional on the cited published result.
  - *Fix:* Keep the sentence but immediately add the existing ACE qualification in the same paragraph, so the trust boundary is visible before the reader reaches the footnote.
- **[minor·prose] global** — Several formal titles violate the house typography rule requiring sentence case. Examples include "Common Experiment Dichotomy", "Local Gaussian Benchmarks", and "Zero-Free Nuisance Factor".
  - *Fix:* Change these to sentence case, e.g. "Common experiment dichotomy", "Local Gaussian benchmarks", and "Zero-free nuisance factor".
- **[minor·prose] limitations and future work** — The open-question remark is appropriately placed in a limitations/future-work section, but it is long and mixes agenda, criteria, and missing deliverables in one sentence.
  - *Fix:* Split the open agenda into two or three shorter sentences: one defining the triangular regime, one naming the desired selector/rate/inference target, and one naming the lower-bound requirement.
- **[nit·prose] finite contour bank** — The displayed bookkeeping identities in the manuscript use both \(u_\star\) and, in the verification contract excerpt, an apparent \(\nu_\star\) typo in the same line.
  - *Fix:* Check the source and ensure the paper consistently writes \(u_\star\) for the exponent defining \(a_\star=2^{-u_\star}\).

## Questions for authors
- Is an actual compiled bounded spectral adapter distributed with the paper, or is the contribution limited to the conditional executable correspondence theorem?
- Can the authors provide a short practical description of when the direct \(L^1(P_X)\) treatment-code gate is easier or harder to satisfy than the JMS ACE eligibility conditions?
- Do the authors intend the generalized lower \((1-\gamma)\)-quantile criterion as a main decision criterion, or only as a consequence of the MSE bound?

