# Chebyshev Rollout Schedules for Low-Budget Extrapolation

Under polynomial rollout means and a sharp round-mean variance envelope, Chebyshev-Lobatto measurement fractions attain the minimax exponential variance-amplification rate for estimating full adoption from partial rollout.

---

## The design question is where to measure before full adoption

- A rollout experiment observes outcomes as treated fraction rises from \(0\) to a budget \(q<1\).
- The estimand is the full-adoption contrast, comparing \(u=1\) with \(u=0\).
- The econometric choice is the schedule \(p=(p_0,\ldots,p_k)\), the treated fractions at which round means are measured.
- The statistical question is how much variance the extrapolation from \([0,q]\) to \(1\) must amplify.
- The paper answers this question for linear unbiased estimators under a diagonal variance envelope.

---

## The result is a minimax schedule for the envelope problem

- Under static rollout consistency, each round mean targets the rollout mean curve at its treated fraction.
- Under a degree-\(\beta\) polynomial rollout mean, unbiased estimation is polynomial extrapolation.
- Under the round-mean variance envelope, worst-case variance is governed by the total variation of the extrapolation weights.
- Chebyshev-Lobatto schedules place measurement fractions densely near \(0\) and \(q\).
- They attain the minimax amplification rate up to constants depending only on the budget cap and oversampling ratio.

@informal thm:chebyshev-minimax: Under \(q\le q_{\max}<1\) and \(k\ge c\beta\), Chebyshev-Lobatto schedules attain the minimax amplification rate up to constants.

---

## A concrete example is network spillovers under a rollout cap

- Suppose a platform can roll out a treatment to at most fraction \(q\) during the experiment.
- Outcomes may depend on treated neighbors or peers, so standard no-interference logic is too narrow for the mean response.
- Low-order interference says the average response along the rollout path is captured by interactions up to order \(\beta\).
- The experiment observes mean outcomes only for treated fractions between \(0\) and \(q\).
- The target remains the global treatment contrast at full adoption.

@figure rollout-extrapolation: A box-and-arrow schematic showing rollout measurements on treated fractions from 0 to q feeding a polynomial extrapolation step, which feeds the full-adoption contrast at 1.

---

## The rollout mean is the object being extrapolated

- Let \(m_P(u)\) be the rollout mean curve: the expected round mean when the treated fraction is \(u\).
- Static rollout consistency gives each round mean its contemporaneous potential-outcome interpretation.
- The polynomial order \(\beta\) is the degree bound on this curve.
- The endpoint contrast is \(\tau_P=m_P(1)-m_P(0)\), the full-adoption effect along the rollout path.
- In the example, \(\beta\) represents the highest interaction order retained in the average spillover structure.

@formal ass:static-rollout-consistency

---

## The key restriction turns interference into polynomial extrapolation

- The polynomial rollout mean condition is the low-order structure used by the schedule result.
- It allows arbitrary coefficients, while fixing the curve’s degree at \(\beta\).
- A linear estimator is unbiased when its weights exactly reproduce the endpoint contrast for every polynomial of that degree.
- The schedule controls how hard that polynomial exactness is to achieve.

@formal ass:beta-order-polynomial

---

## The variance envelope makes weight size the risk criterion

- Each round mean has variance at most \(\sigma_0^2/n\), where \(\sigma_0^2\) is the envelope scale.
- Cross-round covariance is treated through the positive-semidefinite diagonal-envelope class.
- For a fixed schedule, the relevant amplification is the squared \(\ell^1\) norm of the best unbiased weights.
- The design problem is to choose measurement fractions that make those weights as stable as possible.

@formal ass:round-mean-variance-envelope

---

## The low-budget regime is genuine extrapolation

- The budget cap keeps the observed interval \([0,q]\) strictly below the target endpoint \(1\).
- This is the regime where endpoint extrapolation drives the variance cost.
- The budgeted schedule starts at \(0\), ends at \(q\), and uses strictly increasing interior treated fractions.
- Chebyshev-Lobatto placement is evaluated inside this admissible schedule class.

@formal ass:low-budget-cap

---

## Unbiased rollout estimation is exactness on monomials

- The estimator is a weighted sum of observed round means.
- The weights must remove the intercept and reproduce each nonconstant monomial through degree \(\beta\).
- Once those moment equations hold, the estimator targets the endpoint contrast for every law in the polynomial class.
- Thus the econometric problem becomes a finite-dimensional polynomial design problem.

@informal prop:rollout-polynomial-identity: Under static rollout consistency and the polynomial rollout mean condition, the endpoint contrast equals the sum of the nonconstant polynomial coefficients.

---

## The envelope theorem identifies the exact design criterion

@informal thm:tv-envelope-design: For any admissible schedule with \(1\le\beta\le k\), every unbiased weight vector estimates the endpoint contrast and has variance at most the envelope scale times its squared \(\ell^1\) norm.

@formal thm:tv-envelope-design

---

## Equal spacing is a useful feasibility benchmark

- With \(\beta+1\) equally spaced measurement fractions, unbiased extrapolation is feasible.
- The certified amplification is at most \(9(\beta/q)^{2\beta}\).
- This benchmark gives a simple reference scale for the low-budget problem.
- The Chebyshev theorem improves the schedule story by deriving the minimax envelope rate.

@informal prop:equal-spacing-benchmark: Equally spaced \(\beta+1\) nodes on \([0,q]\) have amplification at most \(9(\beta/q)^{2\beta}\).

---

## Full rollout has bounded endpoint amplification

- When \(q=1\), the experiment observes both endpoints of the target contrast.
- The difference between the final and baseline round means is polynomial-exact.
- The amplification is at most \(4\), uniformly in \(\beta\).
- This separates the full-budget endpoint case from the low-budget extrapolation rate.

@informal prop:no-extrapolation-boundary: At full rollout with \(q=1\), the endpoint-difference weights have amplification at most \(4\).

---

## Chebyshev placement controls the extrapolation exponent

- Shifted Chebyshev-Lobatto nodes are the usual endpoint-dense grid on \([0,q]\).
- The schedule uses \(p^{\mathrm{Ch}}_j(k,q)\), with more measurement rounds near both ends of the observed interval.
- Oversampling, \(k\ge c\beta\), lets the discrete grid control the continuous polynomial problem.
- The minimax amplification has base \(((1+\sqrt{1-q})^2/q)\), raised to \(2\beta\).

@figure chebyshev-schedule: A box-and-arrow schematic showing the budgeted interval from 0 to q with endpoint-dense Chebyshev-Lobatto measurement boxes feeding an unbiased-weight construction and then an endpoint extrapolation to 1.

---

## The main theorem gives the matching low-budget rate

@formal thm:chebyshev-minimax

---

## The proof converts weights into worst-case polynomials

- The \(\ell^1\) norm of unbiased weights has a dual description using bounded degree-\(\beta\) polynomials.
- A hard schedule admits a polynomial that stays small on measured nodes but grows at the target endpoint.
- Chebyshev exterior extremality gives the sharp continuous growth benchmark.
- Oversampled Lobatto norming transfers that benchmark back to the discrete schedule.
- The upper and lower bounds meet at the same exponential base.

@informal lem:amplification-dual-norm: The minimum \(\ell^1\) norm of unbiased weights equals the largest endpoint contrast of a degree-\(\beta\) polynomial bounded by one on the schedule nodes.

@informal lem:chebyshev-exterior-extremal: A degree-\(\beta\) polynomial bounded by one on \([-1,1]\) is at most the Chebyshev polynomial at any exterior point.

---

## The auxiliary bounds make the rate uniform

- Lobatto norming says an oversampled Chebyshev grid controls the whole interval from its node values.
- The endpoint bound translates the exterior Chebyshev growth to the low-budget point \(q\).
- Chebyshev admissibility verifies the schedule lies in the budgeted schedule class.
- Nonempty unbiased weights ensure the estimator class is available whenever \(k\ge\beta\).
- Sharp variance envelope algebra shows the \(\ell^1\) variance criterion is tight for the diagonal-envelope class.

@informal lem:oversampled-chebyshev-lobatto-norming: With \(k\ge c\beta\), values on the Lobatto grid control every degree-\(\beta\) polynomial on \([-1,1]\) up to \(K(c)\).

@informal lem:continuous-chebyshev-endpoint-bound: Under \(0<q\le q_{\max}<1\), the endpoint growth is bounded above and below by constants times \(\lambda(q)^\beta\).

@informal lem:chebyshev-schedule-admissible: The shifted Chebyshev-Lobatto schedule is admissible for every \(k\ge1\) and \(q\in(0,1]\).

@informal lem:unbiased-weight-set-nonempty: For \(k\ge\beta\), every budgeted schedule has at least one order-\(\beta\) unbiased weight vector.

@informal lem:variance-envelope-sharpness: The round-mean variance envelope gives the \(\ell^1\) upper bound, and a positive-semidefinite covariance matrix attains it.

---

## The exact nested risk inherits the envelope upper rate

- The exact nested covariance problem keeps the true rollout covariance matrix \(\Gamma_P(p)\) inside the risk.
- The envelope risk bounds this exact risk from above at every admissible schedule.
- Therefore the Chebyshev schedule is rate-feasible for the exact nested risk.
- The exact-covariance statement isolates the stronger Chebyshev optimizer equality for the true nested covariance benchmark.

@informal lem:exact-risk-envelope-upper: At every admissible schedule, the exact nested risk is at most \(\sigma_0^2 A_\beta(p)/n\), and the exact minimax risk is at most \(\sigma_0^2 M_{\beta,k,q}/n\).

@informal lem:exact-chebyshev-rate-feasible: With \(k=\lceil c\beta\rceil\), the Chebyshev-Lobatto schedule has exact-risk upper bound at most the envelope scale times the Chebyshev low-budget rate.

@informal oeq:exact-nested-minimax: The exact-covariance question asks whether fixed Chebyshev-Lobatto risk equals the nested exact minimax risk.

---

## The takeaway is a design rule for low-budget rollout experiments

- Treated-fraction placement is the design variable.
- Polynomial rollout means make full adoption estimable by linear extrapolation from partial rollout.
- The diagonal variance envelope makes the squared \(\ell^1\) norm of unbiased weights the sharp risk multiplier.
- Chebyshev-Lobatto measurement fractions attain the minimax envelope amplification rate under \(q\le q_{\max}<1\) and \(k\ge c\beta\).
- For the exact nested rollout covariance, the same schedule delivers the proved rate-feasible upper bound.
