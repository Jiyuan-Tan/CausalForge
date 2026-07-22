# Title
**Chebyshev Rollout Schedules for Polynomial Extrapolation under Low-Order Interference**

**Contribution statement.** The paper derives the minimax treated-fraction schedule, under a sharp total-variation variance envelope, for estimating a polynomial rollout contrast in finite-population monotone Bernoulli designs, and shows that shifted Chebyshev-Lobatto schedules attain the low-budget exponential rate.

env_overrides: oeq:exact-nested-minimax=remarkv

# Notation
notation_gaps: none

| note symbol | paper notation | defining property in one phrase | home |
|---|---|---|---|
| finite assignment space | $\Omega$ | finite set over which the experimenter's rollout randomization is supported | §Setup and Assumptions |
| rollout randomization | $\pi$ | probability mass function on $\Omega$ inducing design moments | §Setup and Assumptions |
| design expectation | $\mathbb E_\pi$ | finite-sum expectation under $\pi$ | §Setup and Assumptions |
| design variance | $\operatorname{Var}_\pi$ | finite-sum variance under $\pi$ | §Setup and Assumptions |
| design covariance | $\operatorname{Cov}_\pi$ | finite-sum covariance under $\pi$ | §Setup and Assumptions |
| population size | $n$ | number of units in the finite population | §Setup and Assumptions |
| unit set | $U_n$ | finite population of $n$ units | §Setup and Assumptions |
| rollout measurement index | $j$ | index for measurement rounds $0,\ldots,k$ | §Setup and Assumptions |
| number of rollout intervals | $k$ | final measurement index, giving $k+1$ measurement nodes | §Setup and Assumptions |
| polynomial order | $\beta$ | degree bound for rollout mean curves and unbiasedness moments | §Setup and Assumptions |
| rollout budget | $q$ | maximum treated fraction reached by the final rollout measurement | §Setup and Assumptions |
| budget cap | $q_{\max}$ | fixed upper bound for the low-budget regime | ass:low-budget-cap |
| schedule | $p=(p_0,\ldots,p_k)$ | ordered vector of rollout treated fractions | def:budgeted-schedule-class |
| budgeted schedule class | $S_{k,q}$ | admissible schedules from $0$ to $q$ with strictly increasing interior nodes | def:budgeted-schedule-class |
| assignment vector | $Z_j$ | contemporaneous assignment vector at rollout measurement $j$ | ass:static-rollout-consistency |
| potential outcome | $Y_i(Z_j)$ | unit $i$ potential outcome under the contemporaneous assignment vector | ass:static-rollout-consistency |
| round mean | $\bar Y_j$ | finite-population average outcome observed at rollout measurement $j$ | ass:static-rollout-consistency |
| law | $P$ | admissible finite-population law satisfying the stated rollout restrictions | def:rollout-law-class |
| law class | $\mathcal P_\beta$ | laws satisfying consistency, polynomiality, and the variance envelope | def:rollout-law-class |
| rollout mean curve | $m_P(u)$ | mean response curve as a function of treated fraction $u$ under law $P$ | ass:beta-order-polynomial |
| polynomial coefficients | $a_{P,\ell}$ | coefficient of $u^\ell$ in the degree-$\beta$ rollout mean curve | ass:beta-order-polynomial |
| treatment contrast | $\tau_P$ | endpoint contrast $m_P(1)-m_P(0)$ | prop:rollout-polynomial-identity |
| variance envelope scale | $\sigma_0^2/n$ | uniform upper bound on each round-mean design variance | ass:round-mean-variance-envelope |
| weight vector | $w=(w_0,\ldots,w_k)$ | linear coefficients applied to the rollout round means | def:unbiased-weight-set |
| unbiased weight set | $W_\beta(p)$ | weights satisfying the polynomial moment equations through degree $\beta$ | def:unbiased-weight-set |
| estimator | $\hat\tau_{w,p}$ | weighted rollout estimator $\sum_{j=0}^k w_j\bar Y_j$ | §Setup and Assumptions |
| shifted Chebyshev-Lobatto node | $p^{\mathrm{Ch}}_j(k,q)$ | $j$th shifted Chebyshev-Lobatto treated fraction on $[0,q]$ | def:chebyshev-schedule |
| shifted Chebyshev-Lobatto schedule | $p^{\mathrm{Ch}}(k,q)$ | vector of shifted Chebyshev-Lobatto treated fractions | def:chebyshev-schedule |
| amplification criterion | $A_\beta(p)$ | squared minimum $\ell^1$ norm over unbiased weights for schedule $p$ | def:amplification-criterion |
| minimax amplification | $M_{\beta,k,q}$ | infimum of $A_\beta(p)$ over budgeted schedules | def:amplification-criterion |
| covariance matrix | $\Gamma_P(p)$ | design covariance matrix of rollout round means under law $P$ and schedule $p$ | def:exact-nested-risk |
| exact nested risk | $R_{\mathrm{exact}}(\beta,k,q)$ | schedule-and-weight minimax variance using the true covariance matrix | def:exact-nested-risk |
| equal-spacing schedule | $p^{\mathrm{eq}}(\beta,q)$ | equally spaced $\beta+1$ node schedule on $[0,q]$ | §Setup and Assumptions |
| equal-spacing constant | $C_{\mathrm{eq}}$ | universal upper-bound constant for equal-spacing amplification | prop:equal-spacing-benchmark |
| approximation polynomial | $r$ | degree-at-most-$\beta$ real polynomial used in the dual norm | lem:amplification-dual-norm |
| Chebyshev polynomial | $T_\beta$ | degree-$\beta$ Chebyshev polynomial of the first kind | lem:chebyshev-exterior-extremal |
| exterior point | $x_0$ | point outside $[-1,1]$ at which polynomial extrapolation is evaluated | lem:chebyshev-exterior-extremal |
| oversampling ratio | $c$ | constant requiring $k\ge c\beta$ for Chebyshev norming | lem:oversampled-chebyshev-lobatto-norming |
| norming constant | $K(c)$ | finite constant controlling continuous sup norm by oversampled Lobatto values | lem:oversampled-chebyshev-lobatto-norming |
| low-budget exterior point | $x_q$ | affine image of $1$ when $[0,q]$ is mapped to $[-1,1]$ | lem:continuous-chebyshev-endpoint-bound |
| Chebyshev multiplier | $\lambda(q)$ | exterior Chebyshev growth factor $x_q+\sqrt{x_q^2-1}$ | lem:continuous-chebyshev-endpoint-bound |
| pointwise Chebyshev base | $\rho(q)$ | low-budget base $q\lambda(q)=(1+\sqrt{1-q})^2$ | lem:continuous-chebyshev-endpoint-bound |
| endpoint-bound constants | $C(q_{\max}),c(q_{\max})$ | constants uniform over $q\in(0,q_{\max}]$ for the continuous endpoint bound | lem:continuous-chebyshev-endpoint-bound |
| minimax constants | $C_-(q_{\max}),C_+(c,q_{\max})$ | lower and upper constants in the Chebyshev minimax amplification theorem | thm:chebyshev-minimax |

# Sections
## section: Abstract
This section will be drafted after the body is fixed. It will state the finite-population rollout problem, the polynomial low-order restriction, the minimax schedule result under the variance envelope, and the Chebyshev low-budget rate without introducing formal inventory or proof details.

objs: none

bib: none

## section: Introduction
This section motivates treated-fraction placement in staggered rollout experiments with interference, relates the problem to potential outcomes, exposure-based randomization inference, low-order network interference, and optimal design, and states the main contribution at a high level. It includes only one factual sentence saying that the appendix records the machine-verified formal scope.

objs: none

bib: rubin1974, imbens2015, horvitz1952, manski1993, manski2013, aronow2017, savje2017, eckles2017, ugander2013, cortez2022, cortezrodriguez2022, cortezrodriguez2024, eichhorn2024, jiang2023, cai2023, fan2025, smith1918, kiefer1959, kiefer1974, pukelsheim1993, karlin1966

## section: Setup and Assumptions
This section introduces the finite-population monotone Bernoulli rollout design, the schedule and law classes, the polynomial rollout restriction, the variance envelope, the unbiased linear weights, the Chebyshev schedule, the amplification criterion, and the exact nested-risk benchmark. It also introduces ordinary notation used by later frozen statements, including $\Omega,\pi,\mathbb E_\pi,\operatorname{Var}_\pi,\operatorname{Cov}_\pi,n,U_n,\hat\tau_{w,p}$, and $p^{\mathrm{eq}}(\beta,q)$.

objs: ass:static-rollout-consistency, ass:beta-order-polynomial, ass:round-mean-variance-envelope, ass:low-budget-cap, def:budgeted-schedule-class, def:rollout-law-class, def:unbiased-weight-set, def:chebyshev-schedule, def:amplification-criterion, def:exact-nested-risk

bib: rubin1974, imbens2015, horvitz1952, aronow2017, savje2017, cortez2022, cortezrodriguez2022, cortezrodriguez2024

## section: Main Results
This section presents the polynomial identity, the total-variation envelope design theorem, the equal-spacing benchmark, the full-budget boundary observation, and the Chebyshev minimax theorem. The section emphasizes the econometric interpretation: the design variable is the treated-fraction schedule, and Chebyshev-Lobatto placement controls the worst-case amplification exponent in the low-budget regime.

objs: prop:rollout-polynomial-identity, thm:tv-envelope-design, prop:equal-spacing-benchmark, prop:no-extrapolation-boundary, thm:chebyshev-minimax

bib: smith1918, kiefer1959, kiefer1974, pukelsheim1993, karlin1966, tsybakov2009, zhu2015, allard2025

## section: Discussion and Extensions
This section discusses how the envelope result relates to the exact finite-population nested-rollout covariance problem, reports the exact-risk rate-feasibility implication, and labels exact Chebyshev optimality for the true covariance matrix as an open question rather than a proved property. It also situates possible extensions to clustered and mixed rollout designs without making them part of the contribution.

objs: oeq:exact-nested-minimax, lem:exact-risk-envelope-upper, lem:exact-chebyshev-rate-feasible

bib: cortezrodriguez2024, eichhorn2024, jiang2023, cai2023, roth2021, chen2025, fan2025, bhadra2025, schroder2026

## section: Appendix: Proofs and Verification
This section contains the proof architecture and auxiliary approximation and variance lemmas: the $\ell^1/\ell^\infty$ dual norm, Chebyshev exterior extremality, oversampled Lobatto norming, the continuous endpoint bound, Chebyshev schedule admissibility, nonemptiness of unbiased weights, and variance-envelope sharpness. It ends with a verification note consolidating the Lean machine-checking scope: the finite-design variance algebra and real-polynomial approximation objects are verified, while the potential-outcome consistency, polynomial rollout class, and round-mean variance envelope enter as assumptions.

objs: lem:amplification-dual-norm, lem:chebyshev-exterior-extremal, lem:oversampled-chebyshev-lobatto-norming, lem:continuous-chebyshev-endpoint-bound, lem:chebyshev-schedule-admissible, lem:unbiased-weight-set-nonempty, lem:variance-envelope-sharpness

bib: karlin1966, pukelsheim1993, tsybakov2009, zhu2015, allard2025
