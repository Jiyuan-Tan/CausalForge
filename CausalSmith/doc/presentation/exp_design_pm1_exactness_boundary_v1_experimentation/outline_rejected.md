# Title
**Exactness and Loss in Design-Based Network Experiments with Two-Block Homophily**

**Contribution statement.** The paper characterizes when the covariance optimum of an interference-aware experimental-design problem is attainable by an actual balanced sign-assignment design and gives a sharp finite-dimensional formula for the resulting implementability loss.

# Notation
env_overrides: 

notation_gaps: truncSelector=selector named in thm:sharp-rho-star and lem:weighted-simplex-truncation but not introduced by a frozen definition environment

| note symbol | paper notation | defining property in one phrase | home |
|---|---|---|---|
| sample size | $n=2m$ | total number of experimental units in two equal communities | §Setup and Assumptions |
| community size | $m$ | number of units in each block | ass:two-block-homophily |
| within-block weight | $a$ | scaled edge weight for pairs in the same block | ass:two-block-homophily |
| across-block weight | $b$ | scaled edge weight for pairs in different blocks | ass:two-block-homophily |
| first block | $A_m$ | first community of size $m$ | def:two-block-graph |
| second block | $B_m$ | second community of size $m$ | def:two-block-graph |
| graph weights | $W_{ij}$ | two-block weighted adjacency matrix with zero diagonal | def:two-block-graph |
| graph Laplacian | $L_m$ | Laplacian associated with the two-block weighted graph | §Setup and Assumptions |
| Laplacian pseudoinverse | $L_m^\dagger$ | Moore--Penrose inverse used through the two-block spectral coordinates | §Setup and Assumptions |
| all-ones matrix | $J_n$ | $n\times n$ matrix of ones | §Setup and Assumptions |
| assignment vector | $Z$ | random vector taking values in $\{-1,1\}^n$ | def:balanced-design-class |
| assignment realization | $z$ | element of the sign-assignment space $\{-1,1\}^n$ | def:balanced-design-class |
| assignment law | $P$ | probability law on $\{-1,1\}^n$ | def:balanced-design-class |
| balanced design class | $\mathcal P_m^{\mathrm{bal}}$ | sign-symmetric assignment laws | def:balanced-design-class |
| block-exchangeable design class | $\mathcal P_m^{\mathrm{sym}}$ | balanced laws invariant to within-block permutations and block swap | def:block-exchangeable-design-class |
| assignment covariance | $X(P)$ | second-moment matrix induced by a block-exchangeable sign law | def:implementable-covariance-class |
| implementable covariance class | $\mathcal C_m^{\pm}$ | covariance matrices attainable by laws in $\mathcal P_m^{\mathrm{sym}}$ | def:implementable-covariance-class |
| block elliptope | $\mathcal E_m^{\mathrm{blk}}$ | two-parameter block-symmetric elliptope slice | def:block-elliptope |
| block covariance point | $X(u,v)$ | block-symmetric covariance matrix indexed by within- and across-block coordinates | def:block-elliptope |
| within-block coordinate | $u$ | common off-diagonal covariance within each block | def:block-elliptope |
| across-block coordinate | $v$ | common covariance across the two blocks | def:block-elliptope |
| robustness weight | $\kappa$ | nonnegative coefficient on the Frobenius norm term | def:design-objective |
| homophily tradeoff weight | $r$ | nonnegative coefficient on the $L_m^\dagger$ term | def:design-objective |
| design objective | $F_{r,\kappa}(X)$ | trace-plus-robustness objective evaluated at covariance $X$ | def:design-objective |
| implementability gap | $\Delta_m^{\pm}(r,\kappa)$ | implementable optimum minus relaxed block-elliptope optimum | def:implementability-gap |
| block-sum law | $\mathcal L_P(S_A,S_B)$ | law of the two within-block assignment sums under $P$ | def:block-sum-handle |
| block sums | $(S_A,S_B)$ | pair $(\sum_{i\in A_m}Z_i,\sum_{i\in B_m}Z_i)$ | def:block-sum-handle |
| spectral multiplicity | $q$ | $2(m-1)$, the within-block contrast multiplicity | lem:block-spectral-coordinates |
| spectral $x$ coordinate | $x$ | $1-u$ in the reduced block-spectral coordinates | lem:block-spectral-coordinates |
| spectral $y$ coordinate | $y$ | $1+(m-1)u-mv$ in the reduced block-spectral coordinates | lem:block-spectral-coordinates |
| spectral $z$ coordinate | $z$ | $1+(m-1)u+mv$ in the reduced block-spectral coordinates | lem:block-spectral-coordinates |
| reduced triangle | $T_m$ | simplex $\{x,y,z\ge0: qx+y+z=2m\}$ | lem:block-spectral-coordinates |
| cut covariance | $X_{\mathrm{cut}}$ | block covariance with spectral coordinates $(0,2m,0)$ | lem:block-spectral-coordinates |
| cut design | $P_{\mathrm{cut}}$ | sign design attaining the cut covariance | thm:cut-corner-exactness |
| iid covariance | $I_n$ | identity covariance matrix with spectral coordinates $(1,1,1)$ | lem:block-spectral-coordinates |
| iid design | $P_{\mathrm{iid}}$ | independent sign design with covariance $I_n$ | thm:robust-corner-exactness |
| spread covariance | $X_{\mathrm{spread}}$ | relaxed spread vertex with spectral coordinates $(m/(m-1),0,0)$ | thm:gap-window |
| spectral objective coefficient | $c_x$ | coefficient $q((a+b)+r/(a+b))$ in the reduced objective | lem:block-spectral-coordinates |
| spectral objective coefficient | $c_y$ | coefficient $2b+r/(2b)$ in the reduced objective | lem:block-spectral-coordinates |
| spectral objective coefficient | $c_z$ | coefficient $2m$ in the reduced objective | lem:block-spectral-coordinates |
| reduced objective | $\phi_{r,\kappa}(x,y,z)$ | scalar objective on $T_m$ equal to the block covariance objective | lem:rounding-gap-reduction |
| parity truncation level | $d_m$ | $0$ for even $m$ and $2/m$ for odd $m$ | lem:rounding-gap-reduction |
| sharp loss | $\rho_\star(m,a,b,r,\kappa)$ | loss quantity identified with $\Delta_m^{\pm}(r,\kappa)$ | thm:sharp-rho-star |
| simplex index set | $I=\{x,y,z\}$ | coordinate labels for the weighted simplex problem | lem:weighted-simplex-active-set |
| simplex mass | $M=2m$ | total mass in the active-set simplex | lem:weighted-simplex-active-set |
| simplex coordinates | $t_i$ | transformed coordinates with $t_x=qx,t_y=y,t_z=z$ | lem:weighted-simplex-active-set |
| simplex | $\Delta_M$ | set $\{t_i\ge0:\sum_i t_i=M\}$ | lem:weighted-simplex-active-set |
| linear coefficients | $\alpha=(\alpha_x,\alpha_y,\alpha_z)$ | coefficients in the weighted simplex objective | lem:weighted-simplex-active-set |
| quadratic weights | $\beta=(\beta_x,\beta_y,\beta_z)$ | weights with $\beta_x=1/q$ and $\beta_y=\beta_z=1$ | lem:weighted-simplex-active-set |
| simplex objective | $\Phi(t)$ | linear term plus $\kappa$ times weighted Euclidean norm on $\Delta_M$ | lem:weighted-simplex-active-set |
| active support | $S$ | nonempty subset of $\{x,y,z\}$ used in the active-set formula | lem:weighted-simplex-active-set |
| active weight total | $A_S$ | sum $\sum_{i\in S}\beta_i^{-1}$ | lem:weighted-simplex-active-set |
| active weighted mean | $\mu_S$ | weighted mean of $\alpha_i$ over support $S$ | lem:weighted-simplex-active-set |
| active dispersion | $V_S$ | weighted squared dispersion of $\alpha_i$ around $\mu_S$ on $S$ | lem:weighted-simplex-active-set |
| active multiplier | $\lambda_S$ | admissible multiplier determining the active-set minimizer | lem:weighted-simplex-active-set |
| truncated simplex | $K_d$ | subset of $\Delta_M$ with $t_y+t_z\ge d$ | lem:weighted-simplex-truncation |
| relaxed selector | $t_{\mathrm{rel}}$ | selected relaxed minimizer of the simplex objective | lem:weighted-simplex-truncation |
| truncation segment | $H_d$ | boundary segment with $t_x=M-d$, $t_y=s$, $t_z=d-s$ | lem:weighted-simplex-truncation |
| segment coordinate | $s$ | scalar coordinate along the truncation boundary | lem:weighted-simplex-truncation |
| segment objective | $g_d(s)$ | objective restricted to $H_d$ | lem:weighted-simplex-truncation |
| truncation scale | $A_d$ | $(M-d)^2/q$ in the segment formula | lem:weighted-simplex-truncation |
| coefficient contrast | $\delta$ | $\alpha_y-\alpha_z$ in the segment formula | lem:weighted-simplex-truncation |
| cut threshold | $r_{\mathrm{cut}}(m,a,b,\kappa)$ | largest strict range endpoint for cut-corner exactness | thm:cut-corner-exactness |
| gap robustness threshold | $\kappa_{\mathrm{gap}}(m,a,b)$ | upper robustness range for the odd-community gap window | thm:gap-window |
| gap cut threshold | $r_{\mathrm{cut}}^{\mathrm{gap}}(m,a,b,\kappa)$ | cut-side comparison threshold in the gap-window theorem | thm:gap-window |
| lower spread comparison | $R_x^{-}(m,a,b,\kappa)$ | lower comparison value used to define the positive-gap interval | thm:gap-window |
| upper spread comparison | $R_x^{+}(m,a,b,\kappa)$ | upper comparison value used to define the positive-gap interval | thm:gap-window |
| lower gap endpoint | $r_{\mathrm{gap}}^{-}(m,a,b,\kappa)$ | midpoint lower endpoint of the positive-gap interval | thm:gap-window |
| upper gap endpoint | $r_{\mathrm{gap}}^{+}(m,a,b,\kappa)$ | upper endpoint of the positive-gap interval | thm:gap-window |

# Sections

## section: Abstract
The abstract will be drafted after the paper body is fixed. It will state the design problem, the implementability question for sign-assignment covariances, the exactness cases, the odd-community positive-loss window, and the sharp active-set formula without adding claims beyond the frozen theorem layer.

objs: 

bib: thiyageswaran2026

## section: Introduction
The introduction will motivate implementability as a design-based constraint in network experiments with interference and homophily, positioning the paper relative to covariance-based design and randomized assignment mechanisms. It will state the contribution at the level of results: exact cut and iid cases, a positive loss window for odd block sizes, and a finite active-set formula for the loss. A single factual sentence will point readers to the appendix verification note for the scope of machine checking.

objs: 

bib: fisher1935, horvitz1952, rubin1974, hudgens2008, aronow2013, athey2015, eckles2014, thiyageswaran2026

## section: Setup and Assumptions
This section introduces the finite-population sign-assignment setting, the two-block weighted graph, the block elliptope, balanced and block-exchangeable assignment laws, implementable covariance matrices, the design objective, the implementability gap, and the block-sum handle. It also records the standing restrictions on two-block homophily, sign symmetry, low scale, and odd community size, with notation for $L_m$, $L_m^\dagger$, $J_n$, and $\mathcal C_m^\pm$ introduced before their first use.

objs: ass:two-block-homophily, ass:balanced-sign-design, ass:low-scale-two-block, ass:odd-community-size, def:two-block-graph, def:block-elliptope, def:balanced-design-class, def:block-exchangeable-design-class, def:implementable-covariance-class, def:design-objective, def:implementability-gap, def:block-sum-handle

bib: rubin1974, horvitz1952, hudgens2008, aronow2013, savje2017, leung2019, li2020, manski1993, manski2013, mcpherson2001, holland1983, newman2002, abbe2017, banerjee2013

## section: Main Results
This section presents the formal results in the order a reader uses them: symmetry reduction, exactness at the cut corner, exactness of the iid corner only on the affine-balanced locus, failure of implementability in the odd-community spread window, and the sharp active-set representation of the implementability loss. The section keeps the gap-window result separate from the sharp active-set theorem and does not assert any unproved boundary characterization for an $r_\star$ frontier.

objs: prop:symmetry-reduction, thm:cut-corner-exactness, thm:robust-corner-exactness, thm:gap-window, thm:sharp-rho-star

bib: thiyageswaran2026, ugander2013, eckles2014, ugander2020, baird2018, brennan2022, corterodriguez2024, fatemi2020, viviano2023, chen2023, cai2023, goemans1995, deza1997, boyd2004

## section: Discussion and Extensions
This section interprets the verified results for experimental-design practice: when the covariance relaxation can be implemented exactly, when parity blocks implementation, and how the finite active-set formula can be used as a diagnostic for loss. It will relate the results to graph-cluster randomization, correlated assignment, discrepancy-based balancing, and covariance-optimized designs, while avoiding contribution claims about conjectural or non-frozen quantities.

objs: 

bib: efron1971, morgan2012, harshaw2019, bansal2010, lovett2012, li2021, weinstein2023, savje2021, zigler2018, viviano2023, chen2023, thiyageswaran2026

## section: Appendix: Proofs and Auxiliary Lemmas
The appendix contains the reduced-coordinate derivations, vertex certificates, center certificate, plus-minus-one slice characterization, weighted-simplex active-set formula, truncation correction, and rounding-gap reduction. It ends with a verification note consolidating the Lean machine-checking scope: the frozen assumptions, definitions, lemmas, and theorems are the checked mathematical layer, while literature framing and econometric motivation are prose inputs outside the formal proof graph.

objs: lem:block-spectral-coordinates, lem:cut-vertex-certificate, lem:spread-vertex-certificate, lem:frobenius-center-certificate, lem:pm-reduced-slice-characterization, lem:weighted-simplex-active-set, lem:weighted-simplex-truncation, lem:rounding-gap-reduction

bib: boyd2004, deza1997, goemans1995, thiyageswaran2026
