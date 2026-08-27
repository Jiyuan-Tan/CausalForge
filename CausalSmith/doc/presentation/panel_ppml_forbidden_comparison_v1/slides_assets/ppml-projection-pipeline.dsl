node primitive-means | Primitive means | cohort-time means
node ppml-projection | PPML projection | fixed effects
node fitted-means | Fitted means | μ★gt(δ)
node treatment | Treatment | Dgt cells
node weights | PPML weights | qgt μ★gt(δ)
node residualized-treatment | Residualized treatment | fixed-effect residual | under PPML weights
node negative-cells | Negative cells | treated residuals
node coefficient-sign | Coefficient sign | pooled δ
edge primitive-means -> ppml-projection
edge ppml-projection -> fitted-means
edge fitted-means -> weights
edge treatment -> residualized-treatment
edge weights -> residualized-treatment
edge residualized-treatment -> negative-cells
edge negative-cells -> coefficient-sign
