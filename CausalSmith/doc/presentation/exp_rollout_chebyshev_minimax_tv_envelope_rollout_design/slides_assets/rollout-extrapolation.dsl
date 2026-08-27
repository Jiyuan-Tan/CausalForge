node rollout-axis | Rollout axis | fractions 0 to q | target 1 outside
node budget | Budget q | fixes p_k=q
node schedule | Schedule p | chosen before outcomes | p₀,…,p_k
node round-means | Round means | mean at each p_j | measurement rounds
node weights | Unbiased weights w_j | set W_β(p) fixed by schedule
node estimator | Linear estimator | weighted round means | extrapolates to 1
node design-question | Design question | unbiased extrapolation | least variable
edge budget -> schedule
edge schedule -> weights
edge schedule -> round-means
edge round-means -> estimator
edge weights -> estimator
edge rollout-axis -> design-question
edge schedule -> design-question
edge estimator -> design-question
