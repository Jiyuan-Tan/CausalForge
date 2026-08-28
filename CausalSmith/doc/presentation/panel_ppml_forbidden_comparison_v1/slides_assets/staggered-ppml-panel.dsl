node cohort-2 | Cohort 2 | adopts period 2
node cohort-3 | Cohort 3 | adopts period 3
node cohort-4 | Cohort 4 | adopts period 4
node never-treated | Never treated
node untreated-mean | Untreated mean
node effects | Effects | cohort-time proportional
node observed-means | Observed means | cohort-time means
node pooled-coef | Pooled coefficient | FE-PPML
edge cohort-2 -> observed-means
edge cohort-3 -> observed-means
edge cohort-4 -> observed-means
edge never-treated -> observed-means
edge untreated-mean -> observed-means
edge effects -> observed-means
edge observed-means -> pooled-coef
