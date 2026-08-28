node cohort-2 | Cohort 2 | adopts at date 2
node cohort-3 | Cohort 3 | adopts at date 3
node cohort-4 | Cohort 4 | adopts at date 4
node never-treated | Never-treated | no adoption
node cells-2 | Treated cells | cohort 2 periods
node cells-3 | Treated cells | cohort 3 periods
node cells-4 | Treated cells | cohort 4 periods
node pooled-ppml | Pooled PPML | one coefficient
edge cohort-2 -> cells-2
edge cohort-3 -> cells-3
edge cohort-4 -> cells-4
edge cells-2 -> pooled-ppml
edge cells-3 -> pooled-ppml
edge cells-4 -> pooled-ppml
edge never-treated -> pooled-ppml
