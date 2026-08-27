node cohorts | Four cohorts | 2, 3, 4 | never-treated
node periods | Four periods | periods 1–4
node grid | Cohort rows | four rows | four periods
node adoption | First treated | periods 2, 3, 4 | never-treated
node shaded-cells | Treated cells | shaded after adoption | positive effects
node late-cell | Late cell | cohort 2, period 4 | largest effect
node assumptions | Flat means | equal shares
node ppml-sign | PPML sign | pooled fixed effects | treatment?
edge cohorts -> grid
edge periods -> grid
edge adoption -> shaded-cells
edge grid -> shaded-cells
edge shaded-cells -> late-cell
edge shaded-cells -> ppml-sign
edge late-cell -> ppml-sign
edge assumptions -> ppml-sign
