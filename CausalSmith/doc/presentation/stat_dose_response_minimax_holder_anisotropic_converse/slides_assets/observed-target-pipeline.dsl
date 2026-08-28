node observed-data | Observed data | O=(Y,A,X)
node regression | Regression | μ_P(a,x) | conditional mean
node target-dose | Target dose | interior t₀
node evaluation | Evaluation | μ_P(t₀,X)
node covariates | Covariates | population distribution
node target | Target mean | θ_P(t₀) | averages over X
node assumptions | Assumptions | consistency, no confounding | local positivity
node causal | Interpretation | causal dose-response
edge observed-data -> regression
edge regression -> evaluation
edge target-dose -> evaluation
edge evaluation -> target
edge covariates -> target
edge target -> causal
edge assumptions -> causal
