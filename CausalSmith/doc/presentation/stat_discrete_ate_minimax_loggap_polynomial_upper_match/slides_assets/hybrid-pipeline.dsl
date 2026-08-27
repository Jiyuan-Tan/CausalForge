node sample-split | Split sample | pilot and estimation
node pilot | Pilot classify | counts above | log threshold
node heavy | Heavy categories | pilot-certified | stable ratios
node ratio | Ratio estimate | empirical treatment-control
node light | Light categories | too sparse | direct ratios
node poly | Chebyshev poly | reciprocal ratio | degree M(n)
node moments | Factorial moments | monomials to | count statistic
node aggregate | Hybrid τ̂ₙ | add contributions | clip ATE range
edge sample-split -> pilot
edge sample-split -> ratio
edge sample-split -> moments
edge pilot -> heavy
edge pilot -> light
edge heavy -> ratio
edge light -> poly
edge poly -> moments
edge ratio -> aggregate
edge moments -> aggregate
