node target-sample | Target sample | covariate cell labels
node cell-frequencies | Cell frequencies | target empirical probabilities
node collision-statistic | Collision statistic | weight-dispersion scale
node source-sample | Source sample | outcome receipt encouragement
node cellwise-contrasts | IV contrasts | outcome contrast | receipt contrast
node transported-estimates | Transported estimates | reduced form | first stage
node score-inversion | Score inversion | confidence set
edge target-sample -> cell-frequencies
edge target-sample -> collision-statistic
edge source-sample -> cellwise-contrasts
edge cell-frequencies -> transported-estimates
edge cellwise-contrasts -> transported-estimates
edge transported-estimates -> score-inversion
edge collision-statistic -> score-inversion
