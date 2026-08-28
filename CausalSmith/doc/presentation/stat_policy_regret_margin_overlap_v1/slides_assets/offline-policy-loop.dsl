node offline-observations | Offline observations | X, A, bounded Y
node nuisance-estimates | Nuisance estimates
node clipped-aipw-scores | Clipped AIPW scores
node empirical-welfare | Empirical welfare | maximization
node learned-policy | Learned policy | deterministic
node welfare-regret | Welfare regret
edge offline-observations -> nuisance-estimates
edge nuisance-estimates -> clipped-aipw-scores
edge clipped-aipw-scores -> empirical-welfare
edge empirical-welfare -> learned-policy
edge learned-policy -> welfare-regret
