node active-units | Active units | partitioned units
node directed-blocks | Directed blocks | complete d-blocks | arrows incl loops
node representer | Representer | normalized block | target vs energy
node signed-priors | Signed priors | opposite directions | same amount
node hellinger | Hellinger | calibrated by A_d/m | close experiments
node lower-bound | Lower bound | claimed separation | statistically close
node clipped-snipe | Clipped SNIPE | upper bound
node match | Minimax match | lower and upper
edge active-units -> directed-blocks
edge directed-blocks -> representer
edge representer -> signed-priors
edge representer -> hellinger
edge signed-priors -> hellinger
edge signed-priors -> lower-bound
edge hellinger -> lower-bound
edge lower-bound -> match
edge clipped-snipe -> match
