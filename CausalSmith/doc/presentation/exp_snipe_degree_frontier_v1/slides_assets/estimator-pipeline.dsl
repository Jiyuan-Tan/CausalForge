node observed-outcomes | Observed outcomes | Y_i obs
node neighborhoods | Known neighborhoods | exposed order
node centered-scores | Centered scores | Bernoulli monomials | centered score
node score-energy | Score energy | A_d design moment | d-coordinate score
node weighted-average | Weighted average | SNIPE estimate | estimates τ_n
node projection | Projection | clip target range | [-B,B] or [-2B,2B]
node mse-question | MSE question | improve MSE scale
edge neighborhoods -> centered-scores
edge centered-scores -> score-energy
edge observed-outcomes -> weighted-average
edge centered-scores -> weighted-average
edge weighted-average -> projection
edge projection -> mse-question
