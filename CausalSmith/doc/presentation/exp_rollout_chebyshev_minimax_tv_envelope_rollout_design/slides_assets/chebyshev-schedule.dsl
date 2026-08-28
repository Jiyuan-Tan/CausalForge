node interval | Budget interval | 0 to q | observed range
node nodes | Lobatto nodes | shifted Chebyshev | endpoint-dense
node schedule | Schedule | pᶜʰ_j(k,q) | more end rounds
node oversampling | Oversampling | k ≥ cβ | discrete control
node weights | Unbiased weights | construction | from measurements
node extrapolation | Extrapolation | endpoint to 1 | polynomial target
node amplification | Minimax amplification | base ((1+√(1−q))²/q) | exponent 2β
edge interval -> nodes
edge nodes -> schedule
edge oversampling -> schedule
edge schedule -> weights
edge weights -> extrapolation
edge schedule -> amplification
edge oversampling -> amplification
edge extrapolation -> amplification
