node observed-interval | Observed interval | 0 to q
node endpoint-one | Endpoint 1 | extrapolated target
node polynomial | Polynomial control | outside [0,q]
node alternating-weights | Alternating weights | large ℓ₁ price
node oversampling | Oversampling | k ≥ cβ
node rollout-grid | Discrete rollout grid | behaves like continuous problem
node lobatto-nodes | Lobatto nodes | clustered near 0 | clustered near q
edge observed-interval -> polynomial
edge endpoint-one -> polynomial
edge polynomial -> alternating-weights
edge oversampling -> rollout-grid
edge rollout-grid -> lobatto-nodes
edge observed-interval -> lobatto-nodes
