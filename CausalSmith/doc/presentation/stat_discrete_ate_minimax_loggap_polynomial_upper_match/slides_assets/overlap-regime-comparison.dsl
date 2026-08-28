node fixed-overlap | Fixed overlap | interior ε
node hybrid | Hybrid estimator | ratio-polynomial
node sparse-scale | Sparse scale | sparse-cell certificate
node exact-random | Exact random | ε = 1/2
node centered | Centered estimator | centered average
node near-random | Near random | ε near 1/2
node near-scale | Near scale | 1/n + 4(1/2−ε)²
node selector | Selected envelope | better certificate
edge fixed-overlap -> hybrid
edge hybrid -> sparse-scale
edge exact-random -> centered
edge centered -> near-scale
edge near-random -> near-scale
edge sparse-scale -> selector
edge near-scale -> selector
