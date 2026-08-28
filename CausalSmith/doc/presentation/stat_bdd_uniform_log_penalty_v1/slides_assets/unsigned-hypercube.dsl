node boundary-cells | Boundary cells | separated support boundary | changes order aₙ
node hidden-bits | Hidden bits | binary perturbations | local boundary values
node distance-observations | Distance obs | unsigned scalar distances | reveal little
node sup-loss | Sup-loss | uniform over cells | logarithm contribution
node scale-calculation | Scale calc | M≍Δ⁻¹/q, w²≍Δ²/q | information nΔ⁴
node balancing | Balancing | nΔ⁴≍log M | Δ≍(log n/n)¹/4
node decoding | Decoding | difficulty | lower-bound scale
edge boundary-cells -> hidden-bits
edge hidden-bits -> distance-observations
edge boundary-cells -> sup-loss
edge boundary-cells -> scale-calculation
edge sup-loss -> balancing
edge scale-calculation -> balancing
edge distance-observations -> decoding
edge balancing -> decoding
