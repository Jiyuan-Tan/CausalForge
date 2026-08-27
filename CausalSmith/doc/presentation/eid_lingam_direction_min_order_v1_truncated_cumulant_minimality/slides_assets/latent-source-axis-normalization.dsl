node fwd-direct | Direct slot (1, γ) | free slope
node fwd-middle | m middle slots (1, ρ_j) | free slopes
node fwd-axis | Vertical-axis slot (0, 1) | fixed, loads Y only
node rev-axis | Horizontal-axis slot (1, 0) | fixed, loads X only
node rev-middle | m middle slots (σ_j, 1) | free slopes
node rev-direct | Direct slot (δ, 1) | free slope
node fwd | Forward representation | tagged X→Y
node rev | Reverse representation | tagged Y→X
node cumulants | Truncated cumulant vector | can the two agree?
edge fwd-direct -> fwd
edge fwd-middle -> fwd
edge fwd-axis -> fwd
edge rev-axis -> rev
edge rev-middle -> rev
edge rev-direct -> rev
edge fwd -> cumulants
edge rev -> cumulants
