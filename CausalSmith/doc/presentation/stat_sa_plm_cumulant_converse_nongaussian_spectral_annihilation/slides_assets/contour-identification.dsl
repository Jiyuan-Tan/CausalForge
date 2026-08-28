node code-data | Code and data | supplied inputs
node residual | Residual Z_n | treatment code
node f-transform | F_n transform | carries zero locations
node g-transform | G_n transform | numerator information
node nuisance | Nuisance factor | zero-free inside
node contour | Contour C_j | zero-free boundary | enclosed zeros
node average | Contour average | counts zeros | averages G_n/F_n
node estimate | Estimate θ₀ | identified coefficient
edge code-data -> residual
edge code-data -> g-transform
edge residual -> f-transform
edge residual -> g-transform
edge f-transform -> contour
edge nuisance -> contour
edge f-transform -> average
edge g-transform -> average
edge contour -> average
edge average -> estimate
