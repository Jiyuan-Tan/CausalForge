node categories | Categories | covariate cells
node mass | Category mass | sum weights
node treated-mean | Treated mean | categorywise
node control-mean | Control mean | categorywise
node contrast | Contrast | treated − control
node target-sum | Target sum | over categories
node ate-target | ATE target | τ(P)
edge categories -> mass
edge categories -> treated-mean
edge categories -> control-mean
edge treated-mean -> contrast
edge control-mean -> contrast
edge mass -> target-sum
edge contrast -> target-sum
edge target-sum -> ate-target
