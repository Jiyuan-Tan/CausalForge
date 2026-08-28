node latent-sources | Latent sources | cumulant weights
node loadings | Loadings | loading vectors
node forward-map | Forward map | polynomial cumulants
node reverse-map | Reverse map | polynomial cumulants
node truncated-vector | T_L(P) | orders 2 through L
node forward-fiber | Forward fiber | same T_L(P)
node reverse-fiber | Reverse fiber | same T_L(P)
node separation | Direction separation | reverse fiber empty
edge latent-sources -> forward-map
edge loadings -> forward-map
edge latent-sources -> reverse-map
edge loadings -> reverse-map
edge forward-map -> truncated-vector
edge truncated-vector -> forward-fiber
edge forward-map -> forward-fiber
edge truncated-vector -> reverse-fiber
edge reverse-map -> reverse-fiber
edge reverse-fiber -> separation
