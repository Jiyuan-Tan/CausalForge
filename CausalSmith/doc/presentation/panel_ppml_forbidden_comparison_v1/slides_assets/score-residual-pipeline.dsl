node treated-means | Treated means | heterogeneous effects | observed cells
node ppml-fit | PPML FE fit | balances observed/fitted | cohort/time margins
node fitted-weights | Fitted weights | fitted mean weights
node residual-cells | Residual cells | treatment cells | residualized
node score-comparison | Score comparison | fitted-weighted | residual contrasts
node pooled-sign | Pooled sign | coefficient sign | may lower
edge treated-means -> ppml-fit
edge treated-means -> residual-cells
edge ppml-fit -> fitted-weights
edge ppml-fit -> residual-cells
edge fitted-weights -> score-comparison
edge residual-cells -> score-comparison
edge score-comparison -> pooled-sign
