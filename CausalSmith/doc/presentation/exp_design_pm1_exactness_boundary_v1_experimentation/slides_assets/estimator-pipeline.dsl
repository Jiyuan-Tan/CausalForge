node assignment-laws | Balanced sign laws | on {-1,1}^n | P(Z=z)=P(Z=-z)
node sign-design | Block-exchangeable laws | symmetry reduction
node impl-cov | X(P) | implementable covariance
node params | Parameters | u within block | v across block
node elliptope | Block elliptope | block-symmetric X(u,v) | contains the implementable set
node objective | Design objective | disagreement + pseudoinverse | Frobenius + balance
node loss | Δₘ± loss | objective gap | relaxed to implementable
edge assignment-laws -> sign-design
edge sign-design -> impl-cov
edge impl-cov -> objective
edge params -> elliptope
edge elliptope -> objective
edge objective -> loss
