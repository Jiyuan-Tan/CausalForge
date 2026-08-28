node common-covariate-law | Common covariate law | P_X on [0,1]
node active-block | Active block | B_n | small contrast region
node weak-treatment-arm | Weak treatment arm | A=1 on B_n | sampled q_n
node off-block | Off block | same positive contrast | common label 1
node sign-positive-law | Sign-positive law | τ=+h_n on B_n
node sign-negative-law | Sign-negative law | τ=−h_n on B_n
node oracle-policy-choice | Oracle policy choice | infer correct sign | rare low-signal obs
edge common-covariate-law -> active-block
edge active-block -> weak-treatment-arm
edge weak-treatment-arm -> sign-positive-law
edge weak-treatment-arm -> sign-negative-law
edge off-block -> sign-positive-law
edge off-block -> sign-negative-law
edge sign-positive-law -> oracle-policy-choice
edge sign-negative-law -> oracle-policy-choice
