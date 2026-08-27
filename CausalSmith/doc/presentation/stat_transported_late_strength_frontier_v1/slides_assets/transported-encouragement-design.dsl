node source-cells | Source cells | covariates X | Z,D,Y observed
node target-cells | Target cells | covariates X | target population
node weights | Transport weights | target-to-source | uneven reweighting
node weighted-cells | Weighted cells | few carry much | target population
node moments | Transported moments | outcome contrast | μ_n first stage
node dispersion | Kish dispersion | weight dispersion | κ_n
node strength | IV strength | t_n=nμ_n²/κ_n
node effect | Target effect | complier effect θ_T
edge source-cells -> weights
edge target-cells -> weights
edge weights -> weighted-cells
edge source-cells -> moments
edge weights -> moments
edge weights -> dispersion
edge moments -> strength
edge dispersion -> strength
edge moments -> effect
