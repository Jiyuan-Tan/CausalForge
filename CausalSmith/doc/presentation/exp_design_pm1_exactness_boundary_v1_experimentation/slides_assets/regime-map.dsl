node regimes | Parameter regimes | fixed m, a, b | varying r, κ
node cut-region | Cut region | r below r_cut(m,a,b,κ)
node iid-locus | Iid locus | a+3b=2m and r=2b(a+b) | then every κ>0
node gap-window | Gap window | odd m | r between r_gap⁻ and r_gap⁺
node cut-exact | Cut design attains it | loss zero
node iid-exact | Iid design attains it | loss zero
node spread-vertex | Relaxed optimum is spread | y + z_sp = 0
node parity-floor | Parity floor | odd m forces y + z_sp ≥ 2/m
node positive-loss | Loss strictly positive | Δₘ±(r,κ) > 0
edge regimes -> cut-region
edge regimes -> iid-locus
edge regimes -> gap-window
edge cut-region -> cut-exact
edge iid-locus -> iid-exact
edge gap-window -> spread-vertex
edge gap-window -> parity-floor
edge spread-vertex -> positive-loss
edge parity-floor -> positive-loss
