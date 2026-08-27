node observations | Observations | pilot fold | evaluation fold
node residualize | Residualize | treatments Z_n
node transforms | Empirical transforms | F̂ and Ĝ
node radius | Zero radius | R₀ from separation | R₁=R₀+1
node bank | Contour bank | circles R₀ to R₁
node select | Pilot selection | winding count | lower modulus
node average | Contour average | eval Ĝ/F̂ | selected circle
node clip | Clipped midpoint | real midpoint | [−Cθ,Cθ]
edge observations -> residualize
edge residualize -> transforms
edge radius -> bank
edge bank -> select
edge transforms -> select
edge select -> average
edge transforms -> average
edge average -> clip
