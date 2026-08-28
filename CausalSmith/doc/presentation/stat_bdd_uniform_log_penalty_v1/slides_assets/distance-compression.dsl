node bivariate-observations | Bivariate observations | locations and outcomes
node unsigned-distances | Unsigned distances | from query point | outcomes retained
node angular-location | Angular location | forgotten around point
node treatment-side | Treatment side | forgotten by unsigned
node boundary-estimate | Boundary regression | estimate whole curve
node uniform-penalty | Uniform penalty | testing over curve | scale aₙ
edge bivariate-observations -> unsigned-distances
edge unsigned-distances -> angular-location
edge unsigned-distances -> treatment-side
edge unsigned-distances -> boundary-estimate
edge boundary-estimate -> uniform-penalty
