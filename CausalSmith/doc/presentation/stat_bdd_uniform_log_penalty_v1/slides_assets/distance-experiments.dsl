node boundary-point | Boundary point | x on interface
node observations | Nearby observations | around x
node side-label | Treatment side | known side label
node border-geometry | Border geometry | known interface
node unsigned | Unsigned distance | how far from x | side forgotten
node signed | Signed distance | sign by side | geometry used
node loss | Supremum loss | over boundary | μ_P unsigned, τ_P signed
edge boundary-point -> observations
edge observations -> unsigned
edge observations -> signed
edge boundary-point -> unsigned
edge boundary-point -> signed
edge side-label -> signed
edge border-geometry -> signed
edge unsigned -> loss
edge signed -> loss
