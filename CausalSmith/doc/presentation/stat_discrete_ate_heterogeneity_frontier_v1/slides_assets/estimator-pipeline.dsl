node sample | Observed data
node split | Pilot split | classify cells: heavy vs light
node heavy | Heavy cells | plug-in arm contrasts
node light | Light cells | Chebyshev factorial device
node poly | Polynomial branch | heavy + light parts summed | only the light part is polynomial | u ≍ d²/(n²log²(en))
node coll | Collision branch | crossed cells, occupancy weights | h ≍ σ²+d/n²
node zero | Zero branch | constant 0, uses no data
node sel | Known-radius selector | compares u, h, 1 via σ | each branch already in [-M, M]
edge sample -> split
edge split -> heavy
edge split -> light
edge heavy -> poly
edge light -> poly
edge sample -> coll
edge poly -> sel
edge coll -> sel
edge zero -> sel
