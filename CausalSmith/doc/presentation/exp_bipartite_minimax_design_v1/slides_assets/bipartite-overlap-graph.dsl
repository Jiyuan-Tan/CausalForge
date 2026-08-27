node intervention-units | Intervention units | I_n
node outcome-units | Outcome units | O_n
node known-graph | Known graph | G_n
node neighborhoods | Neighborhoods | N_i(G_n) | d_i exposures
node incidences | Incidence counts | s_k outcomes
node shared-neighbors | Shared neighbors | S_ij(G_n)
node overlap-graph | Overlap graph | outcomes share k
node dependence-bound | Dependence bound | Δ_n exposure terms
edge intervention-units -> known-graph
edge outcome-units -> known-graph
edge known-graph -> neighborhoods
edge known-graph -> incidences
edge neighborhoods -> shared-neighbors
edge shared-neighbors -> overlap-graph
edge overlap-graph -> dependence-bound
