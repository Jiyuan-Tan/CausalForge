node interventions | Iₙ | intervention-unit set
node outcomes | Oₙ | outcome-unit set
node bipartite-graph | Gₙ | known bipartite graph | affects each outcome
node neighborhoods | Nᵢ(Gₙ) | intervention assignments | enter outcome i
node shared | Shared neighborhoods | at least one intervention
node overlap-graph | Outcome overlap | induced graph | statistically linked
edge interventions -> bipartite-graph
edge outcomes -> bipartite-graph
edge bipartite-graph -> neighborhoods
edge neighborhoods -> shared
edge outcomes -> overlap-graph
edge shared -> overlap-graph
