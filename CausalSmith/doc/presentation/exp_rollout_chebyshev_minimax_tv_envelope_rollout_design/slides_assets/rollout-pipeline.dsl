node no-adoption | No adoption | rollout fraction 0
node rounds | Measurement rounds | along rollout path | before budget q
node budget | Budget q | rollout stops before | universal adoption
node spillovers | Spillovers | partial adoption | moves outcomes
node extrapolation | Extrapolation | from 0 through q | to target 1
node full-adoption | Full adoption | target fraction 1
node contrast | Endpoint contrast | no vs full | adoption
edge no-adoption -> rounds
edge rounds -> budget
edge rounds -> spillovers
edge budget -> extrapolation
edge spillovers -> extrapolation
edge extrapolation -> full-adoption
edge no-adoption -> contrast
edge full-adoption -> contrast
