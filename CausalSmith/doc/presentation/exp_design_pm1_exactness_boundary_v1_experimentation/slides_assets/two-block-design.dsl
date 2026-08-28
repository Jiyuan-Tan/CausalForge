node community-a | Community A | units A_m
node community-b | Community B | units B_m
node within | Within-block | exposure a/m
node across | Across-block | exposure b/m
node signs | Randomized signs | Z ∈ {±1}
node objective | Design objective | randomize treatment signs | follows graph
edge community-a -> within
edge community-b -> within
edge community-a -> across
edge community-b -> across
edge within -> objective
edge across -> objective
edge signs -> objective
