node axis-x-shocks | Axis shocks | load mainly X | non-Gaussian
node middle-slots | Middle slots | m source slots | load on both
node axis-y-shocks | Axis shocks | load mainly Y | non-Gaussian
node x | X | observed outcome
node y | Y | observed outcome
node maintained | Maintained inputs | m and axis norm
node x-to-y | X → Y | same source slots
node y-to-x | Y → X | same source slots
edge axis-x-shocks -> x
edge middle-slots -> x
edge middle-slots -> y
edge axis-y-shocks -> y
edge x -> x-to-y
edge y -> x-to-y
edge maintained -> x-to-y
edge x -> y-to-x
edge y -> y-to-x
edge maintained -> y-to-x
