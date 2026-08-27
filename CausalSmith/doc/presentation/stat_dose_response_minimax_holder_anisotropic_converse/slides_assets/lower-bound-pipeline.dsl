node fixed-density | Fixed density | covariates frozen | treatment frozen
node local-bump | Local bump | width h near t₀ | Hölder height
node law-minus | Law minus | observed data | shared densities
node law-plus | Law plus | observed data | bumped regression
node close-laws | Close laws | statistically close
node target-shift | Target shift | θ_P(t₀) separated
node beta-obstruction | β obstruction | every fixed β
edge fixed-density -> law-minus
edge fixed-density -> law-plus
edge local-bump -> law-plus
edge law-minus -> close-laws
edge law-plus -> close-laws
edge law-minus -> target-shift
edge law-plus -> target-shift
edge fixed-density -> beta-obstruction
edge close-laws -> beta-obstruction
edge target-shift -> beta-obstruction
