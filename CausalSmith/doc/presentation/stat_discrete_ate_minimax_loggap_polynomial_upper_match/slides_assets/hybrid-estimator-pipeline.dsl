node sample | Sample | observed units
node split | Half split | pilot half | estimation half
node pilot-half | Pilot half | category counts
node estimation-half | Estimation half | second-half counts
node classifier | Classifier | pilot count > threshold | threshold ≍ log n
node heavy-estimate | Heavy estimate | empirical treatment-control ratios
node light-estimate | Light estimate | Chebyshev degree ≍ log n | falling-factorial moments
node clipped-ate | Clipped ATE | final estimate
edge sample -> split
edge split -> pilot-half
edge split -> estimation-half
edge pilot-half -> classifier
edge classifier -> heavy-estimate
edge classifier -> light-estimate
edge estimation-half -> heavy-estimate
edge estimation-half -> light-estimate
edge heavy-estimate -> clipped-ate
edge light-estimate -> clipped-ate
