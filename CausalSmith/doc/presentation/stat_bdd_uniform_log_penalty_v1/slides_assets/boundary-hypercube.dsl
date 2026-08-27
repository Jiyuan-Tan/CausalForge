node square-support | Square support | boundary locations
node boundary-cells | Boundary cells | many separated
node binary-bits | Binary bits | one per cell
node regression-gap | Value gap | differs ≍ aₙ
node matched-radius | Matched radius | at query point
node unsigned-distance | Unsigned distance | radial kept | angular washed out
node local-decoding | Local decoding | many weak bits
node logarithm | Logarithm | coordinate testing
edge square-support -> boundary-cells
edge boundary-cells -> binary-bits
edge binary-bits -> regression-gap
edge binary-bits -> matched-radius
edge matched-radius -> unsigned-distance
edge regression-gap -> local-decoding
edge unsigned-distance -> local-decoding
edge local-decoding -> logarithm
