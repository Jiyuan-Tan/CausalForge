node cumulant-blocks | Cumulant blocks | retained orders up to 2m+2 | binary forms
node apolar-recovery | Apolar equations | common annihilator | generic locus
node loading-support | Loading-direction support | unordered, m+2 directions
node forward-signature | Forward signature | vertical-axis direction present
node reverse-signature | Reverse signature | horizontal-axis direction present
node incompatible | Signatures cannot coincide | axis slots stay distinguished
node arrow-separation | Opposite-arrow fiber empty | separation at representation level
edge cumulant-blocks -> apolar-recovery
edge apolar-recovery -> loading-support
edge loading-support -> forward-signature
edge loading-support -> reverse-signature
edge forward-signature -> incompatible
edge reverse-signature -> incompatible
edge incompatible -> arrow-separation
