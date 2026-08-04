# Revision routing plan (minor_revision)

## holistic revision (local)
- [minor·prose·rewrite] (Setup and Assumptions) The prose says the projected SNIPE estimator "clips that average to the coefficient-mass target range." Under the coefficient-mass envelope the all-treated-versus-all-control target is naturally bounded at scale 2B, while the verified coefficient-class estimator is projected to [-B,B] and the proof uses this as a scale-preserving bounded projection rather than the full target range.
- [minor·structure·rewrite] (Setup and Assumptions) The notation map is helpful, but the setup still introduces many objects in quick succession, including the prior laws, block programs, local-linear sequence, and bounded-outcome class before the reader reaches the main theorem logic.
- [minor·prose·rewrite] (Introduction / Discussion and Extensions) The comparison with Cortez-Rodriguez, Eichhorn, and Yu is directionally accurate but still compressed. The manuscript states that the present paper "sharpens" that setting, but readers would benefit from a more concrete division between the antecedent estimator/variance analysis and the present minimax, lower-bound, bounded-outcome, and local-linear contributions.
- [nit·prose·rewrite] (Main Results) Several reader-facing cross-references are wrapped in math mode, for example "Under the notation in \(\cref{obj:def:exposed-order,obj:def:minimax-risk,obj:def:model-class}\)". This is visually inconsistent with the cleveref-only cross-reference convention.
- [nit·prose·rewrite] (abstract / Main Results) The phrase "degree-one" can still be read as graph degree one because d denotes graph degree throughout the paper, even though the intended specialization is interaction order beta=1.

→ one holistic local pass; formal statements remain frozen
