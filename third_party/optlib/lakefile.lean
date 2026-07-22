import Lake
open Lake DSL

/-!
Vendored, adapted copy of `optsuite/optlib` (Apache-2.0), carried in-tree and
bumped to AutoID's Lean/Mathlib pin. Only the KKT dependency closure is vendored
(Convex/{ConicCaratheodory,ClosedCone,Farkas}, Differential/{Calculation,Lemmas},
Optimality/Constrained_Problem). See `UPSTREAM.md` for provenance.

AutoID's strict style linters (longLine, cdot, …) are intentionally NOT enabled
here: this is upstream third-party source we adapt only for toolchain drift, not
for house style.
-/

package «optlib» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "bf8875c7dc7162b23cdb881f33cc97caab1c688a"

@[default_target]
lean_lib «Optlib» where
