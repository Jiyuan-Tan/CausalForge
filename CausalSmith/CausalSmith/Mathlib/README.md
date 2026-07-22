Staging folder for Mathlib-shaped helper lemmas produced by the CausalSmith research F2
scaffolder. Each file in this folder must be **pure Mathlib types** — no
references to CausalSmith- or Causalean-cluster symbols (no `Cells`, `tildeX`,
`POManskiIVSystem`, `Backdoor`, etc.). Promotion to `Causalean/Mathlib/` is a
separate human step gated on (a) ≥2 independent call sites or a fully general
statement, and (b) no CausalSmith-specific dependencies; see the project
CLAUDE.md "Mathlib helper staging" section.
