# Presentation adjudication — 2026-08-21 (pipeline re-run)

Re-ran `present exp_snipe_degree_frontier v1 --from P1 --refresh-frozen-bodies` to carry the
2026-08-18..21 pipeline improvements into the 2026-08-17 bundle. P1 halted twice on
`notation-reviewer` findings routed to `halt` — Lean-realized symbols with no editable
designated home (`p1_plan.ts:360`). All repairs are in the BUNDLE's `outline.md`
(backup `outline.md.bak`); the bank graph and the accepted note are untouched.

## Root cause

The regenerated outline listed thirteen symbols on its `notation_gaps:` line instead of
assigning each a home environment. Every one is realized in the run's Lean, and the router
refuses to synthesize a presentation-only definition that would compete with a Lean-backed
authority, so it halts rather than inventing content. The 2026-08-17 bundle carried the same
gap list; the older pipeline synthesized four standalone micro-definitions and shipped the
remaining symbols undefined.

Underneath that sat a genuine placement defect: three MAIN-BODY theorems
(`thm:degree-frontier`, `thm:bounded-outcome-degree-frontier`,
`thm:sharp-local-linear-constant-and-representers`) use `\delta`, `\rho`, `U_b`, `V_{n_t}`
and `b(i)` in their STATEMENTS, while every definition of those objects sat in the appendix.
`thm:degree-frontier` said "let \(\delta\) be the least-favourable perturbation amplitude"
with no anchor anywhere before it. The P1 placement lint did not catch this: it inspects
`statement-uses` graph edges, and those point at hidden `aux_*` Lean defs rather than at the
paper environments.

## Edits to `outline.md`

1. Moved `def:block-family`, `def:local-linear-class`, `def:local-linear-estimator-class`
   and `def:local-linear-risk` from the appendix section into the setup section, so the
   objects the main theorems name are defined in the main body (2026-08-21 user directive).
   Adjusted the two affected section descriptions to match.
2. Added notation-table homes for every Lean-realized symbol used in the layer that lacked
   one: `V_n`, `P_Z`, `\mathbb E_Z` -> `ass:bernoulli-design`; `N_i` -> `ass:bounded-degree`;
   `Y_i(z)` -> `ass:low-order`; `\Delta_r(p)`, `\bar\beta_d`, `k_\star` -> `def:exposed-order`;
   `G_n` -> `def:graph-class`; `\tau_n` -> `def:model-class`;
   `g_{i,\beta,p}`, `A_i` -> `def:snipe-score`;
   `Y_i^{\mathrm{obs}}`, `\widehat\tau_n` -> `def:snipe-estimator`;
   `g_d`, `h_d` -> `def:block-score-energy`;
   `f_s`, `\delta`, `\delta(n,d,\beta,B,p)`, `\rho`, `U_b`, `\sigma`, `\Pi_\sigma`
   -> `def:block-family`; `\mathcal P_d`, `L_d` -> `def:perturbation-program`;
   `N_i^{G_t}`, `V_{n_t}`, `G_t`, `n_t` -> `def:local-linear-class`;
   `b(i)`, `Z_{b(i)}` -> `def:local-linear-estimator-class`;
   `c_{\beta,p}`, `C_{\beta,p}` -> `thm:degree-frontier`;
   `\Psi_{b,t}` -> `thm:sharp-local-linear-constant-and-representers`.
3. Trimmed the now-homed entries from `notation_gaps:`; only `L^2(P_Z)` remains, which has
   no Lean realization and legitimately routes to synthesis.

## Verification before re-entry

Checked through the pipeline's own `discoverRealizedSymbols` / `notationHomes` /
`definingNotationKey` / `containsNotation`, against the rendered `formal_layer.json`:

- multi-character Lean-realized symbols used in the layer but unhomed: **0** (was 36)
- notation homes that do not precede every use of their symbol: **0** (was 4)
- 86 homes; outline validates and is reused, not regenerated; all 29 renders cache-hit.

## Method note

The first repair pass fixed only the eleven symbols the reviewer named, and the next run
halted on two more it had not previously reported. The reviewer surfaces a subset per pass,
so patching per-finding does not converge; enumerating the realized-symbol set directly and
closing it in one pass does.
