# Substrate requirement: ehlich_zeller_mesh

## Goal
The Ehlich–Zeller Chebyshev-Lobatto mesh/norming inequality: a real polynomial of degree ≤ β is uniformly controlled on [-1,1] by its values on the (k+1) Chebyshev-Lobatto nodes whenever the mesh is oversampled (β < k), with a norming constant depending only on the oversampling ratio.

## Provides (API contract)
- `ehlichZeller_mesh_bound` (or similarly named): for a real polynomial `R` of degree ≤ `β` and integer `k` with `β < k`,
  `sSup {|R x| : x ∈ [-1,1]} ≤ (1 / Real.cos (π * β / (2 * k))) * (⨆ j ∈ Finset.range (k+1), |R (-Real.cos (π * j / k))|)`.
- A corollary in the "oversampling ratio" form: for `c > 1`, `β ≥ 1`, integer `k ≥ c·β`, the norming constant `K(c) = 1 / Real.cos (π / (2*c))` works (uses `β/k ≤ 1/c` and monotonicity of `sec` on `[0, π/2)`).

## Statement / milestones
Let `R : ℝ[X]` (or a real polynomial function) with `R.natDegree ≤ β`, and `k : ℕ` with `β < k`. Nodes: `x_j = -cos(π j / k)`, `j = 0..k` (these are the Chebyshev-Lobatto / extrema points; note x_0 = -1, x_k = 1 are always nodes). Then
    sup_{x ∈ [-1,1]} |R(x)| ≤ sec(π β / (2k)) · max_{0 ≤ j ≤ k} |R(x_j)|.
Proof route (Bernstein / arccos-speed argument):
1. Put `Q(t) = R(-cos t)`. Then `Q` is a real EVEN trigonometric polynomial of degree ≤ β on `[0, π]`, and `sup_{x∈[-1,1]} |R(x)| = sup_{t∈[0,π]} |Q(t)|`.
2. Let `M = sup_{[0,π]} |Q|`, `S = max_j |Q(π j / k)|`. WLOG `M > 0`; pick `t₀` with `Q(t₀) = M` (replace `Q` by `-Q` if needed). Pick node `j` with `|t₀ − π j / k| ≤ π/(2k)`.
3. Bernstein differential inequality for the normalized trig polynomial `U = Q/M` of degree β: `|U'(t)| ≤ β · √(1 − U(t)²)` wherever `|U(t)| < 1`. Hence `d/dt arccos(U(t)) ` has magnitude ≤ β, so `arccos U` is `β`-Lipschitz.
4. Since `U(t₀) = 1` (arccos 0), `arccos U(π j / k) ≤ β · |t₀ − π j / k| ≤ π β / (2k) < π/2` (as `β < k`). Monotonicity of cos gives `U(π j / k) ≥ cos(π β / (2k))`, i.e. `S ≥ |Q(π j/k)| ≥ M cos(π β/(2k))`, so `M ≤ sec(π β/(2k)) · S`. ∎

If Bernstein's inequality for trigonometric polynomials is available in Mathlib, use it directly. If not, the cleanest alternative is the Chebyshev-polynomial extremal route (Rakhmanov / Coppersmith–Rivlin form) — decide which is more tractable in Mathlib and take it; the deliverable is the mesh bound with a `sec`-type constant, however proved.

## Standard reference
Ehlich, H. & Zeller, K. (1964), "Schwankung von Polynomen zwischen Gitterpunkten", Mathematische Zeitschrift 86, 41–44. Also standard as a Marcinkiewicz–Zygmund / polynomial-mesh (norming-set) inequality; see also Rivlin, "The Chebyshev Polynomials" (1974).

## Intended reuse
Discharges the substrate-gate `lem:ehlich-zeller-chebyshev-lobatto-mesh` of CausalSmith research run `exp_rollout_chebyshev_minimax` / `tv_envelope_rollout_design`. It is consumed by `lem:oversampled-chebyshev-lobatto-norming` (which specializes it to k ≥ cβ to get a β-uniform constant K(c)) and thereby by the headline `thm:chebyshev-minimax`'s upper bound. Needs the general-polynomial, general-(β,k) statement (NOT gerrymandered to rollout objects) so it is reusable and Mathlib-shaped.

## May assume / must derive
- MAY assume standard Mathlib real-analysis / trigonometry (cos monotonicity, arccos, `Real.cos`, derivatives, `Polynomial.natDegree`, Chebyshev polynomials `Polynomial.Chebyshev.T`).
- MUST derive: the mesh/norming inequality itself and the `sec(π/(2c))` corollary. Bernstein's trig inequality: if present in Mathlib, cite/use it; if ABSENT, either prove the needed special case honestly or switch to the Chebyshev-extremal route — do NOT assume it as an unproven axiom/`sorry`.

## Non-goals (optional)
Sharpness of the constant is not required (any finite `sec`-type / oversampling-ratio constant suffices). Complex polynomials, weighted meshes, and the general Marcinkiewicz–Zygmund `L^p` theory are out of scope.

## Known building blocks (optional)
- `Polynomial.Chebyshev.T` and its trig identity `T_n (cos θ) = cos (n θ)`.
- Real trigonometry: `Real.cos`, `Real.arccos`, monotonicity/derivative lemmas.
- Search Mathlib for existing Bernstein/Markov polynomial inequalities and any norming-set / mesh results before building from scratch.

## Target module (optional)
`Causalean.Mathlib.Analysis.EhlichZellerMesh`
