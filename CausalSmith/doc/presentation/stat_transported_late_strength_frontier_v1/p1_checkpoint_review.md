# P1 checkpoint review — 2026-08-02

Decision: approved by the authorized presentation orchestrator.

## Outline and coverage

- Reviewed the title, contribution statement, notation table, seven-section order, per-section briefs, formal-object placement, and bibliography assignments in `outline.md`.
- Parsed all 44 frozen formal blocks. Every block is assigned to exactly one outline section; there are no missing, unknown, or duplicate object IDs.
- Parsed 48 kept bibliography entries. All outline citation keys resolve, and there are no duplicate keys.

## Formal layer and freeze

- Parsed `formal_layer.json` against the presentation schema: 44 blocks, all environment-bearing.
- Recomputed every whitespace-normalized SHA-256 `body_hash`; all 44 match.
- Re-derived the environment text from `formal_layer.json` and compared it with `formal_layer.tex`; the two views match exactly.
- Read the P1 statement-audit result and graph drift log. The audit reports every frozen Lean-linked statement faithful after the recorded refinements, with no hard-gate failure.

## Notation-resolvability scan

- Scanned the outline notation table and every frozen environment for custom named operators and predicates, including all `\mathrm{...}`, `\operatorname{...}`, `\mathsf{...}`, and `\textsf{...}` forms.
- The custom total-variation operator has exactly one defining environment (`synth_4`), and the chi-square divergence has exactly one defining environment (`synth_3`). Their later joint use in `def:geometry-handle` initially lacked anchors; I added `\cref{obj:synth_3,obj:synth_4}` and re-pinned that block's hash.
- The frontier-risk functional has exactly one defining environment (`def:frontier-risk`). Its later use in `thm:oracle-score-inversion-attainment` initially lacked an anchor; I added `\cref{obj:def:frontier-risk}`. I also anchored that theorem's repeated score construction to `def:inversion-handle` and re-pinned the theorem hash.
- The remaining notation-review advisory about `def:fixed-geometry-value` is graph-only: `thm:oracle-score-inversion-attainment` neither displays nor claims the fixed-geometry value, so there is no unresolved symbol use to anchor there.
- Re-ran the freeze and derived-view checks after these repairs; there is no unresolved custom operator or predicate.

## Bibliography

- Compared the 49 raw entries with the 48 kept entries and `p0_verification.json`: 42 exact, six minor metadata caveats, and one major drop (`Kish1965`).
- Manually inspected the six minor entries and their persistent DOI-bearing records. The reported differences are punctuation/subtitle or author-normalization caveats, not identity ambiguity; all six are usable and remain traceable by DOI.
- Confirmed that the dropped Kish entry is not referenced by the outline.

