# Holistic revision pass 1

- mode: reframe
- source digest before: `b95adb3511712c47cf05ef19440c6bf5ca7254247677880421fb5bf822137019`
- source digest after: `0d08b34e5ca18eafcba69f1f613eb32792a0c8e3f9c66664c5df779918cd07da`

## Reviser report

Implemented the rewrite pass in the authored sources.

Changed:
- Consolidated the duplicate introduction roadmap into one paragraph and added the updated Lean/no-external-formal-dependency scope: [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/front_matter.tex:65)
- Reframed the local-linear benchmark affirmatively: [sections/04_discussion_and_extensions.tex](<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/04_discussion_and_extensions.tex:21)
- Updated the active verification note to state displayed statements/proofs are Lean-verified with no external formal dependencies, while citations supply framing/positioning: [sections/06_appendix_verification_note.tex](<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/06_appendix_verification_note.tex:5)
- Normalized several older authored section headings to sentence case and updated the older verification-note source similarly.

Verification run:
- Routed stale/negative-roadmap phrase scan over authored sources: clean.
- Legacy `\ref`, `\eqref`, `\autoref` scan over authored sources: clean.
- `npx tsx bin/check_paper_indexes.ts --strict --no-vs --bundle exp_snipe_degree_frontier_v1`: passed.

Residual/declined:
- The stale author footnote is only present in derived `paper.tex` and in pipeline code outside the editable manuscript-source list. I left `paper.tex` untouched per the hard boundary. It should be fixed by the reassembly/pipeline layer or its template source, not by this authored-source revision pass.
