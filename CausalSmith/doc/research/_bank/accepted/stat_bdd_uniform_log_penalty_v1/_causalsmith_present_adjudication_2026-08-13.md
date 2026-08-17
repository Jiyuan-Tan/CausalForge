# PRESENT semantic adjudication — 2026-08-13

The P3 rubric failure was routed to a scoped PRESENT P1/P2 revision, not to a
research-stage rewind. The accepted mathematics and Lean declarations remain
unchanged.

- Removed the redundant presentation-only kernel and admissible-geometry
  environments. The Lean-backed kernel and known-geometry environments are the
  canonical homes; the latter now also introduces the generic admissible tuple
  used by the decision class.
- Replaced the duplicate presentation-only common-map definition with the
  explicit alias \(\mathcal T:=\mathcal T_n^{\mathrm{NP}}\), leaving the
  Lean-backed sample-size-indexed decision class canonical.
- Reused the outer-expectation definition in
  def:point-indexed-distance-risk from the signed-distance risk environment;
  the signed-distance risk formula itself is unchanged.
- Added the numbered presentation environment synth_139, which states the
  three explicit Lean theorem antecedents—CTY distance identification, uniform
  first-order bias, and expected maximal bounds—and labels them as assumptions
  not proved in this paper.
- Routed only related literature, the affected setup, main results, discussion,
  and front matter for redrafting. Existing proof artifacts remain authoritative
  and must be reused subject to the normal proof audit.

This adjudication changes presentation ownership, self-containment, and scope
signposting only. It does not strengthen, weaken, or replace any accepted
theorem.
