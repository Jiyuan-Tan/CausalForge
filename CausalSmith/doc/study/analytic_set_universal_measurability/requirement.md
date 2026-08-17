# Substrate requirement: analytic_set_universal_measurability

## Goal

Formalize the classical theorem that analytic subsets of Polish Borel spaces are measurable in the completion of every finite Borel measure.

## Provides (API contract)

- `MeasureTheory.AnalyticSet.nullMeasurableSet`: if `s : Set Ω` is analytic, `Ω` is a Polish space with its Borel measurable structure, and `μ` is a finite measure, then `NullMeasurableSet s μ`.
- A narrowly scoped compatibility lemma showing that an upper-semi-analytic extended-nonnegative function is measurable for `μ.completion`, sufficient to identify its completed `lintegral` with the corresponding outer integral when this follows cheaply from the set theorem.

Names may change to fit Mathlib conventions, but the first declaration and its generality are the required public contract.

## Statement / milestones

1. Establish the Souslin/analytic-set closure machinery needed beyond the declarations already in `Mathlib.MeasureTheory.Constructions.Polish.Basic`.
2. Show analytic sets are capacitable for the outer measure induced by a finite Borel measure on a Polish space.
3. Deduce that every analytic set is `NullMeasurableSet` for that measure.
4. Derive the minimal completion-measurability corollary for suprema whose superlevel sets are analytic.
5. Verify every exported theorem with zero `sorry`, zero new axioms, and `#print axioms` showing only standard logical foundations.

## Standard reference

This is the Lusin–Souslin–Choquet universal-measurability theorem for analytic sets; standard references include Kechris, *Classical Descriptive Set Theory*, and Cohn, *Measure Theory*, in their treatments of analytic sets and Choquet capacitability.

## Intended reuse

The immediate consumer is `stat_bdd_uniform_log_penalty`, where a common-map boundary supremum has analytic superlevel projections and must be measurable for the completed sample law so ordinary completed expectation equals outer expectation. The result should be paper-agnostic and reusable anywhere Mathlib needs completed-measure integration of upper-semi-analytic losses.

## May assume / must derive

May assume Mathlib's existing definitions and closure theorems for Polish spaces, Borel spaces, `MeasureTheory.AnalyticSet`, finite measures, completions, and null-measurable sets. Must derive analytic-set universal measurability from those primitives; do not assume Choquet capacitability, universal measurability, or the target theorem as an axiom or local hypothesis.

## Non-goals (optional)

Do not formalize the Cattaneo–Titiunik–Yu model, boundary estimators, minimax risk, angular packing, or any paper-specific result. Avoid a general descriptive-set-theory library beyond the smallest reusable dependency closure needed for the API contract.

## Known building blocks (optional)

Start from `Mathlib.MeasureTheory.Constructions.Polish.Basic`, `MeasureTheory.AnalyticSet`, `MeasurableSet.analyticSet`, the analytic-set continuous-image and countable-union/intersection lemmas, `MeasureTheory.NullMeasurableSet`, `Measure.completion`, and the finite-measure outer-measure API.
