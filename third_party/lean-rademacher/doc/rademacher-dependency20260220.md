```mermaid
graph TD
  Defs["Defs: Signs, empiricalRademacherComplexity, rademacherComplexity, uniformDeviation"]
  Symm["Symmetrization: abs_symmetrization_equation"]
  Rad["Rademacher.lean: expectation_le_rademacher"]
  BD["BoundedDifference: uniformDeviation_bounded_difference"]
  McD["McDiarmid.lean: mcdiarmid_inequality_pos'"]
  MainExp["Main: uniform_deviation_expectation_le_two_smul_rademacher_complexity"]
  MainTail["Main: uniform_deviation_mcdiarmid_tail"]
  MainMain["Main: uniform_deviation_tail_bound_countable(_of_pos)"]
  SepSup["SeparableSpaceSup: separableSpaceSup_eq_real"]
  MainSep["Main: uniform_deviation_tail_bound_separable(_of_pos)"]
  RVProp["RademacherVariableProperty: rademacher_orthogonality, pmf variants"]
  L2["LinearPredictorL2: linear_predictor_l2_bound'"]
  Mass["Massart.lean: massart_lemma_pmf"]
  L1["LinearPredictorL1: linear_predictor_l1_bound'"]
  Cover["CoveringNumber: coveringNumber, coveringFinset"]
  PMet["PseudoMetric: empiricalNorm/dist, EmpiricalFunctionSpace"]
  Dud["DudleyEntropy: dudley_entropy_integral'"]
  MainDud["Main: dudley_entropy_integral_bound"]

  Defs --> Symm
  Defs --> Rad
  Symm --> Rad
  Defs --> BD
  BD --> MainTail
  McD --> MainTail
  Rad --> MainExp
  MainExp --> MainMain
  MainTail --> MainMain

  SepSup --> MainSep
  MainMain --> MainSep

  RVProp --> L2
  Defs --> L2

  Mass --> L1
  Defs --> L1

  Cover --> PMet
  PMet --> Dud
  Mass --> Dud
  Dud --> MainDud
  ```
  