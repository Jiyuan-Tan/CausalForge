import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.IIDPoisson
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Superposition
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.KL

/-!
# Finite marked Poisson samples over finite partitions

This module provides a reusable finite marked Poisson experiment: an i.i.d.
sample with a Poisson count, exact independent restrictions to a finite
measurable partition, measurable mark-ordered superposition, retained i.i.d.
prefixes, and the associated relative-entropy calculation.
-/

