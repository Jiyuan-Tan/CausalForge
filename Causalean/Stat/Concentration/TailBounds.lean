import Causalean.Stat.Concentration.TailBounds.Hoeffding
import Causalean.Stat.Concentration.TailBounds.Bernstein
import Causalean.Stat.Concentration.TailBounds.EmpiricalBernstein
import Causalean.Stat.Concentration.TailBounds.McDiarmid
import Causalean.Stat.Concentration.TailBounds.SubExponential
import Causalean.Stat.Concentration.TailBounds.Massart
import Causalean.Stat.Concentration.TailBounds.MaximalInequality
import Causalean.Stat.Concentration.TailBounds.BinomialCount

/-!
# Concentration · Tail bounds (barrel)

Scalar/bounded-difference tail inequalities: Hoeffding, Bernstein and its
empirical (variance-adaptive) form, McDiarmid's bounded-difference inequality,
the sub-exponential moment-generating-function machinery, finite maximal
inequalities for sub-exponential families, Massart's finite-class maximal
inequality, and multiplicative Bernoulli-count tails. Re-exports
`Causalean.Stat.Concentration.TailBounds.*`.
-/
