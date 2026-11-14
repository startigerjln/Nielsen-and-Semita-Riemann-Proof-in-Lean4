import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
import RH.Paper.AnalyticPrecision

open scoped BigOperators

namespace RH.Paper

/-- The sum of the reciprocals of the positive integers at most `n`. -/
noncomputable def harmonicSum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1)

/-- Problem E in Lagarias's paper, with equality only at `n = 1`. -/
def lagariasCriterion : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    let divisorSum : ℝ := ((∑ d ∈ n.divisors, d : ℕ) : ℝ)
    let bound := harmonicSum n + Real.exp (harmonicSum n) * Real.log (harmonicSum n)
    divisorSum ≤ bound ∧ (divisorSum = bound → n = 1)

/-- Jeffrey C. Lagarias, *An Elementary Problem Equivalent to the
    Riemann Hypothesis*, American Mathematical Monthly 109 (2002),
    pp. 534–543, Theorem 1.1. See https://arxiv.org/abs/math/0008177. -/
axiom lagarias_theorem_1_1 : lagariasCriterion ↔ RiemannHypothesis

/-- The published divisor-sum criterion implies and is implied by the
    analytic check at every dyadic precision. -/
theorem lagarias_iff_dyadic_precision :
    lagariasCriterion ↔
      ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
        (_ : s ≠ 1) (k : ℕ), |s.re - 1 / 2| < (1 / 2 : ℝ) ^ k :=
  lagarias_theorem_1_1.trans riemannHypothesis_iff_dyadic_precision

end RH.Paper
