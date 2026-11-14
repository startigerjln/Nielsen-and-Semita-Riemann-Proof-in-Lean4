import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open Filter
open scoped BigOperators Topology

namespace RH.Paper

/-- The term with index `n + 1` in a Dirichlet series. -/
noncomputable def dirichletTerm (a : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s))

/-- The sum over positive integers at most `x`, with half weight at
    the endpoint if `x` is an integer. -/
noncomputable def perronSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (Nat.floor x),
    if ((n + 1 : ℕ) : ℝ) = x then a (n + 1) / 2 else a (n + 1)

/-- The vertical contour integral divided by `2πi`, with
    `s = c + it` and `ds = i dt`. -/
noncomputable def perronIntegral (F : ℂ → ℂ) (c x T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ t in -T..T,
    let s := (c : ℂ) + (t : ℂ) * Complex.I
    F s * (x : ℂ) ^ s / s

/-- Perron's formula, Montgomery and Vaughan, *Multiplicative Number
    Theory I: Classical Theory* (2007), Theorem 5.1. Here `σ` specifies
    a half-plane of convergence of the Dirichlet series. -/
axiom perron_formula (a : ℕ → ℂ) (F : ℂ → ℂ) (σ c x : ℝ)
    (series : ∀ s : ℂ, σ < s.re → HasSum (dirichletTerm a s) (F s))
    (hc : max (0 : ℝ) σ < c) (hx : 0 < x) :
    Tendsto (perronIntegral F c x) atTop (𝓝 (perronSum a x))

/-- For a cutoff that is not a positive integer, all terms in the
    summatory function have weight one. -/
theorem perron_formula_of_nonintegral_cutoff (a : ℕ → ℂ) (F : ℂ → ℂ) (σ c x : ℝ)
    (series : ∀ s : ℂ, σ < s.re → HasSum (dirichletTerm a s) (F s))
    (hc : max (0 : ℝ) σ < c) (hx : 0 < x)
    (nonintegral : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≠ x) :
    Tendsto (perronIntegral F c x) atTop
      (𝓝 (∑ n ∈ Finset.range (Nat.floor x), a (n + 1))) := by
  simpa only [perronSum, if_neg (nonintegral _)] using perron_formula a F σ c x series hc hx

end RH.Paper
