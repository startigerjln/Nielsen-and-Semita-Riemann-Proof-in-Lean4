import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open Filter MeasureTheory
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

noncomputable def perronIntegrand (F : ℂ → ℂ) (c x t : ℝ) : ℂ :=
  let s := (c : ℂ) + (t : ℂ) * Complex.I
  F s * (x : ℂ) ^ s / s

/-- The vertical contour integral divided by `2πi`, with
    `s = c + it` and `ds = i dt`. -/
noncomputable def perronIntegral (F : ℂ → ℂ) (c x T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ t in -T..T, perronIntegrand F c x t

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

/-- Exact agreement on the integration line transfers the Perron limit
    from the Dirichlet series to the replacement function. -/
theorem perron_formula_of_vertical_agreement (a : ℕ → ℂ) (F G : ℂ → ℂ) (σ c x : ℝ)
    (series : ∀ s : ℂ, σ < s.re → HasSum (dirichletTerm a s) (F s))
    (hc : max (0 : ℝ) σ < c) (hx : 0 < x)
    (agreement : ∀ t : ℝ, G ((c : ℂ) + (t : ℂ) * Complex.I) =
      F ((c : ℂ) + (t : ℂ) * Complex.I)) :
    Tendsto (perronIntegral G c x) atTop (𝓝 (perronSum a x)) := by
  have same : perronIntegral G c x = perronIntegral F c x := by
    funext T
    simp only [perronIntegral, perronIntegrand, agreement]
  rw [same]
  exact perron_formula a F σ c x series hc hx

/-- A finite-contour estimate for a replacement function, in terms of
    the uniform error of its weighted integrand on the contour. -/
theorem perronIntegral_sub_le_of_integrand_bound
    (F G : ℂ → ℂ) (c x T δ : ℝ)
    (integrableF : IntervalIntegrable (perronIntegrand F c x) volume (-T) T)
    (integrableG : IntervalIntegrable (perronIntegrand G c x) volume (-T) T)
    (error : ∀ t ∈ Set.uIoc (-T) T,
      ‖perronIntegrand G c x t - perronIntegrand F c x t‖ ≤ δ) :
    ‖perronIntegral G c x T - perronIntegral F c x T‖ ≤
      ‖(1 / (2 * (Real.pi : ℂ)))‖ * (δ * |T - -T|) := by
  rw [perronIntegral, perronIntegral, ← mul_sub,
    ← intervalIntegral.integral_sub integrableG integrableF, norm_mul]
  exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const error)
    (norm_nonneg _)

end RH.Paper
