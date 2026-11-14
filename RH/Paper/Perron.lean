import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.NormNum

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

/-- If the validity checks control the limiting error on the integration
    line, the coded function has the same Perron limit as the series. -/
theorem perron_formula_of_valid_limits {ι : Type*} {l : Filter ι} [NeBot l]
    (a : ℕ → ℂ) (F G : ℂ → ℂ) (σ c x : ℝ) (D : ι → ℝ → ℂ)
    (series : ∀ s : ℂ, σ < s.re → HasSum (dirichletTerm a s) (F s))
    (hc : max (0 : ℝ) σ < c) (hx : 0 < x)
    (convergence : ∀ t : ℝ, Tendsto (fun k => D k t) l
      (𝓝 (F ((c : ℂ) + (t : ℂ) * Complex.I))))
    (valid : ∀ t : ℝ, Tendsto (fun k => D k t - G ((c : ℂ) + (t : ℂ) * Complex.I)) l
      (𝓝 0)) :
    Tendsto (perronIntegral G c x) atTop (𝓝 (perronSum a x)) := by
  apply perron_formula_of_vertical_agreement a F G σ c x series hc hx
  intro t
  have error := (convergence t).sub
    (tendsto_const_nhds (x := G ((c : ℂ) + (t : ℂ) * Complex.I)))
  exact (sub_eq_zero.mp (tendsto_nhds_unique error (valid t))).symm

/-- A full dyadic precision bound on the integration line supplies the
    vanishing-error hypothesis of the Perron application. -/
theorem perron_formula_of_dyadic_validity
    (a : ℕ → ℂ) (F G : ℂ → ℂ) (σ c x : ℝ) (D : ℕ → ℝ → ℂ)
    (series : ∀ s : ℂ, σ < s.re → HasSum (dirichletTerm a s) (F s))
    (hc : max (0 : ℝ) σ < c) (hx : 0 < x)
    (convergence : ∀ t : ℝ, Tendsto (fun k => D k t) atTop
      (𝓝 (F ((c : ℂ) + (t : ℂ) * Complex.I))))
    (valid : ∀ (t : ℝ) (k : ℕ),
      ‖D k t - G ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 / 2 : ℝ) ^ k) :
    Tendsto (perronIntegral G c x) atTop (𝓝 (perronSum a x)) := by
  apply perron_formula_of_valid_limits a F G σ c x D series hc hx convergence
  intro t
  exact squeeze_zero_norm (valid t)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

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

/-- The Dirichlet checks in Lemma 1.33 identify the coded reciprocal
    zeta integral with the ordinary one at every truncation height. -/
theorem perron_recip_zeta_eq_of_dirichlet_checks
    (g : ℂ → ℂ) (c x : ℝ) (hc : 1 < c) (cutoff : ℕ → ℕ)
    (exhausts : Tendsto cutoff atTop atTop)
    (valid : ∀ (t : ℝ) (k : ℕ),
      ‖(∑ j ∈ Finset.range (cutoff k),
        LSeries.term 1 ((c : ℂ) + (t : ℂ) * Complex.I) j) -
        g ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 / 2 : ℝ) ^ k) :
    perronIntegral (fun s => (g s)⁻¹) c x =
      perronIntegral (fun s => (riemannZeta s)⁻¹) c x := by
  have agree (t : ℝ) :
      g ((c : ℂ) + (t : ℂ) * Complex.I) = riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) := by
    let s : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
    have hs : 1 < s.re := by simpa [s, Complex.mul_re] using hc
    have sum := (LSeriesHasSum_one hs).tendsto_sum_nat.comp exhausts
    have error : Tendsto (fun k => (∑ j ∈ Finset.range (cutoff k), LSeries.term 1 s j) - g s)
        atTop (𝓝 0) :=
      squeeze_zero_norm (valid t)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    exact (sub_eq_zero.mp (tendsto_nhds_unique (sum.sub tendsto_const_nhds) error)).symm
  funext T
  simp only [perronIntegral, perronIntegrand, agree]

private theorem recip_zeta_moebius_series (s : ℂ) (hs : 1 < s.re) :
    HasSum (dirichletTerm (fun j => (ArithmeticFunction.moebius j : ℂ)) s)
      (riemannZeta s)⁻¹ := by
  have eq := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs, mul_comm] at eq
  have value := (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr eq
  rw [one_div] at value
  have series : LSeriesHasSum (fun j => (ArithmeticFunction.moebius j : ℂ))
      s (riemannZeta s)⁻¹ := by
    rw [← value]
    exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have shifted := (hasSum_nat_add_iff'
    (f := LSeries.term (fun j => (ArithmeticFunction.moebius j : ℂ)) s) 1).mpr series
  unfold dirichletTerm
  simpa [LSeries.term_of_ne_zero (Nat.succ_ne_zero _), div_eq_mul_inv,
    Complex.cpow_neg] using shifted

/-- The coded continuation computes the ordinary Mertens sum at a
    nonintegral cutoff, which avoids Perron's half-weight endpoint. -/
theorem perron_mertens_of_dirichlet_checks
    (g : ℂ → ℂ) (c x : ℝ) (hc : 1 < c) (hx : 0 < x) (cutoff : ℕ → ℕ)
    (exhausts : Tendsto cutoff atTop atTop)
    (valid : ∀ (t : ℝ) (k : ℕ),
      ‖(∑ j ∈ Finset.range (cutoff k),
        LSeries.term 1 ((c : ℂ) + (t : ℂ) * Complex.I) j) -
        g ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 / 2 : ℝ) ^ k)
    (nonintegral : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) ≠ x) :
    Tendsto (perronIntegral (fun s => (g s)⁻¹) c x) atTop
      (𝓝 ((∑ j ∈ Finset.range (Nat.floor x), ArithmeticFunction.moebius (j + 1) : ℤ) : ℂ)) := by
  rw [perron_recip_zeta_eq_of_dirichlet_checks g c x hc cutoff exhausts valid]
  simpa only [Int.cast_sum] using
    perron_formula_of_nonintegral_cutoff _ _ 1 c x recip_zeta_moebius_series
      (by simpa using hc) hx nonintegral

end RH.Paper
