import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

namespace RH.Paper

/-- S. N. Mergelyan, *On the representation of functions by series of
    polynomials on closed sets* (1951). Polynomial approximation on a
    compact set with connected complement. -/
axiom mergelyan
    (K : Set ℂ) (f : ℂ → ℂ) (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (continuous : ContinuousOn f K) (holomorphic : DifferentiableOn ℂ f (interior K))
    (ε : ℝ) (positive : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < ε

/-- Multiplying by a prescribed polynomial plants its roots. Approximate
    the quotient on the compact set, where that polynomial is nonzero. -/
theorem approximate_with_polynomial_factor
    (K : Set ℂ) (f : ℂ → ℂ) (factor : Polynomial ℂ)
    (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (continuous : ContinuousOn f K) (holomorphic : DifferentiableOn ℂ f (interior K))
    (nonzero : ∀ z ∈ K, factor.eval z ≠ 0)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ q : Polynomial ℂ, ∀ z ∈ K, ‖(factor * q).eval z - f z‖ < ε := by
  obtain ⟨bound, hbound⟩ := compact.exists_bound_of_continuousOn factor.continuousOn
  have boundPositive : 0 < max bound 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨q, hq⟩ := mergelyan K (fun z => f z / factor.eval z) compact connected
    (continuous.div factor.continuousOn nonzero)
    (holomorphic.div factor.differentiableOn (fun z hz => nonzero z (interior_subset hz)))
    (ε / max bound 1) (div_pos positive boundPositive)
  refine ⟨q, fun z hz => ?_⟩
  rw [Polynomial.eval_mul, ← mul_div_cancel₀ (f z) (nonzero z hz), ← mul_sub, norm_mul]
  calc
    ‖factor.eval z‖ * ‖q.eval z - f z / factor.eval z‖
        ≤ max bound 1 * ‖q.eval z - f z / factor.eval z‖ :=
      mul_le_mul_of_nonneg_right ((hbound z hz).trans (le_max_left _ _)) (norm_nonneg _)
    _ < max bound 1 * (ε / max bound 1) :=
      mul_lt_mul_of_pos_left (hq z hz) boundPositive
    _ = ε := mul_div_cancel₀ ε (ne_of_gt boundPositive)

end RH.Paper
