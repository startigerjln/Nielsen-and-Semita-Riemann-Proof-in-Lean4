import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.NormNum

namespace RH.Paper

/-- Agreement at every dyadic precision is equivalent to exact
    agreement for real numbers. -/
theorem eq_iff_dyadic_precision (x y : ℝ) :
    x = y ↔ ∀ k : ℕ, |x - y| < (1 / 2 : ℝ) ^ k := by
  have half_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
  constructor
  · rintro rfl k
    simpa only [sub_self, abs_zero] using pow_pos half_pos k
  · intro h
    by_contra hne
    have error_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one error_pos half_lt_one
    exact (not_lt_of_ge (le_of_lt hk)) (h k)

/-- The analytic part of the precision characterization in Lemma 1.7.12,
    expressed using Mathlib's definition of the Riemann hypothesis. -/
theorem riemannHypothesis_iff_dyadic_precision :
    RiemannHypothesis ↔
      ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
        (_ : s ≠ 1) (k : ℕ), |s.re - 1 / 2| < (1 / 2 : ℝ) ^ k := by
  constructor
  · intro h s hz hn hp
    exact (eq_iff_dyadic_precision s.re (1 / 2)).mp (h s hz hn hp)
  · intro h s hz hn hp
    exact (eq_iff_dyadic_precision s.re (1 / 2)).mpr (h s hz hn hp)

end RH.Paper
