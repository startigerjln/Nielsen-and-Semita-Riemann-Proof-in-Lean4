import RH.Paper.Perron
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith

open Filter MeasureTheory
open scoped BigOperators Topology

namespace RH.Paper

/-- Rounding recovers the integer once the total error is strictly
    below one half. -/
theorem round_eq_of_abs_sub_lt_half (y : ℝ) (a : ℤ)
    (close : |y - (a : ℝ)| < 1 / 2) : round y = a := by
  have bounds := abs_lt.mp close
  have hzero : round (y - (a : ℝ)) = 0 :=
    round_eq_zero_iff.mpr ⟨bounds.1.le, bounds.2⟩
  rw [round_sub_int] at hzero
  exact sub_eq_zero.mp hzero

/-- Uniform approximation controls the error in taking a reciprocal
    when the target is bounded away from zero. -/
theorem reciprocal_error_le (target approx : ℂ) (lower tolerance : ℝ)
    (positive : 0 < lower) (bound : lower ≤ ‖target‖)
    (close : ‖approx - target‖ ≤ tolerance) (small : tolerance ≤ lower / 2) :
    ‖approx⁻¹ - target⁻¹‖ ≤ tolerance / ((lower / 2) * lower) := by
  have halfPositive : 0 < lower / 2 := half_pos positive
  have triangle : ‖target‖ ≤ ‖approx‖ + ‖approx - target‖ := by
    calc
      ‖target‖ = ‖approx - (approx - target)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖approx‖ + ‖approx - target‖ := norm_sub_le _ _
  have approxBound : lower / 2 ≤ ‖approx‖ := by linarith
  have approxNe : approx ≠ 0 := norm_pos_iff.mp (halfPositive.trans_le approxBound)
  have targetNe : target ≠ 0 := norm_pos_iff.mp (positive.trans_le bound)
  have toleranceNonneg := (norm_nonneg _).trans close
  have denominatorBound : (lower / 2) * lower ≤ ‖approx‖ * ‖target‖ :=
    mul_le_mul approxBound bound positive.le (norm_nonneg _)
  rw [show approx⁻¹ - target⁻¹ = (target - approx) / (approx * target) by
    field_simp [approxNe, targetNe], norm_div, norm_mul, norm_sub_rev]
  exact (div_le_div_of_nonneg_right close
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
    (div_le_div_of_nonneg_left toleranceNonneg (mul_pos halfPositive positive) denominatorBound)

/-- The reciprocal of zeta on the absolute convergence half-plane
    is the Dirichlet series of the Möbius function. -/
theorem recip_zeta_hasSum_moebius (s : ℂ) (hs : 1 < s.re) :
    HasSum (dirichletTerm (fun n => (ArithmeticFunction.moebius n : ℂ)) s) (riemannZeta s)⁻¹ := by
  have series := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have eq := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at eq
  have value : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = (riemannZeta s)⁻¹ := by
    rw [mul_comm] at eq
    rw [← one_div]
    exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr eq
  have full : HasSum
      (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s) (riemannZeta s)⁻¹ := by
    simpa only [LSeriesHasSum, value] using series
  have shifted := (hasSum_nat_add_iff' (f := LSeries.term
    (fun n => (ArithmeticFunction.moebius n : ℂ)) s) 1).mpr full
  change HasSum (fun n : ℕ => (ArithmeticFunction.moebius (n + 1) : ℂ) *
    (((n + 1 : ℕ) : ℂ) ^ (-s))) (riemannZeta s)⁻¹
  simpa [LSeries.term_of_ne_zero (Nat.succ_ne_zero _), div_eq_mul_inv,
    Complex.cpow_neg] using shifted

def mertensValue (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n, ArithmeticFunction.moebius (j + 1)

/-- Use a half-integer cutoff to recover the ordinary Mertens sum,
    avoiding the half weight at integer cutoffs in Perron's formula. -/
theorem perron_tendsto_mertens (n : ℕ) (c : ℝ) (hc : 1 < c) :
    Tendsto (perronIntegral (fun s => (riemannZeta s)⁻¹) c ((n : ℝ) + 1 / 2))
      atTop (𝓝 (mertensValue n : ℂ)) := by
  let x : ℝ := (n : ℝ) + 1 / 2
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : 0 < x := by dsimp [x]; linarith
  have floor : Nat.floor x = n := (Nat.floor_eq_iff hx.le).mpr
    ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have nonintegral (j : ℕ) : ((j + 1 : ℕ) : ℝ) ≠ x := by
    intro eq
    have same : j + 1 = n := by
      rw [← floor, ← eq, Nat.floor_natCast]
    have realSame : ((j + 1 : ℕ) : ℝ) = (n : ℝ) := congrArg (fun v : ℕ => (v : ℝ)) same
    rw [realSame] at eq
    dsimp [x] at eq
    linarith
  have h := perron_formula_of_nonintegral_cutoff
    (fun j => (ArithmeticFunction.moebius j : ℂ)) (fun s => (riemannZeta s)⁻¹) 1 c x
    (fun _ => recip_zeta_hasSum_moebius _) (by simpa using hc) hx nonintegral
  rw [floor] at h
  simpa only [mertensValue, Int.cast_sum] using h

/-- Rounding is stable under an integral perturbation that stays
    within the remaining error allowance. -/
theorem round_mertens_of_perron_errors (n : ℕ) (c T : ℝ) (g : ℂ → ℂ)
    (truncation : ‖perronIntegral (fun s => (riemannZeta s)⁻¹) c ((n : ℝ) + 1 / 2) T -
      (mertensValue n : ℂ)‖ < 1 / 4)
    (replacement : ‖perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2) T -
      perronIntegral (fun s => (riemannZeta s)⁻¹) c ((n : ℝ) + 1 / 2) T‖ < 1 / 4) :
    round (perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2) T).re = mertensValue n := by
  let orig := perronIntegral (fun s => (riemannZeta s)⁻¹) c ((n : ℝ) + 1 / 2) T
  let approx := perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2) T
  apply round_eq_of_abs_sub_lt_half
  change |approx.re - (mertensValue n : ℝ)| < 1 / 2
  have total : ‖approx - (mertensValue n : ℂ)‖ < 1 / 2 := by
    rw [show approx - (mertensValue n : ℂ) =
      (approx - orig) + (orig - (mertensValue n : ℂ)) by abel]
    apply (norm_add_le _ _).trans_lt
    change ‖approx - orig‖ + ‖orig - (mertensValue n : ℂ)‖ < 1 / 2
    linarith only [show ‖orig - (mertensValue n : ℂ)‖ < 1 / 4 from truncation,
      show ‖approx - orig‖ < 1 / 4 from replacement]
  exact (by simpa only [Complex.sub_re, Complex.intCast_re] using
    (Complex.abs_re_le_abs (approx - (mertensValue n : ℂ))).trans_lt total)

/-- At any sufficiently tall finite contour, there is a positive
    uniform tolerance on the zeta approximation that guarantees exact
    recovery of the chosen Mertens sum after rounding. -/
theorem exists_perron_recovery_threshold (n : ℕ) (c : ℝ) (hc : 1 < c) :
    ∃ H : ℝ, ∀ T ≥ H, ∃ ε > (0 : ℝ), ∀ g : ℂ → ℂ,
      ContinuousOn (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc (-T) T) →
      (∀ t ∈ Set.Icc (-T) T, ‖g ((c : ℂ) + (t : ℂ) * Complex.I) -
        riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ε) →
      round (perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2) T).re = mertensValue n := by
  obtain ⟨height, truncation⟩ :=
    Metric.tendsto_atTop.mp (perron_tendsto_mertens n c hc) (1 / 4) (by norm_num)
  refine ⟨max height 1, fun T hT => ?_⟩
  have hTpos : 0 < T := zero_lt_one.trans_le ((le_max_right _ _).trans hT)
  have hInterval : -T ≤ T := by linarith
  let segment := Set.Icc (-T) T
  let point (t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
  let x : ℝ := (n : ℝ) + 1 / 2
  have xPos : 0 < x := by dsimp [x]; positivity
  have pointCont : Continuous point := by
    unfold point
    fun_prop
  have pointRe (t : ℝ) : (point t).re = c := by
    simp [point, Complex.mul_re]
  have pointNe (t : ℝ) : point t ≠ 0 := by
    intro zero
    have := (pointRe t).symm.trans (congrArg Complex.re zero)
    simp at this
    linarith
  have zetaCont : Continuous (fun t => riemannZeta (point t)) := by
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have away : point t ≠ 1 := by
      intro eq
      have := (pointRe t).symm.trans (congrArg Complex.re eq)
      simp at this
      linarith
    exact (differentiableAt_riemannZeta away).continuousAt.comp pointCont.continuousAt
  have zetaNe (t : ℝ) : riemannZeta (point t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa only [pointRe] using hc)
  have compact : IsCompact segment := isCompact_Icc
  have inhabited : segment.Nonempty := ⟨0, by change -T ≤ 0 ∧ 0 ≤ T; constructor <;> linarith⟩
  obtain ⟨minAt, _, minBound⟩ := compact.exists_isMinOn inhabited zetaCont.norm.continuousOn
  let lower : ℝ := ‖riemannZeta (point minAt)‖
  have lowerPos : 0 < lower := norm_pos_iff.mpr (zetaNe minAt)
  let weight (t : ℝ) : ℂ := (x : ℂ) ^ (point t) / point t
  have weightCont : Continuous weight := by
    have baseNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr xPos.ne'
    exact (pointCont.const_cpow (Or.inl baseNe)).div pointCont pointNe
  obtain ⟨b, bound⟩ := compact.exists_bound_of_continuousOn weightCont.continuousOn
  let denom := (lower / 2) * lower
  let pref : ℂ := 1 / (2 * (Real.pi : ℂ))
  let scale := ‖pref‖ * (max b 1 * |T - -T|) / denom
  let ε := min (lower / 2) ((1 / 8 : ℝ) / max scale 1)
  have denomPos : 0 < denom := mul_pos (half_pos lowerPos) lowerPos
  have epsPos : 0 < ε :=
    lt_min (half_pos lowerPos) (div_pos (by norm_num) (zero_lt_one.trans_le (le_max_right _ _)))
  have epsSmall : ε ≤ lower / 2 := min_le_left _ _
  refine ⟨ε, epsPos, fun g gCont approximation => ?_⟩
  have inverseClose (t : ℝ) (ht : t ∈ segment) :
      ‖(g (point t))⁻¹ - (riemannZeta (point t))⁻¹‖ ≤ ε / denom :=
    reciprocal_error_le _ _ lower ε lowerPos (minBound ht) (approximation t ht) epsSmall
  have gNe (t : ℝ) (ht : t ∈ segment) : g (point t) ≠ 0 := by
    intro zero
    have e := approximation t ht
    change ‖g (point t) - riemannZeta (point t)‖ ≤ ε at e
    rw [zero, zero_sub, norm_neg] at e
    have lowerBound : lower ≤ ‖riemannZeta (point t)‖ := minBound ht
    linarith
  have integrableZ : IntervalIntegrable
      (perronIntegrand (fun s => (riemannZeta s)⁻¹) c x) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hInterval
    have h : ContinuousOn (fun t => (riemannZeta (point t))⁻¹ * weight t) segment :=
      (zetaCont.continuousOn.inv₀ (fun t _ => zetaNe t)).mul weightCont.continuousOn
    change ContinuousOn (fun t => (riemannZeta (point t))⁻¹ *
      (x : ℂ) ^ (point t) / point t) segment
    simpa only [weight, div_eq_mul_inv, mul_assoc] using h
  have integrableG : IntervalIntegrable
      (perronIntegrand (fun s => (g s)⁻¹) c x) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hInterval
    have h := (gCont.inv₀ gNe).mul weightCont.continuousOn
    change ContinuousOn (fun t => (g (point t))⁻¹ *
      (x : ℂ) ^ (point t) / point t) segment
    simpa only [weight, div_eq_mul_inv, mul_assoc] using h
  apply round_mertens_of_perron_errors
  · simpa only [dist_eq_norm] using truncation T ((le_max_left _ _).trans hT)
  · have error (t : ℝ) (ht : t ∈ Set.uIoc (-T) T) :
        ‖perronIntegrand (fun s => (g s)⁻¹) c x t -
          perronIntegrand (fun s => (riemannZeta s)⁻¹) c x t‖ ≤ ε / denom * max b 1 := by
      have mem : t ∈ segment := by
        rw [Set.uIoc_of_le hInterval] at ht
        exact ⟨ht.1.le, ht.2⟩
      rw [show perronIntegrand (fun s => (g s)⁻¹) c x t -
          perronIntegrand (fun s => (riemannZeta s)⁻¹) c x t =
          ((g (point t))⁻¹ - (riemannZeta (point t))⁻¹) * weight t by
          simp only [perronIntegrand, point, weight, div_eq_mul_inv]; ring, norm_mul]
      exact mul_le_mul (inverseClose t mem) ((bound t mem).trans (le_max_left _ _))
        (norm_nonneg _) (div_nonneg epsPos.le denomPos.le)
    calc
      _ ≤ ‖pref‖ * ((ε / denom * max b 1) * |T - -T|) :=
        perronIntegral_sub_le_of_integrand_bound _ _ c x T _ integrableZ integrableG error
      _ = ε * scale := by dsimp [scale]; ring
      _ ≤ ε * max scale 1 := mul_le_mul_of_nonneg_left (le_max_left _ _) epsPos.le
      _ ≤ 1 / 8 := by
        have scalePos : 0 < max scale 1 := zero_lt_one.trans_le (le_max_right _ _)
        exact (le_div_iff₀ scalePos).mp (min_le_right _ _)
      _ < 1 / 4 := by norm_num

/-- A single height and tolerance suffice for any finite family of
    Mertens sums. -/
theorem exists_finite_perron_recovery_threshold (inputs : Finset ℕ) (c : ℝ) (hc : 1 < c) :
    ∃ H : ℝ, ∀ T ≥ H, ∃ ε > (0 : ℝ), ∀ g : ℂ → ℂ,
      ContinuousOn (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc (-T) T) →
      (∀ t ∈ Set.Icc (-T) T, ‖g ((c : ℂ) + (t : ℂ) * Complex.I) -
        riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ε) →
      ∀ n ∈ inputs,
        round (perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2) T).re = mertensValue n := by
  induction inputs using Finset.induction_on with
  | empty => exact ⟨1, fun _ _ => ⟨1, zero_lt_one, by simp⟩⟩
  | @insert n rest fresh ih =>
    obtain ⟨height, recover⟩ := exists_perron_recovery_threshold n c hc
    obtain ⟨heightRest, recoverRest⟩ := ih
    refine ⟨max height heightRest, fun T hT => ?_⟩
    obtain ⟨ε, positive, head⟩ := recover T ((le_max_left _ _).trans hT)
    obtain ⟨δ, deltaPositive, tail⟩ := recoverRest T ((le_max_right _ _).trans hT)
    refine ⟨min ε δ, lt_min positive deltaPositive, fun g continuous close j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact head g continuous (fun t ht => (close t ht).trans (min_le_left _ _))
    · exact tail g continuous (fun t ht => (close t ht).trans (min_le_right _ _)) j hj

/-- At a standard point in the Dirichlet convergence half-plane,
    a close zeta approximant also agrees with sufficiently late partial
    Dirichlet sums to the requested tolerance. -/
theorem close_to_zeta_eventually_close_to_dirichlet_sum
    (s g : ℂ) (hs : 1 < s.re) (ε : ℝ) (positive : 0 < ε)
    (close : ‖g - riemannZeta s‖ < ε / 2) :
    ∃ N : ℕ, ∀ j ≥ N, ‖g - ∑ i ∈ Finset.range j, LSeries.term 1 s i‖ < ε := by
  have sum : HasSum (LSeries.term 1 s) (riemannZeta s) := LSeriesHasSum_one hs
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp sum.tendsto_sum_nat (ε / 2) (half_pos positive)
  refine ⟨N, fun j hj => ?_⟩
  have tail : ‖(∑ i ∈ Finset.range j, LSeries.term 1 s i) - riemannZeta s‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN j hj
  rw [show g - (∑ i ∈ Finset.range j, LSeries.term 1 s i) =
    (g - riemannZeta s) - ((∑ i ∈ Finset.range j, LSeries.term 1 s i) - riemannZeta s) by abel]
  exact (norm_sub_le _ _).trans_lt (by linarith)

end RH.Paper
