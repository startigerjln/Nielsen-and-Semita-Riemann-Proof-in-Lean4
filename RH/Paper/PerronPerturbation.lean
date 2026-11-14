import RH.Paper.Perron
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith

open Filter
open scoped BigOperators Topology

namespace RH.Paper

/-- The coefficients of the multiplier `1 + 3q^(-s) - 3(q+1)^(-s)`. -/
private def multiplierCoefficients (q n : ℕ) : ℤ :=
  if n = 1 then 1 else if n = q then 3 else if n = q + 1 then -3 else 0

private noncomputable def perronMultiplier (q : ℕ) (s : ℂ) : ℂ :=
  1 + 3 * (q : ℂ) ^ (-s) - 3 * ((q + 1 : ℕ) : ℂ) ^ (-s)

private theorem multiplier_hasSum (q : ℕ) (hq : 1 < q) (s : ℂ) :
    LSeriesHasSum (fun n => (multiplierCoefficients q n : ℂ)) s (perronMultiplier q s) := by
  have qNe : q ≠ 0 := by omega
  have qNeOne : q ≠ 1 := by omega
  have nextNeOne : q + 1 ≠ 1 := by omega
  have sum := hasSum_sum_of_ne_finset_zero
    (s := ({1, q, q + 1} : Finset ℕ))
    (f := LSeries.term (fun n => (multiplierCoefficients q n : ℂ)) s)
    (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [LSeries.term, multiplierCoefficients, hn.1, hn.2.1, hn.2.2])
  simpa [LSeriesHasSum, LSeries.term_of_ne_zero, multiplierCoefficients, perronMultiplier,
    qNe, qNeOne, nextNeOne, Ne.symm qNeOne, Ne.symm nextNeOne, div_eq_mul_inv,
    Complex.cpow_neg, sub_eq_add_neg, add_assoc] using sum

private noncomputable def perturbedCoefficients (q : ℕ) : ℕ → ℤ :=
  LSeries.convolution ArithmeticFunction.moebius (multiplierCoefficients q)

private theorem perturbedCoefficients_prime {q : ℕ} (prime : q.Prime) :
    perturbedCoefficients q q = 2 := by
  have qa : q ≠ 1 := prime.ne_one
  have qb : q + 1 ≠ 1 := by have := prime.two_le; omega
  have pairs : q.divisorsAntidiagonal = {(1, q), (q, 1)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp only [Nat.mem_divisorsAntidiagonal, prime.ne_zero, and_true, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro h
      have hd : a ∣ q := ⟨b, h.1.symm⟩
      rcases (Nat.dvd_prime prime).mp hd with rfl | rfl
      · exact Or.inl ⟨rfl, by simpa using h.1⟩
      · exact Or.inr ⟨rfl, Nat.eq_of_mul_eq_mul_left prime.pos (h.1.trans (Nat.mul_one _).symm)⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [prime.ne_zero]
  have unequal : (1, q) ≠ (q, 1) := by simp [qa, Ne.symm qa]
  simp [perturbedCoefficients, LSeries.convolution_def, pairs, unequal, multiplierCoefficients,
    qa, qb, ArithmeticFunction.moebius_apply_prime prime]

private theorem perron_perturbed_sum (q : ℕ) (hq : 1 < q) (n : ℕ) (c : ℝ)
    (hc : 1 < c) :
    Tendsto (perronIntegral (fun s => (riemannZeta s)⁻¹ * perronMultiplier q s) c
      ((n : ℝ) + 1 / 2)) atTop
      (𝓝 ((∑ j ∈ Finset.range n, perturbedCoefficients q (j + 1) : ℤ) : ℂ)) := by
  have series (s : ℂ) (hs : 1 < s.re) :
      HasSum (dirichletTerm (fun j => (perturbedCoefficients q j : ℂ)) s)
        ((riemannZeta s)⁻¹ * perronMultiplier q s) := by
    have eq := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs, mul_comm] at eq
    have value := (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr eq
    rw [one_div] at value
    have moebius : LSeriesHasSum (fun j => (ArithmeticFunction.moebius j : ℂ))
        s (riemannZeta s)⁻¹ := by
      rw [← value]
      exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
    have castConv : (fun j => (perturbedCoefficients q j : ℂ)) =
        LSeries.convolution (fun j => (ArithmeticFunction.moebius j : ℂ))
          (fun j => (multiplierCoefficients q j : ℂ)) := by
      funext j
      simp [perturbedCoefficients, LSeries.convolution_def, Int.cast_sum]
    rw [castConv]
    have full := moebius.convolution (multiplier_hasSum q hq s)
    have shifted := (hasSum_nat_add_iff'
      (f := LSeries.term
        (LSeries.convolution (fun j => (ArithmeticFunction.moebius j : ℂ))
          (fun j => (multiplierCoefficients q j : ℂ))) s) 1).mpr full
    unfold dirichletTerm
    simpa [LSeries.term_of_ne_zero (Nat.succ_ne_zero _),
      div_eq_mul_inv, Complex.cpow_neg] using shifted
  let x : ℝ := (n : ℝ) + 1 / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have floor : Nat.floor x = n := (Nat.floor_eq_iff hx.le).mpr
    ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
  have nonintegral (j : ℕ) : ((j + 1 : ℕ) : ℝ) ≠ x := by
    intro eq
    have same : j + 1 = n := by rw [← floor, ← eq, Nat.floor_natCast]
    have realSame := congrArg (fun k : ℕ => (k : ℝ)) same
    change ((j + 1 : ℕ) : ℝ) = (n : ℝ) at realSame
    rw [realSame] at eq
    dsimp [x] at eq
    linarith
  have h := perron_formula_of_nonintegral_cutoff _ _ 1 c x series (by simpa using hc) hx nonintegral
  rw [floor] at h
  simpa only [Int.cast_sum] using h

private theorem multiplier_sub_one_le (q : ℕ) (hq : 0 < q) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖perronMultiplier q s - 1‖ ≤ 3 * ‖s‖ / q := by
  let interval := Set.Icc (q : ℝ) ((q : ℝ) + 1)
  let power (x : ℝ) : ℂ := (x : ℂ) ^ (-s)
  let slope (x : ℝ) : ℂ := (-s) * (x : ℂ) ^ (-s - 1)
  have qPos : 0 < (q : ℝ) := by exact_mod_cast hq
  have deriv (x : ℝ) (hx : x ∈ interval) :
      HasDerivWithinAt power (slope x) interval x := by
    have pos : 0 < x := qPos.trans_le hx.1
    have h := (hasDerivAt_id (x : ℂ)).cpow_const (c := -s)
      (by simp [pos] : (x : ℂ) ∈ Complex.slitPlane)
    exact ((by simpa [slope] using h : HasDerivAt (fun z : ℂ => z ^ (-s)) (slope x)
      (x : ℂ)).comp_ofReal).hasDerivWithinAt
  have bound (x : ℝ) (hx : x ∈ interval) : ‖slope x‖ ≤ ‖s‖ / q := by
    have pos : 0 < x := qPos.trans_le hx.1
    have oneLe : 1 ≤ x := (by exact_mod_cast hq : (1 : ℝ) ≤ q).trans hx.1
    change ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ / q
    rw [norm_mul, norm_neg, Complex.norm_eq_abs ((x : ℂ) ^ (-s - 1)),
      Complex.abs_cpow_eq_rpow_re_of_pos pos, Complex.sub_re, Complex.neg_re, Complex.one_re,
      Real.rpow_sub pos, Real.rpow_one]
    calc
      ‖s‖ * (x ^ (-s.re) / x) ≤ ‖s‖ * (1 / x) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos oneLe
            (neg_nonpos.mpr hs)) pos.le) (norm_nonneg _)
      _ ≤ ‖s‖ / q := by
        rw [← mul_div_assoc, mul_one]
        exact div_le_div_of_nonneg_left (norm_nonneg _) qPos hx.1
  have diff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le deriv bound
    (convex_Icc (q : ℝ) ((q : ℝ) + 1)) (x := (q : ℝ)) (y := (q : ℝ) + 1) (by simp [interval])
    (by simp [interval])
  simp only [power, add_sub_cancel_left, norm_one] at diff
  rw [show perronMultiplier q s - 1 = (3 : ℂ) *
    ((q : ℂ) ^ (-s) - ((q + 1 : ℕ) : ℂ) ^ (-s)) by unfold perronMultiplier; ring,
    norm_mul, norm_sub_rev]
  norm_num at diff ⊢
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left diff (by norm_num)

private theorem eventually_round_of_tendsto_integer {F : ℝ → ℂ} {a : ℤ}
    (h : Tendsto F atTop (𝓝 (a : ℂ))) :
    ∀ᶠ T in atTop, round (F T).re = a := by
  filter_upwards [Metric.tendsto_nhds.mp h (1 / 2) (by norm_num)] with T close
  have realClose : |(F T).re - (a : ℝ)| < 1 / 2 := by
    rw [dist_eq_norm] at close
    simpa only [Complex.sub_re, Complex.intCast_re] using
      (Complex.abs_re_le_abs (F T - (a : ℂ))).trans_lt close
  have bounds := abs_lt.mp realClose
  have zero : round ((F T).re - (a : ℝ)) = 0 :=
    round_eq_zero_iff.mpr ⟨bounds.1.le, bounds.2⟩
  rw [round_sub_int] at zero
  exact sub_eq_zero.mp zero

/-- Uniform local approximation to zeta, even by a function holomorphic at
    every checked point, allows the rounded Perron sums to have increment 2
    at all sufficiently large cutoff heights.
    Half-integer cutoffs avoid the endpoint convention. -/
theorem exists_local_zeta_perturbation_with_perron_increment_two
    (K : Set ℂ) (compact : IsCompact K) (halfPlane : ∀ s ∈ K, 0 ≤ s.re)
    (poleOutside : (1 : ℂ) ∉ K) (ε : ℝ) (positive : 0 < ε) (c : ℝ) (hc : 1 < c) :
    ∃ (g : ℂ → ℂ) (n : ℕ),
      (∀ s ∈ K, DifferentiableAt ℂ g s ∧ ‖g s - riemannZeta s‖ < ε) ∧
      ∀ᶠ T in atTop,
        round (perronIntegral (fun s => (g s)⁻¹) c (((n + 1 : ℕ) : ℝ) + 1 / 2) T).re -
          round (perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2) T).re = 2 := by
  have zetaDiff (s : ℂ) (hs : s ∈ K) : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (fun eq => poleOutside (eq ▸ hs))
  obtain ⟨a, ha⟩ := compact.exists_bound_of_continuousOn
    (fun s hs => (zetaDiff s hs).continuousAt.continuousWithinAt)
  obtain ⟨b, hb⟩ := compact.exists_bound_of_continuousOn continuous_id.continuousOn
  let A := max a 1
  let δ := min (1 / 2 : ℝ) (ε / (2 * A))
  have APos : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  have δPos : 0 < δ := lt_min (by norm_num) (div_pos positive (by positivity))
  obtain ⟨m, hm⟩ := exists_nat_gt (3 * b / δ)
  obtain ⟨q, hq, prime⟩ := Nat.exists_infinite_primes m
  let g (s : ℂ) := riemannZeta s / perronMultiplier q s
  have multiplierClose (s : ℂ) (hs : s ∈ K) : ‖perronMultiplier q s - 1‖ < δ := by
    have qPos : 0 < (q : ℝ) := by exact_mod_cast prime.pos
    calc
      _ ≤ 3 * ‖s‖ / q := multiplier_sub_one_le q prime.pos s (halfPlane s hs)
      _ ≤ 3 * b / q := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb s hs) (by norm_num)) qPos.le
      _ < δ := (div_lt_iff₀ qPos).mpr (by
        have castLe : (m : ℝ) ≤ q := by exact_mod_cast hq
        have h := (div_lt_iff₀ δPos).mp (hm.trans_le castLe)
        simpa only [mul_comm] using h)
  have gClose (s : ℂ) (hs : s ∈ K) :
      DifferentiableAt ℂ g s ∧ ‖g s - riemannZeta s‖ < ε := by
    have err := multiplierClose s hs
    have triangle := norm_sub_norm_le (1 : ℂ) (perronMultiplier q s)
    rw [norm_one, norm_sub_rev] at triangle
    have lower : 1 / 2 ≤ ‖perronMultiplier q s‖ := by
      linarith only [err, triangle, min_le_left (1 / 2 : ℝ) (ε / (2 * A))]
    have halfPositive : 0 < (1 / 2 : ℝ) := by norm_num
    have nonzero : perronMultiplier q s ≠ 0 := norm_pos_iff.mp (halfPositive.trans_le lower)
    have powDiff (k : ℕ) (hk : 0 < k) :
        DifferentiableAt ℂ (fun z : ℂ => (k : ℂ) ^ (-z)) s := by
      have deriv := (Complex.hasStrictDerivAt_const_cpow
        (x := (k : ℂ)) (y := -s) (Or.inl (Nat.cast_ne_zero.mpr hk.ne'))).hasDerivAt
      exact deriv.differentiableAt.comp s differentiableAt_id.neg
    constructor
    · exact (zetaDiff s hs).div
        (((differentiableAt_const (1 : ℂ)).add ((powDiff q prime.pos).const_mul 3)).sub
          ((powDiff (q + 1) (Nat.succ_pos q)).const_mul 3)) nonzero
    · change ‖riemannZeta s / perronMultiplier q s - riemannZeta s‖ < ε
      rw [show riemannZeta s / perronMultiplier q s - riemannZeta s =
        riemannZeta s * (1 - perronMultiplier q s) / perronMultiplier q s by
          field_simp [nonzero]; ring, norm_div, norm_mul, norm_sub_rev]
      calc
        _ ≤ A * ‖perronMultiplier q s - 1‖ / (1 / 2) :=
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            ((ha s hs).trans (le_max_left _ _)) (norm_nonneg _)) (norm_nonneg _)).trans
            (div_le_div_of_nonneg_left (mul_nonneg APos.le (norm_nonneg _)) halfPositive lower)
        _ < A * (ε / (2 * A)) / (1 / 2) := by
          exact div_lt_div_of_pos_right
            (mul_lt_mul_of_pos_left (err.trans_le (min_le_right _ _)) APos) halfPositive
        _ = ε := by field_simp [APos.ne']; ring
  have inverse : (fun s => (g s)⁻¹) =
      (fun s => (riemannZeta s)⁻¹ * perronMultiplier q s) := by
    funext s
    simp [g, div_eq_mul_inv, mul_comm]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero prime.ne_zero
  let total : ℤ := ∑ j ∈ Finset.range n, perturbedCoefficients (n + 1) (j + 1)
  have atN : Tendsto (perronIntegral (fun s => (g s)⁻¹) c ((n : ℝ) + 1 / 2))
      atTop (𝓝 (total : ℂ)) := by
    rw [inverse]
    exact perron_perturbed_sum (n + 1) prime.one_lt n c hc
  have atNext : Tendsto (perronIntegral (fun s => (g s)⁻¹) c (((n + 1 : ℕ) : ℝ) + 1 / 2))
      atTop (𝓝 ((total + 2 : ℤ) : ℂ)) := by
    rw [inverse]
    simpa only [Finset.sum_range_succ, perturbedCoefficients_prime prime, total] using
      perron_perturbed_sum (n + 1) prime.one_lt (n + 1) c hc
  refine ⟨g, n, gClose, ?_⟩
  filter_upwards [eventually_round_of_tendsto_integer atN,
    eventually_round_of_tendsto_integer atNext] with T left right
  rw [left, right]
  omega

end RH.Paper
