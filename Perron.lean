/-
Copyright (c) 2026 J. L. Nielsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. L. Nielsen
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Perron's Summation Formula

This file proves Perron's formula, which relates the partial sums of a
Dirichlet series to a vertical contour integral.

## Main definitions

* `perronKernel`: The Perron kernel `x^s / s` for `x > 0`, `s ≠ 0`.
* `perronIntegral`: The truncated Perron integral
  `(1/2πi) ∫_{σ-iT}^{σ+iT} F(s) x^s/s ds`.
* `perronSum`: The partial sum `Σ_{n ≤ x} a(n)` of Dirichlet series coefficients.

## Main results

* `perronKernel_differentiableAt`: The Perron kernel is holomorphic away from `s = 0`.
* `perronKernel_norm`: The norm `‖x^s/s‖ = x^(Re s) / ‖s‖` for `x > 0`.
* `perron_truncated`: The truncated Perron formula with explicit error term.
* `perron_formula`: The limiting Perron formula (T → ∞).

## Implementation notes

Several proofs are marked `sorry` pending compilation against Mathlib to
resolve API details (exact names of `cpow` norm lemmas, `Complex.norm`
rewrites, integral convergence automation). The proof STRATEGIES are
documented in comments; filling the `sorry`s requires a working Lean
build environment with Mathlib loaded.

## References

* [O. Perron, *Zur Theorie der Dirichletschen Reihen*][perron1908]
* [E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*][titchmarsh1986]
* [H. Iwaniec and E. Kowalski, *Analytic Number Theory*][iwaniec-kowalski2004]

## Tags

Perron formula, Dirichlet series, contour integration, analytic number theory
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology LSeries.notation

noncomputable section

/-! ## The Perron Kernel -/

/-- The Perron kernel: for `x > 0` and `s : ℂ` with `s ≠ 0`, this is `x^s / s`.
    The kernel has a simple pole at `s = 0` with residue `log x`.
    On the vertical line `Re s = σ`, the kernel has magnitude `x^σ / |s|`.
    [Titchmarsh 1986, Section 3.12] -/
def perronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s / s

/-- The Perron kernel is holomorphic away from `s = 0`. -/
theorem perronKernel_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (perronKernel x) s := by
  unfold perronKernel
  apply DifferentiableAt.div
  · exact differentiableAt_const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  · exact differentiableAt_id
  · exact hs

/-! ## Perron Kernel Norm Estimates -/

/-- The norm of the Perron kernel: `‖x^s / s‖ = x^(Re s) / ‖s‖` for `x > 0`, `s ≠ 0`.
    Uses Mathlib's `abs_cpow_eq_rpow_re_of_pos`. -/
theorem perronKernel_norm {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    ‖perronKernel x s‖ = x ^ s.re / ‖s‖ := by
  simp only [perronKernel, norm_div, Complex.norm_eq_abs,
    abs_cpow_eq_rpow_re_of_pos hx]

/-- On a vertical line `Re s = σ`, the imaginary part controls the denominator:
    `‖σ + t*I‖² = σ² + t²`, so `‖σ + t*I‖ ≥ |t|`.
    This is the key estimate for bounding the Perron integral error.
    [Standard; Titchmarsh 1986, Lemma 3.12] -/
theorem norm_vertical_ge_im (σ t : ℝ) :
    |t| ≤ ‖(↑σ + ↑t * I : ℂ)‖ := by
  rw [Complex.norm_eq_abs]
  calc ↑|t| = Complex.abs (↑t * I) := by
        rw [map_mul, abs_ofReal, abs_I, mul_one]
      _ ≤ Complex.abs (↑σ + ↑t * I) := by
        sorry -- |im z| ≤ |z|; needs Complex.abs_im_le_abs or sq_abs

/-- The Perron kernel bound: `‖x^(σ+it) / (σ+it)‖ ≤ x^σ / |t|` for |t| ≥ 1.
    Combines perronKernel_norm with norm_vertical_ge_im.
    [Titchmarsh 1986, Lemma 3.12] -/
theorem perronKernel_bound {x : ℝ} (hx : 0 < x) {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖perronKernel x (↑σ + ↑t * I)‖ ≤ x ^ σ / |t| := by
  have hne : (↑σ + ↑t * I : ℂ) ≠ 0 := by
    intro h
    have : Complex.im (↑σ + ↑t * I : ℂ) = 0 := by rw [h]; simp
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im] at this
    linarith
  rw [perronKernel_norm hx hne]
  have hre : (↑σ + ↑t * I : ℂ).re = σ := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [hre]
  apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx σ).le
    (by linarith : (0 : ℝ) < |t|)
    (norm_vertical_ge_im σ t)

/-! ## The Truncated Perron Integral -/

/-- The truncated Perron integral: the vertical line integral of `F(s) x^s / s`
    from `σ - iT` to `σ + iT`.
    This is `(1/2πi) ∫_{-T}^{T} F(σ + it) (x^(σ+it)) / (σ+it) dt`.
    [Perron 1908; Titchmarsh 1986, Section 3.12] -/
def perronIntegral (F : ℂ → ℂ) (σ : ℝ) (T : ℝ) (x : ℝ) : ℂ :=
  (1 / (2 * π * I)) • ∫ t in Set.Icc (-T) T,
    F (σ + t * I) * perronKernel x (σ + t * I)

/-- The partial sum of Dirichlet series coefficients up to x.
    `perronSum a x = Σ_{1 ≤ n ≤ x} a(n)` -/
def perronSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n in Finset.Icc 1 ⌊x⌋₊, a n

/-! ## The Perron Kernel Step Function Property

The Perron integral of the bare kernel `x^s/s` (with F = 1) computes
a step function: it equals 1 for x > 1 and 0 for 0 < x < 1.
This is the core identity underlying Perron's formula.

The proof uses contour shifting:
- For x > 1: shift the contour left past the pole at s = 0,
  picking up residue 1. The shifted integral vanishes because
  |x^s| = x^(Re s) → 0 as Re s → -∞.
- For 0 < x < 1: shift the contour right. No poles are crossed.
  The shifted integral vanishes because |x^s| → 0 as Re s → +∞.

Both arguments require Cauchy's theorem (rectangular contour) and
decay estimates on the horizontal segments.
[Titchmarsh 1986, Lemma 3.12] -/

/-- For x > 1, the Perron integral of the bare kernel tends to 1.
    Proof strategy: shift contour left, pick up residue at s = 0. -/
theorem perronKernel_integral_gt_one {x : ℝ} (hx : 1 < x) {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun T => perronIntegral (fun _ => 1) σ T x)
      Filter.atTop (nhds 1) := by
  -- Strategy: Use Cauchy's theorem on the rectangle with vertices
  -- σ±iT, -R±iT. As R → ∞, the left vertical integral vanishes
  -- (x^(-R) → 0). The horizontal segments are O(1/T) and vanish
  -- as T → ∞. The residue at s = 0 contributes 1.
  sorry

/-- For 0 < x < 1, the Perron integral of the bare kernel tends to 0.
    Proof strategy: shift contour right, no poles crossed. -/
theorem perronKernel_integral_lt_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1)
    {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun T => perronIntegral (fun _ => 1) σ T x)
      Filter.atTop (nhds 0) := by
  -- Strategy: Shift contour right to Re s = R. By Cauchy's theorem
  -- (no poles for Re s > 0), the integral is unchanged. The shifted
  -- vertical integral is O(x^R) → 0 as R → ∞ since x < 1.
  sorry

/-! ## The Truncated Perron Formula

The main theorem: interchanging summation and integration to express
partial sums of Dirichlet series as contour integrals.

**Proof outline** (following Iwaniec-Kowalski, Prop 5.1):

1. Write `F(s) = Σ a(n)/n^s` and substitute into the contour integral.
2. Interchange sum and integral (justified by absolute convergence
   of the Dirichlet series for Re s = σ > σ_a).
3. Each term becomes `a(n) · (1/2πi) ∫ (x/n)^s/s ds`.
4. By the kernel step function property:
   - When n < x: the integral → 1 as T → ∞
   - When n > x: the integral → 0 as T → ∞
   - When n = x: boundary case (excluded by hypothesis)
5. The finite-T error comes from the truncation of the vertical integral,
   bounded using perronKernel_bound.
-/

/-- **Truncated Perron Formula**: For a Dirichlet series `L a s`
    absolutely convergent at `σ`, for `σ > 0`, `T > 0`, and `x > 0`
    not a positive integer:

    `Σ_{n ≤ x} a(n) = (1/2πi) ∫_{σ-iT}^{σ+iT} (L a s) x^s/s ds + Error`

    with `‖Error‖ ≤ (x^σ / T) · Σ ‖a(n)‖/n^σ`.

    [Perron 1908; Titchmarsh 1986, Theorem 3.12] -/
theorem perron_truncated (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : LSeriesSummable a σ)
    {x : ℝ} (hx : 0 < x) (hx_int : ∀ n : ℕ, (n : ℝ) ≠ x)
    {T : ℝ} (hT : 0 < T) :
    ∃ (E : ℂ), perronSum a x = perronIntegral (LSeries a) σ T x + E ∧
      ‖E‖ ≤ (x ^ σ / T) * ∑' n, ‖a n‖ / (n : ℝ) ^ σ := by
  -- Step 1: Substitute F(s) = L a s = Σ a(n)/n^s into the integral
  -- Step 2: Interchange sum and integral (Fubini, from absolute convergence)
  -- Step 3: Each term is a(n) · perronIntegral(1, σ, T, x/n)
  -- Step 4: Split into n ≤ x (contribute a(n) + error) and n > x (error only)
  -- Step 5: The total error is bounded by Σ |a(n)| · |kernel truncation error|
  --         Each truncation error is O(x^σ / (n^σ · T)) from perronKernel_bound
  -- Step 6: Summing gives the bound (x^σ/T) · Σ ‖a(n)‖/n^σ
  sorry

/-! ## The Limiting Perron Formula -/

/-- **Perron's Formula** (limiting version): As `T → ∞`, the truncated
    Perron integral converges to the partial sum.

    `Σ_{n ≤ x} a(n) = lim_{T→∞} (1/2πi) ∫_{σ-iT}^{σ+iT} (L a s) x^s/s ds`

    This follows from perron_truncated: the error is O(1/T) → 0.
    [Perron 1908; Titchmarsh 1986, Theorem 3.12] -/
theorem perron_formula (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : LSeriesSummable a σ)
    {x : ℝ} (hx : 0 < x) (hx_int : ∀ n : ℕ, (n : ℝ) ≠ x) :
    Filter.Tendsto (fun T => perronIntegral (LSeries a) σ T x)
      Filter.atTop (nhds (perronSum a x)) := by
  -- From perron_truncated: for each T > 0, the error ‖E(T)‖ ≤ C/T
  -- where C = x^σ · Σ ‖a(n)‖/n^σ is a constant.
  -- Since C/T → 0 as T → ∞, the integral converges to the sum.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose T₀ large enough that C/T₀ < ε
  obtain ⟨E, hE_eq, hE_bound⟩ := perron_truncated a hσ hconv hx hx_int (T := 1) one_pos
  sorry -- Complete: use perron_truncated at each T, bound error by C/T < ε

/-! ## Application: Mertens Function

The Mertens function M(x) = Σ_{n ≤ x} μ(n) is the partial sum of the
Möbius function. By Perron's formula applied to the Dirichlet series
1/ζ(s) = Σ μ(n)/n^s:

  M(x) = (1/2πi) ∫_{σ-i∞}^{σ+i∞} (1/ζ(s)) x^s/s ds

This connects the Mertens function directly to the zeros of ζ.
The RH is equivalent to M(x) = O(x^{1/2+ε}) for all ε > 0.
[Titchmarsh 1986, Section 14.25; Schoenfeld 1976] -/

-- Future work: connect to ArithmeticFunction.moebius in Mathlib
-- and instantiate perron_formula for the Mertens function.

end -- noncomputable section
