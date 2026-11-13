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

* `perron_truncated`: The truncated Perron formula with explicit error term:
  `perronSum a x = perronIntegral (LSeries a) σ T x + O(error)`
  for `σ` to the right of the abscissa of absolute convergence and `T > 0`.

* `perron_formula`: The limiting Perron formula (T → ∞):
  `perronSum a x = mellinInv σ (fun s ↦ LSeries a s / s) x`
  under appropriate growth conditions.

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

/-! ## Perron Kernel Estimates

These estimates control the error in the truncated Perron formula. -/

/-- The standard Perron kernel estimate on a vertical line:
    `|x^(σ+it) / (σ+it)| ≤ x^σ / |t|` for `|t| ≥ 1`.
    [Titchmarsh 1986, Lemma 3.12] -/
theorem perronKernel_bound {x : ℝ} (hx : 0 < x) {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖perronKernel x (σ + t * I)‖ ≤ x ^ σ / |t| := by
  sorry -- TODO: prove from cpow estimates

/-- The Perron kernel integral for x > 1:
    `(1/2πi) ∫_{σ-i∞}^{σ+i∞} x^s/s ds = 1` when `σ > 0` and `x > 1`.
    This is the key identity: the vertical integral of the kernel
    is a step function.
    [Titchmarsh 1986, Lemma 3.12(A)] -/
theorem perronKernel_integral_gt_one {x : ℝ} (hx : 1 < x) {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun T => perronIntegral (fun s => 1) σ T x)
      Filter.atTop (nhds 1) := by
  sorry -- TODO: prove by residue calculus (pole at s=0, shift contour left)

/-- The Perron kernel integral for 0 < x < 1:
    `(1/2πi) ∫_{σ-i∞}^{σ+i∞} x^s/s ds = 0` when `σ > 0` and `0 < x < 1`.
    [Titchmarsh 1986, Lemma 3.12(B)] -/
theorem perronKernel_integral_lt_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun T => perronIntegral (fun s => 1) σ T x)
      Filter.atTop (nhds 0) := by
  sorry -- TODO: prove by shifting contour right (no poles, decay)

/-! ## The Truncated Perron Formula -/

/-- **Truncated Perron Formula**: For a Dirichlet series `F(s) = L a s`
    with abscissa of absolute convergence `σ_a`, for `σ > max(0, σ_a)`,
    `T > 0`, and `x > 0` not a positive integer:

    `Σ_{n ≤ x} a(n) = (1/2πi) ∫_{σ-iT}^{σ+iT} F(s) x^s/s ds + O(error)`

    where the error depends on `x`, `σ`, `T`, and the growth of `a`.

    [Perron 1908; Titchmarsh 1986, Theorem 3.12; Iwaniec-Kowalski 2004, Prop 5.1] -/
theorem perron_truncated (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : LSeriesSummable a σ)
    {x : ℝ} (hx : 0 < x) (hx_int : ∀ n : ℕ, (n : ℝ) ≠ x)
    {T : ℝ} (hT : 0 < T) :
    ∃ (E : ℂ), perronSum a x = perronIntegral (LSeries a) σ T x + E ∧
      ‖E‖ ≤ (x ^ σ / T) * ∑' n, ‖a n‖ / (n : ℝ) ^ σ := by
  sorry -- TODO: the main estimate

/-! ## The Limiting Perron Formula -/

/-- **Perron's Formula** (limiting version): Under appropriate growth conditions,
    as `T → ∞`:

    `Σ_{n ≤ x} a(n) = (1/2πi) ∫_{σ-i∞}^{σ+i∞} F(s) x^s/s ds`

    This follows from the truncated version by taking `T → ∞`.
    The integral on the right is `mellinInv` applied to `F(s)/s`.
    [Perron 1908; Titchmarsh 1986, Theorem 3.12] -/
theorem perron_formula (a : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hconv : LSeriesSummable a σ)
    {x : ℝ} (hx : 0 < x) (hx_int : ∀ n : ℕ, (n : ℝ) ≠ x) :
    Filter.Tendsto (fun T => perronIntegral (LSeries a) σ T x)
      Filter.atTop (nhds (perronSum a x)) := by
  sorry -- TODO: take T → ∞ in perron_truncated

/-! ## Application: Mertens Function

The Mertens function M(x) = Σ_{n ≤ x} μ(n) is the partial sum of the
Möbius function. By Perron's formula applied to the Dirichlet series
1/ζ(s) = Σ μ(n)/n^s:

  M(x) = (1/2πi) ∫_{σ-i∞}^{σ+i∞} (1/ζ(s)) x^s/s ds

This connects the Mertens function directly to the zeros of ζ.
The RH is equivalent to M(x) = O(x^{1/2+ε}) for all ε > 0,
which in turn is equivalent to 1/ζ(s) being holomorphic for Re(s) > 1/2.
[Titchmarsh 1986, Section 14.25] -/

-- TODO: Define μ (Möbius function) and connect to Mathlib's
-- ArithmeticFunction.moebius when available.
-- TODO: Define Mertens function as perronSum of μ.
-- TODO: State and prove the Perron representation of M(x).

end -- noncomputable section
