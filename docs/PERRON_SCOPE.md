# Perron Formula Formalization — Scope Document

## Goal

Formalize Perron's summation formula in Lean 4 as a reusable Mathlib
contribution, independent of any specific application (including RH).

## What Mathlib Already Has

### Directly relevant:
- `Analysis.MellinTransform` — Mellin transform, convergence, holomorphy in strips
- `Analysis.MellinInversion` — Mellin inversion formula (Lawrence Wu, 2024)
- `mellinInv σ f x = (1/2π) ∫ y, x^(-(σ+yi)) • f(σ+yi)` — vertical line integral
- `NumberTheory.LSeries.MellinEqDirichlet` — Mellin transform = Dirichlet series (David Loeffler)
- `NumberTheory.LSeries.Basic` — LSeries, convergence, summability
- `NumberTheory.LSeries.Convergence` — abscissa of convergence
- `Analysis.Complex.CauchyIntegral` — Cauchy integral formula, residues

### Building blocks:
- `MeasureTheory.Integral.CircleIntegral` — circle integrals
- `Analysis.SpecialFunctions.ImproperIntegrals` — improper integrals on half-lines
- `Analysis.Calculus.ParametricIntegral` — differentiation under the integral

### Key people working in this area:
- **David Loeffler** — LSeries, MellinEqDirichlet, Hurwitz zeta, Dirichlet L-functions
- **Lawrence Wu** — Mellin inversion
- **Michael Stoll** — LSeries infrastructure
- **Aaron Anderson** — original LSeries

## Proposed Module: `Mathlib.NumberTheory.LSeries.Perron`

### Theorem 1: Perron Kernel

Define the Perron kernel and its basic properties:

```
def perronKernel (x s : ℂ) : ℂ := x ^ s / s
```

Properties:
- Holomorphy away from s = 0
- Growth estimates on vertical lines
- Residue at s = 0 equals log(x) behavior

### Theorem 2: Truncated Perron Formula

The finite-height Perron formula with explicit error:

For a Dirichlet series F(s) = Σ a(n)/n^s convergent for Re(s) > σ_c,
and for x > 0 not an integer, c > max(0, σ_c), T > 0:

  Σ_{n ≤ x} a(n) = (1/2πi) ∫_{c-iT}^{c+iT} F(s) x^s/s ds + Error(x, T)

where |Error| is bounded by explicit terms involving:
- The abscissa of absolute convergence
- The growth of F on the contour
- The distance of x from the nearest integer

This is the workhorse version for applications.

### Theorem 3: Limiting Perron Formula

The T → ∞ limit (under appropriate growth conditions):

  Σ_{n ≤ x} a(n) = (1/2πi) ∫_{c-i∞}^{c+i∞} F(s) x^s/s ds

recoverable from the Mellin inversion already in Mathlib.

### Theorem 4: Application to Arithmetic Functions

Specialize to:
- The Möbius summatory function M(x) = Σ_{n ≤ x} μ(n)
  via the Dirichlet series 1/ζ(s)
- The Mertens function connection to RH

## Proposed Module: `Mathlib.Analysis.Complex.PolynomialApproximation.Mergelyan`

### Phase 1: Runge's Theorem
- Rational approximation on compact sets with finitely many holes
- Uses Cauchy integral already in Mathlib

### Phase 2: Mergelyan's Theorem
- Extension to boundary: continuous on K, holomorphic on int(K)
- Requires Vitushkin-type capacity arguments or the Lavrentiev approach

This is a longer-term project (weeks to months).

## Development Plan

### Week 1-2: Perron Kernel + Truncated Formula
- Define `perronKernel` and prove basic properties
- State and prove the truncated Perron formula
- Build on `mellinInv` and `hasSum_mellin`

### Week 3-4: Error Bounds + Applications
- Explicit error terms for the truncated formula
- Specialize to 1/ζ(s) for the Mertens function
- Connect to `RiemannHypothesis` in Mathlib

### Longer term: Mergelyan
- Runge's theorem first
- Full Mergelyan as follow-up

## How This Helps the RH Formalization

Once Perron is in Mathlib:
1. `mergelyan_schema_finitely_satisfiable` — still published axiom
   (Mergelyan not yet formalized)
2. `no_contour_no_certificate` — becomes a THEOREM from Perron
3. `perron_contour_gives_certificate` — becomes a THEOREM from Perron
4. `contour_fails_at_nonstandard` — the novel bridge, provable from
   Perron + overspill once the infrastructure exists

This eliminates ~3 published axioms from the RH formalization.
