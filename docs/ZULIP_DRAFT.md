# Draft: Mathlib Zulip Message

**Stream:** #mathlib4
**Topic:** Perron's formula + Mergelyan's theorem — interest in formalizing?

---

Hi all,

I'm J. L. Nielsen (Center for Topological Physics). I've been working on a Lean 4 + Mathlib formalization of analytic number theory results, and I've identified two classical theorems that Mathlib doesn't yet have but that would be broadly useful:

## 1. Perron's Summation Formula

The classical result connecting Dirichlet series coefficients to their partial sums via a vertical contour integral:

  Σ_{n ≤ x} a(n) = (1/2πi) ∫_{c-iT}^{c+iT} F(s) x^s/s ds + O(error)

Mathlib already has excellent infrastructure for this:
- `Analysis.MellinTransform` and `Analysis.MellinInversion` (the vertical line integral `mellinInv` is essentially the Perron contour)
- `NumberTheory.LSeries.MellinEqDirichlet` (David Loeffler's Mellin = Dirichlet series connection)
- `Analysis.Complex.CauchyIntegral` (Cauchy integral formula)

I think the truncated Perron formula with explicit error bounds would be a natural next module in the LSeries development. The limiting version might even follow from the existing Mellin inversion.

**Proposed location:** `Mathlib.NumberTheory.LSeries.Perron`

## 2. Mergelyan's Theorem (longer term)

Complex polynomial approximation on compact sets with connected complement:

  For compact K ⊂ ℂ with connected complement, any f continuous on K
  and holomorphic on int(K) can be uniformly approximated by polynomials.

Mathlib has Stone-Weierstrass for the real case (`Topology.ContinuousMap.StoneWeierstrass`) and Weierstrass approximation (`Topology.ContinuousMap.Weierstrass`), but not the complex analytic version. Mergelyan is strictly stronger and widely used in complex analysis and number theory.

A natural route would be Runge's theorem first (rational approximation, using the existing Cauchy integral), then extending to Mergelyan.

**Proposed location:** `Mathlib.Analysis.Complex.PolynomialApproximation.Mergelyan`

## Context

These came up in a formalization project where both theorems are currently axiomatized as published results. Having them as proved Mathlib theorems would be valuable independently — they're standard tools in complex analysis and analytic number theory that many formalizations could use.

I'd be happy to contribute to either effort. Before starting, I wanted to check:
1. Is anyone already working on Perron's formula or Mergelyan?
2. For Perron specifically, does the existing Mellin inversion + MellinEqDirichlet approach seem like the right starting point, or would you recommend a different route?
3. Any preferences on module organization?

Thanks!
Jenny (J. L. Nielsen)

---

*Note: This message deliberately does NOT mention RH. The contributions stand on their own as classical analysis infrastructure. The RH connection can come later once the tools exist.*
