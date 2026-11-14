import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.Connected.Basic
/-!
# Published analysis, stated in its own language

Each axiom in this file is a published theorem of analysis, stated over
`ℂ`, `ℝ` and Mathlib's `riemannZeta`. Nothing here mentions `ZModel`,
precision indices, the Mergelyan schema, or any other object of the main
construction. Anything that connects these statements to the model-level
construction is a separate theorem and does not belong in this file.

These are axioms only because their proofs are not yet in Mathlib.
-/

namespace RH.Published

/-! ## Mergelyan's theorem -/

/-- **Mergelyan's theorem** (Mergelyan 1951; Rudin, *Real and Complex
    Analysis*, 3rd ed., Theorem 20.5).

    If `K ⊂ ℂ` is compact with connected complement, and `f` is continuous
    on `K` and holomorphic on the interior of `K`, then for every `ε > 0`
    there is a polynomial `p` with `|f z - p z| < ε` for all `z ∈ K`. -/
axiom mergelyan (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    (f : ℂ → ℂ) (hf : ContinuousOn f K)
    (hf' : DifferentiableOn ℂ f (interior K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε

/-! ## Zero density for the Riemann zeta function -/

/-- The zeros `ρ = β + iγ` of `ζ` with `β > σ` and `0 < γ ≤ T`. -/
def zetaZeroSet (σ T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- `N(σ, T)`: the number of zeros of `ζ` with real part `> σ` and
    imaginary part in `(0, T]`, counted here as distinct points.
    (The literature counts with multiplicity; an upper bound for that
    count is also an upper bound for this one.) -/
noncomputable def zetaZeroCount (σ T : ℝ) : ℕ := (zetaZeroSet σ T).ncard

/-- **Ingham's zero-density estimate** (Ingham 1940; Titchmarsh, *The
    Theory of the Riemann Zeta-Function*, 2nd ed., Ch. 9).

    Uniformly for `1/2 ≤ σ ≤ 1` and `T ≥ 2`,
    `N(σ, T) ≤ C · T^(3(1-σ)/(2-σ)) · (log T)^5`.

    This is an UPPER bound on the number of zeros to the right of the
    line `Re s = σ`. -/
axiom ingham_zero_density :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤
        C * T ^ (3 * (1 - σ) / (2 - σ)) * (Real.log T) ^ (5 : ℕ)

end RH.Published
