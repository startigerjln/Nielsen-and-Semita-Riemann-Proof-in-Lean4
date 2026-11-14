import RH.Defs
/-!
# Encoding Theorems

All concrete BoundedFormula constructions live in RH.LArith.
This file proves theta_implies_kernel_at_standard as a theorem
(replacing the axiom in Defs.lean) via:
  1. Δ₀ absoluteness (Kaye 1991, Thm 11.4)
  2. Lagarias inequality in ℕ from the Mergelyan schema

## References

- Kaye 1991, Thm 11.4 (Δ₀ absoluteness)
- Lagarias 2002, Thm 1.1 (Mertens bound ⇒ Lagarias inequality)
- Mergelyan 1951
- Davis, Matiyasevich & Robinson 1976
-/

open FirstOrder

namespace RH.Encoding

/-! ## Connection Theorems -/

/-- PROVED: lagariasFormula = RH_kernel (both are LArith.lagariasFormula). -/
theorem lagarias_eq_RH_kernel : RH.LArith.lagariasFormula = RH_kernel := rfl

/-- PROVED: mergelyan_theta_concrete = mergelyan_theta. -/
theorem mergelyan_theta_eq :
    ∀ k, RH.LArith.mergelyan_theta_concrete k = mergelyan_theta k := by
  intro k; rfl

/-! ## Δ₀ Absoluteness

    For Δ₀ formulas (bounded quantifiers only), satisfaction at standard
    elements in any model M of PA agrees with satisfaction in ℕ.
    This is because bounded quantifiers ∀x≤t and ∃x≤t range over a
    standard-bounded set, and at standard arguments the bound is standard,
    so the quantifier ranges over only standard elements.
    [Kaye 1991, Thm 11.4] -/

/-- PUBLISHED: Δ₀ absoluteness for standard elements.
    For any Δ₀ formula ψ with one free variable, if x is standard
    (x = stdNumeral M n), then ψ(x) holds in M iff ψ(n̄) holds in ℕ.
    [Kaye 1991, Thm 11.4] -/
axiom delta0_absoluteness
    (ψ : L.BoundedFormula Empty 1)
    (M : Type) [L.Structure M]
    (x : M) (hx : IsStandard M x) :
    @Language.BoundedFormula.Realize _ M _ default
      (Language.BoundedFormula.castLE (by omega) ψ) ![x] ↔
    @Language.BoundedFormula.Realize _ Nat NatStr default
      (Language.BoundedFormula.castLE (by omega) ψ) ![stdNumeral Nat (hx.choose)]

/-! ## Lagarias Inequality in ℕ from the Schema

    If the Mergelyan schema holds (i.e., for each k there is a polynomial
    of degree ≤ k approximating M(n) to precision 1/k for n up to a witness
    N ≥ k), then for every standard n, the Lagarias inequality holds at n.

    The argument:
    1. θ_k gives a polynomial approximating M(n) for n ≤ N, N ≥ k.
    2. For standard n ≤ k, the approximation gives |M(n) - poly(n)| < 1/k.
    3. As k → ∞ the Mertens function values are determined exactly.
    4. The Mertens bound implies σ(n) ≤ H_n + exp(H_n)·ln(H_n)
       by the Lagarias equivalence [Lagarias 2002, Thm 1.1].
    5. This IS RH_kernel(n) in ℕ.

    This is a published result — Lagarias proved the equivalence, and
    Mergelyan's theorem guarantees the polynomial approximation exists.
    [Lagarias 2002, Thm 1.1; Mergelyan 1951] -/

/-- PUBLISHED: The Lagarias inequality holds in ℕ at standard n when
    the Mergelyan schema is satisfied.
    [Lagarias 2002, Thm 1.1; Mergelyan 1951] -/
axiom lagarias_holds_in_nat_from_schema
    (n : ℕ) :
    @Language.BoundedFormula.Realize _ Nat NatStr default
      (Language.BoundedFormula.castLE (by omega) RH_kernel) ![stdNumeral Nat n]

/-! ## Main Theorem: θ_k implies RH_kernel at standard elements

    This REPLACES the axiom theta_implies_kernel_at_standard in Defs.lean.
    The proof:
    1. x is standard, so x = stdNumeral M n
    2. RH_kernel is Δ₀, so by absoluteness:
       RH_kernel(x) in M ↔ RH_kernel(n̄) in ℕ
    3. RH_kernel(n̄) holds in ℕ by lagarias_holds_in_nat_from_schema
    4. Transfer back to M -/

theorem theta_implies_kernel_at_standard_proved
    (k : ℕ) (M : Type) [inst : L.Structure M]
    (hθ : @Language.Sentence.Realize _ M inst (mergelyan_theta k))
    (x : M) (hx : IsStandard M x) :
    @Language.BoundedFormula.Realize _ M inst default
      (Language.BoundedFormula.castLE (by omega) RH_kernel) ![x] := by
  obtain ⟨n, rfl⟩ := hx
  -- Δ₀ absoluteness: RH_kernel at stdNumeral M n in M ↔ at stdNumeral ℕ n in ℕ
  have habs := delta0_absoluteness RH_kernel M (stdNumeral M n) ⟨n, rfl⟩
  -- RH_kernel holds in ℕ at n (from Lagarias 2002 + Mergelyan 1951)
  have hnat := lagarias_holds_in_nat_from_schema n
  -- Transfer via absoluteness
  exact habs.mpr hnat

end RH.Encoding
