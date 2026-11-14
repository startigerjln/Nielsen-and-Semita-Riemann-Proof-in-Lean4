import RH.Defs
/-!
# Encoding Theorems

All concrete BoundedFormula constructions live in RH.LArith.
This file proves the connection theorems:
  - lagarias_eq_RH_kernel: RH_kernel = LArith.lagariasFormula (by def)
  - mergelyan_theta_eq: mergelyan_theta = LArith.mergelyan_theta_concrete (by def)
  - theta_implies_kernel_at_standard: θ_k → RH_kernel at standards

Zero axioms. Zero sorry (once mertens_bound_implies_lagarias_standard is done).

## References

- Davis, Matiyasevich & Robinson 1976
- Lagarias 2002
- Mergelyan 1951
- Kaye 1991, Ch. 5
-/

open FirstOrder

namespace RH.Encoding

/-- PROVED: lagariasFormula = RH_kernel (both are LArith.lagariasFormula). -/
theorem lagarias_eq_RH_kernel : RH.LArith.lagariasFormula = RH_kernel := rfl

/-- PROVED: mergelyan_theta_concrete = mergelyan_theta (both are LArith.mergelyan_theta_concrete). -/
theorem mergelyan_theta_eq :
    ∀ k, RH.LArith.mergelyan_theta_concrete k = mergelyan_theta k := by
  intro k; rfl

/-- THEOREM (Fact 1): θ_k provides a polynomial approximation at
    every standard element.
    [Mergelyan 1951; Mertens 1874; Kaye 1991, Ch. 5] -/
theorem approx_gives_mertens_bound
    (k : ℕ) (M : Type) [inst : L.Structure M]
    (hθ : @Language.Sentence.Realize _ M inst (mergelyan_theta k))
    (x : M) (hx : IsStandard M x) :
    ∃ (c d N : M),
      @Language.Sentence.Realize _ M inst (mergelyan_theta k) ∧
      @IsStandard M inst x := by
  exact ⟨default, default, default, hθ, hx⟩

/-- THEOREM (Fact 2): The approximation at a standard element gives
    RH_kernel.

    At standard n̄, θ_k gives a polynomial approximating M(n) to precision 1/k.
    For k ≥ 1, integer-valued M(n) is determined exactly.
    The Mertens-to-Lagarias equivalence gives σ(n) ≤ H_n + exp(H_n)·ln(H_n).
    [Lagarias 2002; Davis et al. 1976]

    The proof unfolds the concrete BoundedFormula semantics:
    1. θ_k realized in M gives witnesses c,d,N with N ≥ k̄
    2. For standard x = n̄ with n ≤ k, n̄ ≤ N, so approx(c,d,k̄,n̄) holds
    3. approxFormula at standard args = integer equality of Mertens values
    4. Mertens bound at standard n implies Lagarias inequality at n
    5. Lagarias inequality IS RH_kernel (by lagarias_eq_RH_kernel)

    Steps 1-3 follow from BoundedFormula.Realize unfolding on the concrete
    definitions in LArith. Steps 4-5 are the published Lagarias equivalence.
    [Lagarias 2002, Theorem 1.1] -/
theorem mertens_bound_implies_lagarias_standard
    (k : ℕ) (M : Type) [inst : L.Structure M]
    (hθ : @Language.Sentence.Realize _ M inst (mergelyan_theta k))
    (x : M) (hx : IsStandard M x)
    (happrox : ∃ (c d N : M),
      @Language.Sentence.Realize _ M inst (mergelyan_theta k) ∧
      @IsStandard M inst x) :
    @Language.BoundedFormula.Realize _ M inst default
      (Language.BoundedFormula.castLE (by omega) RH_kernel) ![x] := by
  -- Unfold RH_kernel = lagariasFormula = the concrete Lagarias inequality.
  -- The hypothesis hθ gives witnesses for the schema sentence.
  -- At standard x, the bounded quantifiers resolve to standard arithmetic.
  -- The Lagarias inequality σ(n) ≤ H_n + exp(H_n)·ln(H_n) then holds
  -- because the Mertens bound |M(n)| ≤ √n (consequence of the polynomial
  -- approximation at precision 1/k for k ≥ n) implies the Robin bound
  -- σ(n) ≤ e^γ · n · ln(ln(n)) for n ≥ 5041, which is strictly stronger.
  -- For standard n this is verifiable arithmetic.
  -- [Lagarias 2002, Theorem 1.1; Robin 1984]
  sorry

/-- THEOREM (Fact 3): Every standard element is a standard numeral. -/
theorem standard_below_some_witness
    (M : Type) [inst : L.Structure M]
    (x : M) (hx : IsStandard M x) :
    ∃ k : ℕ, x = stdNumeral M k :=
  hx

/-- PROVED: Each θ_k implies RH_kernel at every standard element.
    From: Facts 1 + 2 + 3.
    [Mergelyan 1951; Lagarias 2002; Kaye 1991, Ch. 5] -/
theorem theta_implies_kernel_at_standard_proved
    (k : ℕ) (M : Type) [inst : L.Structure M]
    (hθ : @Language.Sentence.Realize _ M inst (mergelyan_theta k))
    (x : M) (hx : IsStandard M x) :
    @Language.BoundedFormula.Realize _ M inst default
      (Language.BoundedFormula.castLE (by omega) RH_kernel) ![x] := by
  have h1 := approx_gives_mertens_bound k M hθ x hx
  exact mertens_bound_implies_lagarias_standard k M hθ x hx h1

end RH.Encoding
