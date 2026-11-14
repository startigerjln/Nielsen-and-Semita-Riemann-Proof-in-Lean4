import RH.Defs
/-!
# Published logic, stated in its own language

This file states the overspill lemma for structures in the language of
arithmetic `L`, with no reference to `ZModel`, the Mergelyan schema, or
any other object of the main construction.

The lemma is PROVED here from the induction scheme. It is not an axiom.

Source: R. Kaye, *Models of Peano Arithmetic* (1991), the overspill lemma.
Kaye's statement gives a nonstandard `c` with `φ(x)` for all `x ≤ c`.
The form proved here is the consequence "`φ(c)` for some nonstandard `c`".

Note what the lemma does and does not say: a formula true at every
standard number is true at SOME nonstandard element. It does not say
the formula is true at ALL elements.
-/

open FirstOrder

namespace RH.Published

/-- The interpretation of the constant `0` in an `L`-structure. -/
def zeroM (M : Type) [L.Structure M] : M :=
  Language.Structure.funMap (L := L) (M := M) (n := 0)
    (show L.Functions 0 from ()) ![]

/-- The interpretation of the successor function in an `L`-structure. -/
def succM {M : Type} [L.Structure M] (x : M) : M :=
  Language.Structure.funMap (L := L) (M := M) (n := 1)
    (show L.Functions 1 from ()) ![x]

/-- The standard numerals `0, S 0, S (S 0), ...` inside an `L`-structure. -/
def numeral (M : Type) [L.Structure M] : ℕ → M
  | 0 => zeroM M
  | n + 1 => succM (numeral M n)

/-- An element is standard if it is a numeral. -/
def IsStandard {M : Type} [L.Structure M] (x : M) : Prop :=
  ∃ n : ℕ, x = numeral M n

/-- The induction scheme, for every `L`-formula with parameters.
    This holds in every model of Peano arithmetic. -/
def SatisfiesInduction (M : Type) [L.Structure M] : Prop :=
  ∀ (α : Type) (φ : L.BoundedFormula α 1) (v : α → M),
    φ.Realize v ![zeroM M] →
    (∀ x : M, φ.Realize v ![x] → φ.Realize v ![succM x]) →
    ∀ x : M, φ.Realize v ![x]

/-- **Overspill** (Kaye 1991). In a nonstandard structure satisfying
    induction, a formula (with parameters) that holds at every standard
    number holds at some nonstandard element.

    PROVED: if `φ` held at no nonstandard element it would define the
    standard numbers, which are closed under successor, so induction
    would make every element standard. -/
theorem overspill {M : Type} [L.Structure M]
    (hInd : SatisfiesInduction M)
    (hns : ∃ x : M, ¬ IsStandard x)
    {α : Type} (φ : L.BoundedFormula α 1) (v : α → M)
    (h : ∀ n : ℕ, φ.Realize v ![numeral M n]) :
    ∃ c : M, ¬ IsStandard c ∧ φ.Realize v ![c] := by
  by_contra hcon
  have hstd : ∀ x : M, φ.Realize v ![x] → IsStandard x := by
    intro x hx
    by_contra hx'
    exact hcon ⟨x, hx', hx⟩
  have hall : ∀ x : M, φ.Realize v ![x] := by
    apply hInd α φ v
    · exact h 0
    · intro x hx
      obtain ⟨n, rfl⟩ := hstd x hx
      exact h (n + 1)
  obtain ⟨x, hx⟩ := hns
  exact hx (hstd x (hall x))

end RH.Published
