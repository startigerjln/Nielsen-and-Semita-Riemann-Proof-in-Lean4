import Mathlib.ModelTheory.Semantics
/-!
# Language of arithmetic, the standard model, and Δ₀ formulas

Definitions only. No axioms.

* `L` : the language ⟨0, S, +, ×; ≤⟩ of first-order arithmetic.
* `natStructure` : the standard interpretation of `L` on `ℕ`.
* `IsDelta0` : formulas all of whose quantifiers are bounded (`∀ x ≤ t`).
  Mathlib's `BoundedFormula` bounds the number of free variables, not the
  quantifiers, so Δ₀ has to be defined separately.
-/

open FirstOrder

namespace RH.Paper

def ArithFunctions : ℕ → Type
  | 0 => Unit | 1 => Unit | 2 => Bool | _ => Empty

def ArithRelations : ℕ → Type
  | 2 => Unit | _ => Empty

/-- The language of first-order arithmetic. -/
def L : Language.{0, 0} := ⟨ArithFunctions, ArithRelations⟩

def zeroFunc : L.Functions 0 := ()
def succFunc : L.Functions 1 := ()
def addFunc : L.Functions 2 := false
def mulFunc : L.Functions 2 := true
def leRel : L.Relations 2 := ()

/-- The standard model: `ℕ` with 0, successor, +, × and ≤. -/
instance natStructure : L.Structure ℕ where
  funMap := fun {n} (f : ArithFunctions n) xs =>
    match n, f, xs with
    | 0, _, _ => 0
    | 1, _, xs => xs 0 + 1
    | 2, false, xs => xs 0 + xs 1
    | 2, true, xs => xs 0 * xs 1
    | _ + 3, f, _ => nomatch f
  RelMap := fun {n} (r : ArithRelations n) xs =>
    match n, r, xs with
    | 0, r, _ => nomatch r
    | 1, r, _ => nomatch r
    | 2, _, xs => xs 0 ≤ xs 1
    | _ + 3, r, _ => nomatch r

/-- The atomic formula `t₁ ≤ t₂`. -/
def leF {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.rel leRel ![t₁, t₂]

/-- Δ₀ formulas: built from atomic formulas by implication (hence all
    Boolean connectives) and bounded universal quantification
    `∀ x ≤ t, φ`, where the bound `t` does not mention `x`. -/
inductive IsDelta0 : ∀ {n : ℕ}, L.BoundedFormula Empty n → Prop
  | falsum {n : ℕ} : IsDelta0 (Language.BoundedFormula.falsum : L.BoundedFormula Empty n)
  | equal {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) :
      IsDelta0 (Language.BoundedFormula.equal t₁ t₂)
  | rel {n k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (Empty ⊕ Fin n)) :
      IsDelta0 (Language.BoundedFormula.rel R ts)
  | imp {n : ℕ} {φ ψ : L.BoundedFormula Empty n} :
      IsDelta0 φ → IsDelta0 ψ → IsDelta0 (φ.imp ψ)
  | bdAll {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) {φ : L.BoundedFormula Empty (n + 1)} :
      IsDelta0 φ →
      IsDelta0 (Language.BoundedFormula.all
        ((leF (Language.Term.var (Sum.inr (Fin.last n)))
              (t.relabel (Sum.map id Fin.castSucc))).imp φ))

end RH.Paper
