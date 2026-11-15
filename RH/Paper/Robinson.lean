import RH.Paper.Arith
import Mathlib.ModelTheory.Satisfiability

/-!
# Published arithmetic input for finite-witness reflection

The eight sentences below are Robinson arithmetic Q, with its definitional
extension by `≤`. They follow Definition 3.1 of the Charles University
Mathematical Logic notes:
https://www.mff.cuni.cz/data/web/obsah/department_math/ka/MathLogic.pdf

The sole external axiom is the one-existential-variable instance of the
published Σ₁-completeness theorem for Q, expressed using semantic consequence
(by soundness of first-order logic). See L. D. Beklemishev,
"Gödel incompleteness theorems and the limits of their applicability. I",
Russian Mathematical Surveys 65 (2010), Theorem 6, §3.5:
https://homepage.mi-ras.ru/~bekl/Papers/goedel-en.pdf
Also Theorem 3.10 of the notes above. It mentions neither RH nor a translation.
-/

open FirstOrder

namespace RH.Paper.Robinson

private abbrev Term (n : ℕ) := L.Term (Empty ⊕ Fin n)
private def x {n : ℕ} (i : Fin n) : Term n := .var (.inr i)
private def zero {n : ℕ} : Term n := .func zeroFunc ![]
private def succ {n : ℕ} (t : Term n) : Term n := .func succFunc ![t]
private def add {n : ℕ} (s t : Term n) : Term n := .func addFunc ![s, t]
private def mul {n : ℕ} (s t : Term n) : Term n := .func mulFunc ![s, t]
private def eq {n : ℕ} (s t : Term n) : L.BoundedFormula Empty n := .equal s t

/-- `∀ x y, S x = S y → x = y`. -/
def successorInjective : L.Sentence :=
  ((eq (succ (x 0)) (succ (x 1))).imp (eq (x 0) (x 1))).all.all
/-- `∀ x, S x ≠ 0`. -/
def successorNonzero : L.Sentence := (eq (succ (x 0)) zero).not.all
/-- `∀ x, x ≠ 0 → ∃ y, S y = x`. -/
def predecessor : L.Sentence :=
  ((eq (x 0) zero).not.imp (eq (succ (x 1)) (x 0)).ex).all
/-- `∀ x, x + 0 = x`. -/
def addZero : L.Sentence := (eq (add (x 0) zero) (x 0)).all
/-- `∀ x y, x + S y = S (x + y)`. -/
def addSuccessor : L.Sentence :=
  (eq (add (x 0) (succ (x 1))) (succ (add (x 0) (x 1)))).all.all
/-- `∀ x, x * 0 = 0`. -/
def mulZero : L.Sentence := (eq (mul (x 0) zero) zero).all
/-- `∀ x y, x * S y = x * y + x`. -/
def mulSuccessor : L.Sentence :=
  (eq (mul (x 0) (succ (x 1))) (add (mul (x 0) (x 1)) (x 0))).all.all
/-- `∀ x y, x ≤ y ↔ ∃ z, z + x = y`. -/
def orderDefinition : L.Sentence :=
  ((leF (x 0) (x 1)).iff (eq (add (x 2) (x 0)) (x 1)).ex).all.all

/-- The fixed, explicitly specified published theory Q. -/
def Q : L.Theory :=
  {successorInjective, successorNonzero, predecessor, addZero,
   addSuccessor, mulZero, mulSuccessor, orderDefinition}

/-- Published Σ₁-completeness of Q (Beklemishev, Theorem 6), followed by
first-order soundness. The bounded matrix is arbitrary; there is no RH-specific
premise or conclusion. This external theorem has not been proved in this repo. -/
axiom sigma1_complete (ψ : L.BoundedFormula Empty 1) (bounded : IsDelta0 ψ)
    (trueInN : @Language.Sentence.Realize L ℕ natStructure ψ.ex) :
    Q ⊨ᵇ ψ.ex

end RH.Paper.Robinson
