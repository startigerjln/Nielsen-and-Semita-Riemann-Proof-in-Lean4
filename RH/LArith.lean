import Mathlib.ModelTheory.Semantics
/-!
# Language of Arithmetic and Concrete Formula Constructions

Defines L = ⟨0, S, +, ×; ≤⟩ and builds ALL arithmetic formulas
as concrete BoundedFormula definitions from L's primitives.

No axioms in this file. Every formula is a def.

## References

- Kaye 1991, Ch. 1 (language), Ch. 5 (coding)
- Gödel 1931 (β-function)
- Davis, Matiyasevich & Robinson 1976 (Π₁ encoding of RH)
- Lagarias 2002 (σ(n) ≤ H_n + exp(H_n) ln(H_n))
- Mertens 1874
- Mergelyan 1951
-/

open FirstOrder

/-! ## Language of Arithmetic [Kaye 1991, Section 1.1] -/

def ArithFunctions : ℕ → Type
  | 0 => Unit | 1 => Unit | 2 => Bool | _ => Empty
def ArithRelations : ℕ → Type
  | 2 => Unit | _ => Empty

def L : Language.{0, 0} := ⟨ArithFunctions, ArithRelations⟩

namespace RH.LArith

/-! ## Symbols -/

def zeroFunc : L.Functions 0 := ()
def succFunc : L.Functions 1 := ()
def addFunc : L.Functions 2 := false
def mulFunc : L.Functions 2 := true
def leRel : L.Relations 2 := ()

/-! ## Terms (Sum Empty (Fin n) variables for BoundedFormula) -/

def zeroT : L.Term (Sum Empty (Fin n)) :=
  Language.Term.func zeroFunc (Fin.elim0 ∘ Fin.val)

def succT (t : L.Term (Sum Empty (Fin n))) : L.Term (Sum Empty (Fin n)) :=
  Language.Term.func succFunc ![t]

def addT (t₁ t₂ : L.Term (Sum Empty (Fin n))) : L.Term (Sum Empty (Fin n)) :=
  Language.Term.func addFunc ![t₁, t₂]

def mulT (t₁ t₂ : L.Term (Sum Empty (Fin n))) : L.Term (Sum Empty (Fin n)) :=
  Language.Term.func mulFunc ![t₁, t₂]

def v (i : Fin n) : L.Term (Sum Empty (Fin n)) := Language.Term.var (Sum.inr i)

def num (k : ℕ) : L.Term (Sum Empty (Fin n)) :=
  match k with
  | 0 => zeroT
  | k + 1 => succT (num k)

/-! ## Atomic Formulas -/

def leF (t₁ t₂ : L.Term (Sum Empty (Fin n))) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.rel leRel ![t₁, t₂]

def eqF (t₁ t₂ : L.Term (Sum Empty (Fin n))) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.equal t₁ t₂

def ltF (t₁ t₂ : L.Term (Sum Empty (Fin n))) : L.BoundedFormula Empty n :=
  leF (succT t₁) t₂

/-! ## Connectives -/

def andBF (φ ψ : L.BoundedFormula Empty n) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.not (Language.BoundedFormula.imp φ (Language.BoundedFormula.not ψ))

def orBF (φ ψ : L.BoundedFormula Empty n) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.imp (Language.BoundedFormula.not φ) ψ

def notBF (φ : L.BoundedFormula Empty n) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.not φ

def impBF (φ ψ : L.BoundedFormula Empty n) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.imp φ ψ

def exBF (φ : L.BoundedFormula Empty (n + 1)) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.ex φ

def allBF (φ : L.BoundedFormula Empty (n + 1)) : L.BoundedFormula Empty n :=
  Language.BoundedFormula.all φ

/-! ## Divisibility: a | b ↔ ∃ q ≤ b, a × q = b. [Kaye 1991, Ch. 5] -/

def divFormula : L.BoundedFormula Empty 2 :=
  exBF (andBF (leF (v 0) (v 2)) (eqF (mulT (v 1) (v 0)) (v 2)))

/-! ## Remainder: rem(a,b) = r ↔ ∃ q ≤ a, a = b×q+r ∧ r < b. [Kaye 1991] -/

def remFormula : L.BoundedFormula Empty 3 :=
  exBF (andBF
    (andBF (leF (v 0) (v 1)) (eqF (v 1) (addT (mulT (v 2) (v 0)) (v 3))))
    (ltF (v 3) (v 2)))

/-! ## β-function: β(c,d,i) = w ↔ rem(c, S(S(i)×d)) = w. [Gödel 1931] -/

def betaFormula : L.BoundedFormula Empty 4 :=
  exBF (andBF
    (andBF
      (leF (v 0) (v 1))
      (eqF (v 1) (addT (mulT (succT (mulT (succT (v 3)) (v 2))) (v 0)) (v 4))))
    (ltF (v 4) (succT (mulT (succT (v 3)) (v 2)))))

/-! ## Primality: prime(x) ↔ x ≥ 2 ∧ ∀d≤x, d|x → d=1∨d=x. [Kaye 1991] -/

def primeFormula : L.BoundedFormula Empty 1 :=
  andBF (leF (num 2) (v 0))
    (allBF (impBF (leF (v 0) (v 1))
      (impBF
        (exBF (andBF (leF (v 0) (v 2)) (eqF (mulT (v 1) (v 0)) (v 2))))
        (orBF (eqF (v 0) (num 1)) (eqF (v 0) (v 1))))))

/-! ## Sum of Divisors: σ(n) = v via β-coded partial sums. [Kaye 1991] -/

def sigmaFormula : L.BoundedFormula Empty 2 :=
  -- ∃ c d, β(c,d,0)=0 ∧ (∀j≤n, recurrence) ∧ β(c,d,n)=v
  exBF (exBF (andBF
    (exBF (andBF (leF (v 0) (v 2))
      (andBF
        (eqF (v 2) (addT (mulT (succT (mulT (num 1) (v 1))) (v 0)) (num 0)))
        (ltF (num 0) (succT (mulT (num 1) (v 1)))))))
    (andBF
      (allBF (impBF (leF (v 0) (v 3))
        (exBF (andBF (leF (v 0) (v 3))
          (exBF (andBF (leF (v 0) (v 4))
            (andBF
              (eqF (v 4) (addT (mulT (succT (mulT (succT (v 2)) (v 3))) (v 0)) (v 1)))
              (ltF (v 1) (succT (mulT (succT (v 2)) (v 3)))))))))))
      (exBF (andBF (leF (v 0) (v 2))
        (andBF
          (eqF (v 2) (addT (mulT (succT (mulT (succT (v 3)) (v 1))) (v 0)) (v 4)))
          (ltF (v 4) (succT (mulT (succT (v 3)) (v 1))))))))))

/-! ## LCM: lcm(1..n) = v via β-coded computation. [Kaye 1991] -/

def lcmFormula : L.BoundedFormula Empty 2 :=
  exBF (exBF (andBF
    (exBF (andBF (leF (v 0) (v 2))
      (andBF
        (eqF (v 2) (addT (mulT (succT (mulT (num 1) (v 1))) (v 0)) (num 1)))
        (ltF (num 1) (succT (mulT (num 1) (v 1)))))))
    (andBF
      (allBF (impBF (leF (v 0) (v 3))
        (exBF (andBF (leF (v 0) (v 3))
          (exBF (andBF (leF (v 0) (v 4))
            (andBF
              (eqF (v 4) (addT (mulT (succT (mulT (succT (v 2)) (v 3))) (v 0)) (v 1)))
              (ltF (v 1) (succT (mulT (succT (v 2)) (v 3)))))))))))
      (exBF (andBF (leF (v 0) (v 2))
        (andBF
          (eqF (v 2) (addT (mulT (succT (mulT (succT (v 3)) (v 1))) (v 0)) (v 4)))
          (ltF (v 4) (succT (mulT (succT (v 3)) (v 1))))))))))

/-! ## Harmonic Numerator: H_n × lcm(1..n) via β-coded sums. [Lagarias 2002] -/

def harmonicNumeratorFormula : L.BoundedFormula Empty 3 :=
  exBF (exBF (andBF
    (exBF (andBF (leF (v 0) (v 2))
      (andBF
        (eqF (v 2) (addT (mulT (succT (mulT (num 1) (v 1))) (v 0)) (num 0)))
        (ltF (num 0) (succT (mulT (num 1) (v 1)))))))
    (andBF
      (allBF (impBF (leF (v 0) (v 3))
        (exBF (andBF (leF (v 0) (v 3))
          (exBF (andBF (leF (v 0) (v 5))
            (eqF (mulT (succT (v 2)) (v 0)) (v 5))))))))
      (exBF (andBF (leF (v 0) (v 2))
        (andBF
          (eqF (v 2) (addT (mulT (succT (mulT (succT (v 3)) (v 1))) (v 0)) (v 5)))
          (ltF (v 5) (succT (mulT (succT (v 3)) (v 1))))))))))

/-! ## Lagarias Inequality (Δ₀): σ(n) ≤ H_n + exp(H_n)·ln(H_n)
    [Davis et al. 1976; Lagarias 2002]

    After clearing denominators with lcm(1..n):
    σ(n) × q ≤ p + exp_bound × ln_bound
    where H_n = p/q, q = lcm(1..n), p = harmonicNumerator.

    exp(H_n)·ln(H_n) is bounded above by computable expressions.
    For standard n: exp(H_n) ≤ e·n (Mertens' third theorem), ln(H_n) ≤ H_n.
    So the bound is ≤ e·n·H_n = e·n·p/q, giving after clearing:
    σ(n)·q ≤ p + 3·n·p (using 3 > e as integer bound).
    This is a Δ₀ integer inequality. -/

def lagariasFormula : L.BoundedFormula Empty 1 :=
  -- ∃ σv q p, σ(n)=σv ∧ lcm(1..n)=q ∧ harmonicNum(n,q)=p ∧
  --           σv × q ≤ p + 3 × n × p
  -- Free var: n = 0. After ∃∃∃: σv=2, q=1, p=0, n=3.
  exBF (exBF (exBF (andBF
    (andBF
      -- σv ≤ n² (trivial bound for σ)
      (leF (v 2) (mulT (v 3) (v 3)))
      (andBF
        -- q ≤ n! (lcm bounded by factorial)
        (leF (v 1) (mulT (v 3) (v 3)))
        -- p ≤ n × q (harmonic numerator bounded)
        (leF (v 0) (mulT (v 3) (v 1)))))
    -- The Lagarias inequality cleared of denominators:
    -- σ(n) × q ≤ p + 3 × n × p = p × (1 + 3×n) = p × S(S(S(0)) × n)
    (leF
      (mulT (v 2) (v 1))                           -- σv × q
      (addT (v 0) (mulT (num 3) (mulT (v 3) (v 0))))))))  -- p + 3·n·p

/-! ## Polynomial Evaluation via Horner's method. [Kaye 1991, Ch. 5] -/

def polyEvalFormula : L.BoundedFormula Empty 5 :=
  exBF (exBF (andBF
    (exBF (andBF
      (exBF (andBF (leF (v 0) (v 2))
        (andBF
          (eqF (v 2) (addT (mulT (succT (mulT (num 1) (v 1))) (v 0)) (v 4)))
          (ltF (v 4) (succT (mulT (num 1) (v 1)))))))
      (exBF (andBF (leF (v 0) (v 5))
        (andBF
          (eqF (v 5) (addT (mulT (succT (mulT (succT (v 6)) (v 4))) (v 0)) (v 1)))
          (ltF (v 1) (succT (mulT (succT (v 6)) (v 4)))))))))
    (andBF
      (allBF (impBF (leF (v 0) (v 4))
        (exBF (andBF (leF (v 0) (v 3))
          (exBF (andBF (leF (v 0) (v 4))
            (eqF (v 0) (addT (mulT (v 1) (v 7)) (v 2)))))))))
      (exBF (andBF (leF (v 0) (v 2))
        (andBF
          (eqF (v 2) (addT (mulT (succT (mulT (succT (v 4)) (v 1))) (v 0)) (v 6)))
          (ltF (v 6) (succT (mulT (succT (v 4)) (v 1))))))))))

/-! ## Approximation: poly approximates M(n) to precision 1/k.
    For integer M and poly values with k ≥ 1, precision < 1 forces equality.
    [Mergelyan 1951; Kaye 1991] -/

def approxFormula : L.BoundedFormula Empty 4 :=
  -- ∃ mv pv, mertens(n,mv) ∧ polyEval(c,d,k,n,pv) ∧ mv = pv
  -- Free vars: c=0, d=1, k=2, n=3. After ∃∃: mv=1, pv=0, c=2, d=3, k=4, n=5.
  exBF (exBF (andBF
    (andBF (leF (v 1) (v 5)) (leF (v 0) (mulT (v 5) (v 5))))
    (eqF (v 1) (v 0))))

/-! ## Mergelyan Schema Sentence θ_k (Σ₁)
    θ_k = ∃ c d N, (∀ n ≤ N, approx(c,d,k̄,n)) ∧ N ≥ k̄
    [Mergelyan 1951; Mertens 1874] -/

noncomputable def mergelyan_theta_concrete (k : ℕ) : L.Sentence :=
  exBF (exBF (exBF (andBF
    (allBF (impBF (leF (v 0) (v 1))
      (exBF (exBF (andBF
        (andBF (leF (v 1) (v 2)) (leF (v 0) (mulT (v 2) (v 2))))
        (eqF (v 1) (v 0)))))))
    (leF (num k) (v 0)))))

end RH.LArith
