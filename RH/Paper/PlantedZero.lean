import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.NormNum

namespace RH.Paper.PlantedZero

abbrev Point := ℚ × ℚ

private def add (z w : Point) : Point :=
  (z.1 + w.1, z.2 + w.2)

private def sub (z w : Point) : Point :=
  (z.1 - w.1, z.2 - w.2)

private def mul (z w : Point) : Point :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Evaluate a polynomial with Gaussian-rational coefficients by Horner's rule.
    Coefficients are listed starting with the constant coefficient. -/
def evalPolynomial (z : Point) (coefficients : List Point) : Point :=
  coefficients.foldr (fun a value => add a (mul z value)) (0, 0)

/-- Numerator factors, remaining numerator coefficients, and denominator
    coefficients of a rational-function code. -/
abbrev RationalFunction := List Point × List Point × List Point

def evalNumerator (f : RationalFunction) (z : Point) : Point :=
  f.1.foldr (fun root value => mul (sub z root) value) (evalPolynomial z f.2.1)

/-- Exact rational check for a zero, excluding poles and removable
    singularities where the coded quotient is undefined. -/
def isZeroAt (f : RationalFunction) (z : Point) : Prop :=
  evalNumerator f z = (0, 0) ∧ evalPolynomial z f.2.2 ≠ (0, 0)

instance (f : RationalFunction) (z : Point) : Decidable (isZeroAt f z) := by
  unfold isZeroAt
  infer_instance

def criticalLineCheck (z : Point) (k : ℕ) : Prop :=
  |z.1 - 1 / 2| < (1 / 2 : ℚ) ^ k

instance (z : Point) (k : ℕ) : Decidable (criticalLineCheck z k) := by
  unfold criticalLineCheck
  infer_instance

/-- A zero certificate names the point by its natural-number code. -/
def passes (m n k : ℕ) : Prop :=
  match Encodable.decode (α := RationalFunction) m, Encodable.decode (α := Point) n with
  | some f, some z => isZeroAt f z → criticalLineCheck z k
  | _, _ => True

instance (m n k : ℕ) : Decidable (passes m n k) := by
  unfold passes
  split <;> infer_instance

def plantedPoint (N : ℕ) : Point :=
  (3 / 4, (N : ℚ) + 1)

/-- The reflected and conjugate points accompany the planted zero. -/
def plant (N : ℕ) (f : RationalFunction) : RationalFunction :=
  let height := (N : ℚ) + 1
  ([plantedPoint N, (3 / 4, -height), (1 / 4, height), (1 / 4, -height)] ++ f.1, f.2)

theorem planted_isZeroAt (N : ℕ) (f : RationalFunction)
    (defined : evalPolynomial (plantedPoint N) f.2.2 ≠ (0, 0)) :
    isZeroAt (plant N f) (plantedPoint N) := by
  refine ⟨?_, defined⟩
  simp [evalNumerator, plant, sub, mul]

theorem planted_fails_precision (N : ℕ) : ¬ criticalLineCheck (plantedPoint N) 3 := by
  norm_num [criticalLineCheck, plantedPoint, abs_of_nonneg]

/-- A concrete standard counterexample to the coded zero-location test.
    All three inputs are ordinary natural numbers. -/
theorem planted_code_fails (N : ℕ) (f : RationalFunction)
    (defined : evalPolynomial (plantedPoint N) f.2.2 ≠ (0, 0)) :
    ¬ passes (Encodable.encode (plant N f)) (Encodable.encode (plantedPoint N)) 3 := by
  intro h
  have hcheck : isZeroAt (plant N f) (plantedPoint N) → criticalLineCheck (plantedPoint N) 3 := by
    simpa only [passes, Encodable.encodek] using h
  exact planted_fails_precision N (hcheck (planted_isZeroAt N f defined))

/-- For the direct zero-location check, standard witnesses exist at
    arbitrarily large imaginary height. Use the constant-one quotient
    before inserting the four numerator factors. -/
theorem exists_standard_failing_code (N : ℕ) :
    ∃ m : ℕ, ¬ passes m (Encodable.encode (plantedPoint N)) 3 :=
  ⟨Encodable.encode (plant N ([], [(1, 0)], [(1, 0)])),
    planted_code_fails N ([], [(1, 0)], [(1, 0)]) (by simp [evalPolynomial, add, mul])⟩

/-- The arithmetic part of the finite-witness argument, with local
    validity and the size of the code supplied by the approximation step. -/
theorem finite_checks_with_failure (validAt : ℕ → ℕ → Prop)
    (approximants : ∀ N : ℕ, ∃ f : RationalFunction,
      evalPolynomial (plantedPoint N) f.2.2 ≠ (0, 0) ∧
      N < Encodable.encode (plant N f) ∧
      ∀ k ≤ N, validAt (Encodable.encode (plant N f)) k)
    (bounds checks : Finset ℕ) :
    ∃ m n : ℕ, (∀ b ∈ bounds, b < m) ∧ (∀ k ∈ checks, validAt m k) ∧ ¬ passes m n 3 := by
  let N := (bounds ∪ checks).sup id
  obtain ⟨f, defined, large, valid⟩ := approximants N
  refine ⟨Encodable.encode (plant N f), Encodable.encode (plantedPoint N), ?_, ?_,
    planted_code_fails N f defined⟩
  · intro b hb
    exact lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_union_left _ hb)) large
  · intro k hk
    exact valid k (Finset.le_sup (f := id) (Finset.mem_union_right _ hk))

end RH.Paper.PlantedZero
