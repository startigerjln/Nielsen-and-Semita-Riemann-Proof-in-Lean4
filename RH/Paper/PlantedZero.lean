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

@[simp] theorem evalPolynomial_one (z : Point) :
    evalPolynomial z [(1, 0)] = (1, 0) := by
  simp [evalPolynomial, add, mul]

theorem evalPolynomial_one_padded (z : Point) (length : ℕ) :
    evalPolynomial z ((1, 0) :: List.replicate length (0, 0)) = (1, 0) := by
  have zeroEval : ∀ n : ℕ, evalPolynomial z (List.replicate n (0, 0)) = (0, 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa [List.replicate_succ, evalPolynomial, add, mul] using
        congrArg (fun v => add (0, 0) (mul z v)) ih
  change add (1, 0) (mul z (evalPolynomial z (List.replicate length (0, 0)))) = _
  rw [zeroEval length]
  simp [add, mul]

/-- Numerator factors, remaining numerator coefficients, and denominator
    coefficients of a rational-function code. -/
abbrev RationalFunction := List Point × List Point × List Point

private theorem list_length_le_encode (points : List Point) :
    points.length ≤ Encodable.encode points := by
  induction points with
  | nil => simp
  | cons z points ih =>
    change points.length + 1 ≤ Nat.pair (Encodable.encode z) (Encodable.encode points) + 1
    exact Nat.succ_le_succ (ih.trans (Nat.right_le_pair _ _))

theorem denominator_length_le_code (f : RationalFunction) :
    f.2.2.length ≤ Encodable.encode f := by
  rw [show f = (f.1, f.2.1, f.2.2) from rfl, Encodable.encode_prod_val, Encodable.encode_prod_val]
  exact (list_length_le_encode _).trans ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))

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
def plantedRoots (N : ℕ) : List Point :=
  let height := (N : ℚ) + 1
  [plantedPoint N, (3 / 4, -height), (1 / 4, height), (1 / 4, -height)]

def plant (N : ℕ) (f : RationalFunction) : RationalFunction :=
  (plantedRoots N ++ f.1, f.2)

theorem planted_isZeroAt (N : ℕ) (f : RationalFunction)
    (defined : evalPolynomial (plantedPoint N) f.2.2 ≠ (0, 0)) :
    isZeroAt (plant N f) (plantedPoint N) := by
  refine ⟨?_, defined⟩
  simp [evalNumerator, plant, plantedRoots, sub, mul]

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

/-- A single-root rational-function code passes every candidate point check
    through precision `K`, and fails at precision `K + 2`. The size
    bound allows any finite lower bounds on the named continuation code. -/
theorem exists_code_passing_precision_prefix_and_failing (K bound : ℕ) :
    ∃ m n : ℕ, bound < m ∧ (∀ j k : ℕ, k ≤ K → passes m j k) ∧
      ¬ passes m n (K + 2) := by
  let distance := (1 / 2 : ℚ) ^ (K + 2)
  let root : Point := (1 / 2 + distance, (bound : ℚ) + 1)
  let f : RationalFunction := ([root], [(1, 0)], (1, 0) :: List.replicate bound (0, 0))
  have zero_iff (z : Point) : isZeroAt f z ↔ z = root := by
    rcases z with ⟨x, y⟩
    change (evalNumerator f (x, y) = (0, 0) ∧
      evalPolynomial (x, y) ((1, 0) :: List.replicate bound (0, 0)) ≠ (0, 0)) ↔
        (x, y) = root
    rw [evalPolynomial_one_padded]
    simp [f, evalNumerator, evalPolynomial_one, mul, sub, Prod.mk.injEq, sub_eq_zero, root]
  have dist (k : ℕ) : criticalLineCheck root k ↔ distance < (1 / 2 : ℚ) ^ k := by
    simp only [criticalLineCheck, root, add_sub_cancel_left]
    rw [abs_of_nonneg (by dsimp [distance]; positivity)]
  refine ⟨Encodable.encode f, Encodable.encode root, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by simp [f]) (denominator_length_le_code f)
  · intro j k bounded
    simp only [passes, Encodable.encodek]
    cases Encodable.decode (α := Point) j with
    | none => trivial
    | some z =>
      intro hz
      rw [(zero_iff z).mp hz, dist]
      exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · simp only [passes, Encodable.encodek, (zero_iff root).mpr rfl, true_implies, dist]
    exact lt_irrefl distance

/-- No fixed ceiling gives the full direct zero-location check on all
    rational continuation codes. -/
theorem no_fixed_precision_ceiling (K : ℕ) :
    ¬ ∀ m : ℕ, (∀ j k : ℕ, k ≤ K → passes m j k) ↔ (∀ j k : ℕ, passes m j k) := by
  obtain ⟨m, n, _, pass, fail⟩ := exists_code_passing_precision_prefix_and_failing K 0
  exact fun equivalent => fail ((equivalent m).mp pass n (K + 2))

/-- A finite list of the standard precision checks can hold in ordinary
    arithmetic together with the assertion that some check fails. -/
theorem finite_standard_checks_with_failure (bounds : Finset ℕ)
    (checks : Finset (ℕ × ℕ)) :
    ∃ m : ℕ, (∀ b ∈ bounds, b < m) ∧ (∀ p ∈ checks, passes m p.1 p.2) ∧
      ∃ n k : ℕ, ¬ passes m n k := by
  obtain ⟨m, n, large, pass, fail⟩ :=
    exists_code_passing_precision_prefix_and_failing (checks.sup Prod.snd) (bounds.sup id)
  exact ⟨m, fun b hb => (Finset.le_sup (f := id) hb).trans_lt large,
    fun p hp => pass p.1 p.2 (Finset.le_sup (f := Prod.snd) hp), _, _, fail⟩

end RH.Paper.PlantedZero
