import RH.Paper.ProofI
open FirstOrder RH.Paper
#print axioms RH.Paper.standard_counterexample_of_not_true
#print axioms RH.Paper.finite_witness_reflection
#print axioms RH.Paper.RH_true_in_N
#print axioms RH.Paper.RH_true_in_N_of_independence
#check RH.Paper.RH_true_in_N_of_independence

-- Check the bindings and operation order of all eight encoded Q axioms.
example : ℕ ⊨ Robinson.successorInjective := by
  change ∀ x y : ℕ, x + 1 = y + 1 → x = y
  exact fun _ _ => Nat.add_right_cancel
example : ℕ ⊨ Robinson.successorNonzero := by
  change ∀ x : ℕ, ¬ x + 1 = 0
  exact fun x => Nat.succ_ne_zero x
example : ℕ ⊨ Robinson.predecessor := by
  change ∀ x : ℕ, x ≠ 0 → ¬ ∀ y : ℕ, ¬ y + 1 = x
  intro x hx h
  cases x with
  | zero => exact hx rfl
  | succ n => exact h n rfl
example : ℕ ⊨ Robinson.addZero := by
  change ∀ x : ℕ, x + 0 = x
  exact Nat.add_zero
example : ℕ ⊨ Robinson.addSuccessor := by
  change ∀ x y : ℕ, x + (y + 1) = (x + y) + 1
  exact fun x y => (Nat.add_assoc x y 1).symm
example : ℕ ⊨ Robinson.mulZero := by
  change ∀ x : ℕ, x * 0 = 0
  exact Nat.mul_zero
example : ℕ ⊨ Robinson.mulSuccessor := by
  change ∀ x y : ℕ, x * (y + 1) = x * y + x
  exact Nat.mul_succ
example : ℕ ⊨ Robinson.orderDefinition := by
  unfold Robinson.orderDefinition
  simp only [Language.Sentence.Realize, Language.Formula.Realize,
    Language.BoundedFormula.realize_all, Language.BoundedFormula.realize_iff,
    Language.BoundedFormula.realize_ex]
  change ∀ x y : ℕ, x ≤ y ↔ ∃ z : ℕ, z + x = y
  intro x y
  constructor
  · intro h
    exact ⟨y - x, Nat.sub_add_cancel h⟩
  · rintro ⟨z, rfl⟩
    exact Nat.le_add_left x z
