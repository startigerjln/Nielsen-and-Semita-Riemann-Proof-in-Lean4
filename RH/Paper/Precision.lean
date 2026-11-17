import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact equality and unbounded precision

The proposed reconstruction checks an equality at every precision. Over an
Archimedean ordered field this is equivalent to the equality itself. This
is an algebraic lemma, not an assumption of RH and not a disagreement-model
construction. When used inside a model of ZFC, all natural-number quantifiers
are internal to that model, including its nonstandard natural numbers.
-/

namespace RH.Paper

variable {α : Type*} [LinearOrderedField α] [Archimedean α]

/-- An exact equality and its all-precision reconstruction have identical content. -/
theorem exact_iff_all_dyadic_precision (x c : α) :
    x = c ↔ ∀ k : ℕ, |x - c| < (1 / 2 : α) ^ k := by
  constructor
  · rintro rfl k
    simpa only [sub_self, abs_zero] using
      (pow_pos (by norm_num : (0 : α) < 1 / 2) k)
  · intro h
    by_contra hne
    have hpos : 0 < |x - c| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : α) < 1)
    exact (lt_asymm (h k) hk)

/-- The extra universally quantified precision parameter does not create a
new mathematical condition for an indexed family of exact equalities. -/
theorem family_exact_iff_all_dyadic_precision {ι : Type*} (x : ι → α) (c : α) :
    (∀ i, x i = c) ↔ ∀ i, ∀ k : ℕ, |x i - c| < (1 / 2 : α) ^ k := by
  constructor
  · intro h i
    exact (exact_iff_all_dyadic_precision (x i) c).mp (h i)
  · intro h i
    exact (exact_iff_all_dyadic_precision (x i) c).mpr (h i)

end RH.Paper

#print axioms RH.Paper.exact_iff_all_dyadic_precision
