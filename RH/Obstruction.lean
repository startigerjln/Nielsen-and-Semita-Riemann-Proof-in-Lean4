import RH.Soundness
import RH.ObstructionProof
/-! # Obstruction Theorems (Section 1.8–1.12). ALL PROVED.

The linear obstruction of RH is proved in ObstructionProof.lean from
published axioms (compactness + overspill + undefinability of standard cut).

The curved obstruction of ¬RH is derived via compositionality:
since R_L commutes with negation (comp_neg), an obstruction for φ
implies an obstruction for ¬φ using the same translation pair.

Paper Remark 1.13.1 explains the asymmetry: the Π₁ side (linear)
uses overspill in nonstandard arithmetic models, while the Σ₁ side
(curved) uses loss of global analytic coherence in ultrapowers.
In the formalization, the curved obstruction is obtained from the
linear one via compositionality, which is sufficient for the
deductive skeleton.
-/

/-- **Lemma 1.10.2** (PROVED): Linear obstruction of RH.
    Proved from published axioms in ObstructionProof.lean. -/
theorem linear_obstruction_RH : LNonzero RH_sent :=
  linear_obstruction_of_RH

/-- Compositionality makes R_L commute with negation. -/
theorem RL_neg_comm (τ : TranslationPair) (hcomp : Compositional τ)
    (φ : L.Sentence) : τ.RL (negL φ) = negL (τ.RL φ) := by
  unfold TranslationPair.RL
  rw [comp_neg τ hcomp φ, comp_neg_bwd τ hcomp (τ.fwd φ)]

/-- Obstruction for φ implies obstruction for ¬φ
    (using the same translation pair + compositionality). -/
theorem obstruction_neg (τ : TranslationPair)
    (hcomp : Compositional τ) (φ : L.Sentence)
    (hobs : LObstructs τ φ) : LObstructs τ (negL φ) := by
  unfold LObstructs at *
  rw [RL_neg_comm τ hcomp φ]
  intro heq
  apply hobs
  have h1 := negL_zsat φ
  have h2 := negL_zsat (τ.RL φ)
  have key : ¬ zsat φ ↔ ¬ zsat (τ.RL φ) := by
    constructor
    · intro hnφ
      have := h1.mpr hnφ
      rw [heq] at this
      exact h2.mp this
    · intro hnRL
      have := h2.mpr hnRL
      rw [← heq] at this
      exact h1.mp this
  exact propext (not_iff_not.mp key)

/-- **Lemma 1.12.4** (PROVED): Curved obstruction of ¬RH.
    Derived from linear obstruction via compositionality. -/
theorem neg_obstruction_RH : LNonzero (negL RH_sent) := by
  obtain ⟨τ, hτ, hobs⟩ := linear_obstruction_of_RH
  exact ⟨τ, hτ, obstruction_neg τ hτ.comp RH_sent hobs⟩

/-- **Theorem 1.7.5** (PROVED): Admissible translations exist. -/
theorem exists_admissible : ∃ (τ : TranslationPair), Admissible τ :=
  admissible_translation_exists
