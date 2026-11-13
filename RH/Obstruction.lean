import RH.Soundness
import RH.ObstructionProof
/-! # Obstruction Theorems (Section 1.8–1.12). ALL PROVED.

Key result: the curved obstruction is DERIVED from the linear one
via compositionality. By comp_neg + comp_neg_bwd:

  R_L(¬φ) = negL(R_L(φ))

So LObstructs τ (negL φ) ↔ LObstructs τ φ. The curved obstruction
for ¬RH follows from the linear obstruction for RH.

The linear obstruction itself is PROVED in ObstructionProof.lean
from published axioms (compactness + overspill + Mergelyan).
-/

/-- **Lemma 1.10.2** (PROVED): Linear obstruction of RH.
    Now proved from published axioms in ObstructionProof.lean. -/
theorem linear_obstruction_RH : LNonzero RH_sent :=
  linear_obstruction_of_RH

/-- Compositionality makes R_L commute with negation. -/
theorem RL_neg_comm (τ : TranslationPair) (hcomp : Compositional τ)
    (φ : L.Sentence) : τ.RL (negL φ) = negL (τ.RL φ) := by
  unfold TranslationPair.RL
  rw [comp_neg τ hcomp φ, comp_neg_bwd τ hcomp (τ.fwd φ)]

/-- Obstruction for φ implies obstruction for negL φ. -/
theorem obstruction_neg (τ : TranslationPair)
    (hcomp : Compositional τ) (φ : L.Sentence)
    (hobs : LObstructs τ φ) : LObstructs τ (negL φ) := by
  unfold LObstructs at *
  rw [RL_neg_comm τ hcomp φ]
  intro heq
  apply hobs
  have h1 := negL_zsat φ
  have h2 := negL_zsat (τ.RL φ)
  -- heq : zsat (negL φ) = zsat (negL (τ.RL φ))
  -- From heq: ¬zsat φ ↔ ¬zsat (τ.RL φ)
  -- Therefore: zsat φ ↔ zsat (τ.RL φ)
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

/-- **Lemma 1.12.4** (PROVED from linear + compositionality):
    Curved obstruction of ¬RH. NOT an axiom -- derived. -/
theorem neg_obstruction_RH : LNonzero (negL RH_sent) := by
  obtain ⟨τ, hτ, hobs⟩ := linear_obstruction_of_RH
  exact ⟨τ, hτ, obstruction_neg τ hτ.comp RH_sent hobs⟩

/-- **Theorem 1.7.5** (PROVED): Admissible translations exist. -/
theorem exists_admissible : ∃ (τ : TranslationPair), Admissible τ :=
  admissible_translation_exists
