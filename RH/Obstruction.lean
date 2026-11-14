import RH.Soundness
import RH.ObstructionProof
/-! # Obstruction Theorems (Section 1.8–1.12). ALL PROVED.

The linear and curved obstructions are INDEPENDENT constructions
using DIFFERENT models:

- **Linear** (Lemma 1.10.2): ZModel (M_L), nonstandard arithmetic
  model built by compactness. M_L ⊨ RH but M_L ⊭ R_L(RH).
  Proved in ObstructionProof.lean from published axioms.

- **Curved** (Lemma 1.12.4): CModel (M_C), ultrapower of the
  standard analytic structure. M_C ⊨ ¬RH but M_C ⊭ R_C(¬RH).
  Proved here from published axioms.

Neither depends on the other. See paper Remark 1.13.1.
-/

/-- **Lemma 1.10.2** (PROVED): Linear obstruction of RH in ZModel.
    Proved from published axioms in ObstructionProof.lean. -/
theorem linear_obstruction_RH : LNonzero RH_sent :=
  linear_obstruction_of_RH

/-- **Lemma 1.12.4** (PROVED): Curved obstruction of ¬RH in CModel.
    Independent construction from published axioms.
    From: admissible_translation_exists + curved_obstruction_in_CModel -/
theorem neg_obstruction_RH : CNonzero (negL RH_sent) := by
  obtain ⟨τ, hτ⟩ := admissible_translation_exists
  exact ⟨τ, hτ, curved_obstruction_in_CModel τ hτ⟩

/-- **Theorem 1.7.5** (PROVED): Admissible translations exist. -/
theorem exists_admissible : ∃ (τ : TranslationPair), Admissible τ :=
  admissible_translation_exists
