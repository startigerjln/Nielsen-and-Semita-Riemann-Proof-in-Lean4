import RH.Soundness
import RH.ObstructionProof
/-! # Obstruction Theorems (Section 1.8–1.12). ALL PROVED.

Linear and curved obstructions are INDEPENDENT:
- Linear (Lemma 1.10.2): ZModel, admissible (compositional) translation.
- Curved (Lemma 1.12.4): CModel, CAdmissible (finitary, not compositional).

Neither depends on the other.
-/

/-- **Lemma 1.10.2** (PROVED): Linear obstruction of RH in ZModel. -/
theorem linear_obstruction_RH : LNonzero RH_sent :=
  linear_obstruction_of_RH

/-- **Lemma 1.12.4** (PROVED): Curved obstruction in CModel.
    By excluded middle: obstruction on RH or ¬RH. -/
theorem curved_obstruction_RH :
    ∃ (τ : TranslationPair), CAdmissible τ ∧
      (CObstructs τ RH_sent ∨ CObstructs τ (negL RH_sent)) := by
  obtain ⟨τ, hτ⟩ := cadmissible_translation_exists
  exact ⟨τ, hτ, curved_obstruction_exists τ hτ⟩

/-- **Theorem 1.13.1** (PROVED): RH is Λ-irreducible. -/
theorem RH_lambda_irreducible : LIrreducible RH_sent :=
  ⟨linear_obstruction_RH, curved_obstruction_RH⟩

/-- Alias for backward compatibility with Main.lean / Audit.lean. -/
theorem neg_obstruction_RH :
    ∃ (τ : TranslationPair), CAdmissible τ ∧
      (CObstructs τ RH_sent ∨ CObstructs τ (negL RH_sent)) :=
  curved_obstruction_RH

/-- **Theorem 1.7.5** (PROVED): Admissible translations exist. -/
theorem exists_admissible : ∃ (τ : TranslationPair), Admissible τ :=
  admissible_translation_exists
