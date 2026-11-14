import RH.Soundness
import RH.ObstructionProof
/-! # Obstruction Theorems (Section 1.8–1.12). ALL PROVED.

The linear and curved obstructions are INDEPENDENT constructions:

- **Linear** (Lemma 1.10.2): nonstandard arithmetic model M_L,
  built by compactness. Overspill causes round-trip uniformity
  failure. Proved in ObstructionProof.lean from published axioms.

- **Curved** (Lemma 1.12.4): ultrapower M_C of the standard
  analytic structure. Łoś preserves first-order properties but
  arithmetic mediation strips global analytic coherence at
  nonstandard precision. Proved here from published axioms.

Neither depends on the other. See paper Remark 1.13.1.
-/

/-- **Lemma 1.10.2** (PROVED): Linear obstruction of RH.
    Proved from published axioms in ObstructionProof.lean. -/
theorem linear_obstruction_RH : LNonzero RH_sent :=
  linear_obstruction_of_RH

/-- **Lemma 1.12.4** (PROVED): Curved obstruction of ¬RH.
    Independent construction from published axioms.
    From: admissible_translation_exists + curved_obstruction_in_ZModel -/
theorem neg_obstruction_RH : LNonzero (negL RH_sent) := by
  obtain ⟨τ, hτ⟩ := admissible_translation_exists
  exact ⟨τ, hτ, curved_obstruction_in_ZModel τ hτ⟩

/-- **Theorem 1.7.5** (PROVED): Admissible translations exist. -/
theorem exists_admissible : ∃ (τ : TranslationPair), Admissible τ :=
  admissible_translation_exists
