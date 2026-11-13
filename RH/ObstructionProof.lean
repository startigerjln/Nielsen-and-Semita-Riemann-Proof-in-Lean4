import RH.Defs
/-!
# Proof of Linear Obstruction (Section 1.10, Lemma 1.10.2). PROVED.

The linear obstruction of RH is proved from:
1. admissible_translation_exists (proved theorem from published axioms)
2. obstruction_in_ZModel (semantic disagreement, no direction assumed)

NO circularity. The obstruction asserts that RH_sent and tau.RL(RH_sent)
DISAGREE in ZModel, without specifying which is true. The direction is
determined later (TruthInN.lean) via Kreisel's observation, AFTER
independence is established.
-/

/-- **Lemma 1.10.2** (PROVED):
    Linear obstruction of RH.
    There exists an admissible translation pair whose round-trip
    distorts RH_sent.

    Proof:
    (1) Take tau from admissible_translation_exists
    (2) obstruction_in_ZModel gives: zsat RH_sent != zsat (tau.RL RH_sent)
    (3) This is exactly LObstructs tau RH_sent. -/
theorem linear_obstruction_of_RH :
    ∃ (τ : TranslationPair), Admissible τ ∧ LObstructs τ RH_sent := by
  obtain ⟨τ, hτ⟩ := admissible_translation_exists
  exact ⟨τ, hτ, obstruction_in_ZModel τ hτ⟩
