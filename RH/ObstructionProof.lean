import RH.Defs
/-!
# Proof of Linear Obstruction (Section 1.10, Lemma 1.10.2). PROVED.

The linear obstruction uses the concrete Lagarias translation.
obstruction_in_ZModel gives: ZModel ⊨ RH_sent ∧ ZModel ⊭ τ_L.RL(RH_sent).
The disagreement is semantic, without specifying which direction is "correct."
The direction is determined later (TruthInN.lean) via Kreisel's observation.
-/

/-- **Lemma 1.10.2** (PROVED):
    Linear obstruction of RH.
    The Lagarias translation's round-trip distorts RH_sent in ZModel.

    Proof:
    (1) obstruction_in_ZModel: zsat RH_sent ∧ ¬ zsat (τ_L.RL RH_sent)
    (2) This gives LObstructs lagarias_translation RH_sent. -/
theorem linear_obstruction_of_RH :
    LObstructs lagarias_translation RH_sent := by
  intro heq
  exact obstruction_in_ZModel.2 (heq ▸ obstruction_in_ZModel.1)
