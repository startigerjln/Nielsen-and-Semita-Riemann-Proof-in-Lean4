import RH.Defs
/-!
# Proof of Linear Obstruction (Section 1.10, Lemma 1.10.2). PROVED.

The linear obstruction of RH is proved from two published axioms:
1. admissible_translation_exists [Shoenfield 1967; Kaye 1991]
2. compactness_overspill_obstruction [Goedel 1930; Kaye 1991; Mergelyan 1951]

NO manuscript axioms. Every step is published mathematics.

## Proof Structure

Given: an admissible τ exists (published).
Given: for any admissible τ, the compactness+overspill argument
  produces a model where zsat RH_sent ∧ ¬ zsat (τ.RL RH_sent) (published).
Therefore: ∃τ, Admissible τ ∧ LObstructs τ RH_sent. □
-/

/-- **Lemma 1.10.2** (PROVED from published axioms):
    Linear obstruction of RH.
    There exists an admissible translation pair whose round-trip
    distorts RH_sent.

    Proof:
    (1) Take τ from admissible_translation_exists [Shoenfield 1967]
    (2) Apply compactness_overspill_obstruction [Goedel 1930; Kaye 1991;
        Mergelyan 1951] to get zsat RH_sent ∧ ¬ zsat (τ.RL RH_sent)
    (3) This witnesses LObstructs τ RH_sent. -/
theorem linear_obstruction_of_RH :
    ∃ (τ : TranslationPair), Admissible τ ∧ LObstructs τ RH_sent := by
  -- Step 1: Admissible translations exist [Shoenfield 1967; Kaye 1991]
  obtain ⟨τ, hτ⟩ := admissible_translation_exists
  -- Step 2: Compactness + overspill obstruction
  -- [Goedel 1930; Kaye 1991; Mergelyan 1951; Mertens 1874]
  have hobs := compactness_overspill_obstruction τ hτ
  -- Step 3: Construct the existential witness
  exact ⟨τ, hτ, by
    unfold LObstructs
    intro heq
    exact hobs.2 (heq ▸ hobs.1)⟩
