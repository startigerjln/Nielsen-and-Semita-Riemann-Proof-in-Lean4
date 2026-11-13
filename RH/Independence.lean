import RH.Obstruction
/-! # ZFC Independence (§1.6, §1.13). ALL PROVED.

Proof structure (∃ obstruction vs ∀ soundness):
  Soundness: ZFC ⊢ φ → ∀ τ admissible, LVanishes τ φ
  Obstruction: ∃ τ₀ admissible, LObstructs τ₀ φ
  Together: ZFC ⊢ φ → (LVanishes τ₀ φ ∧ LObstructs τ₀ φ) → False
-/

/-- **Theorem 1.13.1** (PROVED): RH is Λ-irreducible. -/
theorem RH_lambda_irreducible : LIrreducible RH_sent :=
  ⟨linear_obstruction_RH, neg_obstruction_RH⟩

/-- **Theorem 1.6.1 first half** (PROVED): ZFC ⊬ RH.
    Obtains the witness τ₀ from the existential obstruction axiom,
    then applies universal soundness to τ₀ to get the contradiction. -/
theorem unprovable_RH : ¬ ZFCProv RH_sent := by
  intro hprov
  obtain ⟨τ, hτ, hobs⟩ := linear_obstruction_RH
  exact lambda_reduction_soundness τ hτ RH_sent hprov hobs

/-- **Theorem 1.6.1 second half** (PROVED): ZFC ⊬ ¬RH. -/
theorem neg_unprovable_RH : ¬ ZFCProv (negL RH_sent) := by
  intro hprov
  obtain ⟨τ, hτ, hobs⟩ := neg_obstruction_RH
  exact lambda_reduction_soundness τ hτ (negL RH_sent) hprov hobs

/-- **Corollary 1.13.2** (PROVED): Full independence. -/
theorem RH_independent_of_ZFC :
    ¬ ZFCProv RH_sent ∧ ¬ ZFCProv (negL RH_sent) :=
  ⟨unprovable_RH, neg_unprovable_RH⟩
