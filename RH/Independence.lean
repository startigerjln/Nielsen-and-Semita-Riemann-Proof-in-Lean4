import RH.Obstruction
/-! # ZFC Independence (Section 1.6, Section 1.13). ALL PROVED.

Two independent obstruction arguments in two different models:

  Linear (ZModel):
    Soundness: ZFC ⊢ φ → ∀ τ admissible, LVanishes τ φ
    Obstruction: ∃ τ₀ admissible, LObstructs τ₀ RH_sent
    Together: ZFC ⊢ RH → contradiction → ZFC ⊬ RH

  Curved (CModel):
    Soundness: ZFC ⊢ φ → ∀ τ admissible, CVanishes τ φ
    Obstruction: ∃ τ₀ admissible, CObstructs τ₀ (¬RH_sent)
    Together: ZFC ⊢ ¬RH → contradiction → ZFC ⊬ ¬RH
-/

/-- **Theorem 1.13.1** (PROVED): RH is Λ-irreducible. -/
theorem RH_lambda_irreducible : LIrreducible RH_sent :=
  ⟨linear_obstruction_RH, neg_obstruction_RH⟩

/-- **Theorem 1.6.1 first half** (PROVED): ZFC ⊬ RH.
    Uses linear obstruction in ZModel + linear soundness. -/
theorem unprovable_RH : ¬ ZFCProv RH_sent := by
  intro hprov
  obtain ⟨τ, hτ, hobs⟩ := linear_obstruction_RH
  exact lambda_reduction_soundness τ hτ RH_sent hprov hobs

/-- **Theorem 1.6.1 second half** (PROVED): ZFC ⊬ ¬RH.
    Uses curved obstruction in CModel + curved soundness. -/
theorem neg_unprovable_RH : ¬ ZFCProv (negL RH_sent) := by
  intro hprov
  obtain ⟨τ, hτ, hobs⟩ := neg_obstruction_RH
  exact curved_reduction_soundness τ hτ (negL RH_sent) hprov hobs

/-- **Corollary 1.13.2** (PROVED): Full independence. -/
theorem RH_independent_of_ZFC :
    ¬ ZFCProv RH_sent ∧ ¬ ZFCProv (negL RH_sent) :=
  ⟨unprovable_RH, neg_unprovable_RH⟩
