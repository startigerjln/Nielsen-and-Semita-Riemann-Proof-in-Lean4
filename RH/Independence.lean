import RH.Obstruction
/-! # ZFC Independence (Section 1.6, Section 1.13). ALL PROVED.

Two independent obstruction arguments in two different models:

  Linear (ZModel, M_L):
    ZFC ⊢ RH → RH holds in all models → R_L(RH) holds in ZModel
    → Λ_L = 0, contradicting the linear obstruction → ZFC ⊬ RH

  Curved (CModel, M_C):
    ZFC ⊢ ¬RH → ¬RH holds in all models → CModel ⊨ ¬RH
    → But CModel ⊨ RH (from Łoś) → contradiction → ZFC ⊬ ¬RH
-/

/-- **Theorem 1.13.1** (PROVED): RH is Λ-irreducible. -/
theorem RH_lambda_irreducible : LIrreducible RH_sent :=
  ⟨linear_obstruction_RH, curved_obstruction_RH⟩

/-- **Theorem 1.6.1 first half** (PROVED): ZFC ⊬ RH.
    Uses linear obstruction in ZModel + linear soundness.
    If ZFC ⊢ RH, then RH holds in ZModel, so R_L(RH) holds
    (by soundness), so Λ_L = 0, contradicting the obstruction. -/
theorem unprovable_RH : ¬ ZFCProv RH_sent := by
  intro hprov
  obtain ⟨τ, hτ, hobs⟩ := linear_obstruction_RH
  exact lambda_reduction_soundness τ hτ RH_sent hprov hobs

/-- **Theorem 1.6.1 second half** (PROVED): ZFC ⊬ ¬RH.
    Uses curved model CModel.
    If ZFC ⊢ ¬RH, then ¬RH holds in CModel (soundness).
    But CModel ⊨ RH (from CModel_satisfies_RH + Łoś).
    CModel ⊨ RH ∧ CModel ⊨ ¬RH is a contradiction. -/
theorem neg_unprovable_RH : ¬ ZFCProv (negL RH_sent) := by
  intro hprov
  have h_neg : csat (negL RH_sent) := zfc_sound_curved _ hprov
  have h_pos : csat RH_sent := CModel_satisfies_RH
  exact ((negL_csat RH_sent).mp h_neg) h_pos

/-- **Corollary 1.13.2** (PROVED): Full independence. -/
theorem RH_independent_of_ZFC :
    ¬ ZFCProv RH_sent ∧ ¬ ZFCProv (negL RH_sent) :=
  ⟨unprovable_RH, neg_unprovable_RH⟩
