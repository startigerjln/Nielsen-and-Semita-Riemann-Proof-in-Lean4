import RH.Obstruction
/-! # ZFC Independence (Section 1.6, Section 1.13). ALL PROVED.

ZFC ⊬ RH: from linear obstruction (admissible translation in ZModel).
ZFC ⊬ ¬RH: from curved obstruction (CAdmissible translation in CModel).
Independent arguments, independent models.

For ZFC ⊬ ¬RH: assume ZFC ⊢ ¬RH. Then csat(¬RH) by soundness.
So ¬csat(RH). The curved obstruction gives τ with CObstructs τ RH
or CObstructs τ ¬RH.
- CObstructs τ RH: csat(RH) ≠ csat(τ.RL(RH)). Both are false
  (csat(RH) false by assumption, τ.RL(RH) false by ultrapower).
  They agree → this case is impossible.
- CObstructs τ ¬RH: csat(¬RH) ≠ csat(τ.RL(¬RH)). csat(¬RH) is
  true. τ.RL(¬RH) is false (ultrapower). They disagree. ✓
  Now: ZFC ⊢ ¬RH + CAdmissible.pres → csat(τ.RL(¬RH)).
  But ultrapower says ¬csat(τ.RL(¬RH)). Contradiction.
-/

/-- **Theorem 1.6.1 first half** (PROVED): ZFC ⊬ RH. -/
theorem unprovable_RH : ¬ ZFCProv RH_sent := by
  intro hprov
  obtain ⟨τ, hτ, hobs⟩ := linear_obstruction_RH
  exact lambda_reduction_soundness τ hτ RH_sent hprov hobs

/-- **Theorem 1.6.1 second half** (PROVED): ZFC ⊬ ¬RH.
    Uses curved obstruction + CAdmissible preservation. -/
theorem neg_unprovable_RH : ¬ ZFCProv (negL RH_sent) := by
  intro hprov
  obtain ⟨τ, hτ, hcases⟩ := curved_obstruction_RH
  -- ZFC ⊢ ¬RH → csat(¬RH) by soundness
  have h_neg_holds : csat (negL RH_sent) := zfc_sound_curved _ hprov
  -- Round-trip of ¬RH fails in CModel (from sigma1_holds_roundtrip_fails)
  have h_neg_rt_fails : ¬ csat (τ.RL (negL RH_sent)) :=
    (ultrapower_falsifies_finitary_roundtrip τ hτ.fin RH_sent RH_is_pi1).2
      h_neg_holds
  -- CAdmissible.pres: ZFC ⊢ ¬RH → csat(¬RH) → csat(τ.RL(¬RH))
  have h_pres := hτ.pres (negL RH_sent) hprov h_neg_holds
  -- But ultrapower says ¬csat(τ.RL(¬RH)). Contradiction.
  exact h_neg_rt_fails h_pres

/-- **Corollary 1.13.2** (PROVED): Full independence. -/
theorem RH_independent_of_ZFC :
    ¬ ZFCProv RH_sent ∧ ¬ ZFCProv (negL RH_sent) :=
  ⟨unprovable_RH, neg_unprovable_RH⟩
