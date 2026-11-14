import RH.Defs
/-! # Theorem 1.5.2: Λ-Reduction Soundness. PROVED.

If ZFC ⊢ φ, then every admissible translation preserves φ in ZModel.
So the round-trip matches φ → no distortion → Λ vanishes. -/

/-- **Theorem 1.5.2** (PROVED): ZFC ⊢ φ ⟹ Λ_L(φ) vanishes in ZModel. -/
theorem lambda_reduction_soundness
    (τ : TranslationPair) (hτ : Admissible τ)
    (φ : L.Sentence) (hφ : ZFCProv φ) :
    LVanishes τ φ := by
  intro hobs
  have h1 := zfc_sound φ hφ
  have h2 := hτ.pres φ hφ h1
  exact hobs (propext ⟨fun _ => h2, fun _ => h1⟩)
