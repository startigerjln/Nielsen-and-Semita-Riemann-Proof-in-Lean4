import RH.Defs
/-! # Theorem 1.5.2: Λ-Reduction Soundness. PROVED. -/

/-- **Theorem 1.5.2** (PROVED): ZFC ⊢ φ ⟹ Λ(φ) vanishes. -/
theorem lambda_reduction_soundness
    (τ : TranslationPair) (hτ : Admissible τ)
    (φ : L.Sentence) (hφ : ZFCProv φ) :
    LVanishes τ φ := by
  intro hobs
  have h1 := zfc_sound φ hφ
  have h2 := hτ.pres φ hφ h1
  exact hobs (propext ⟨fun _ => h2, fun _ => h1⟩)
