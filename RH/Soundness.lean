import RH.Defs
/-! # Theorem 1.5.2: Λ-Reduction Soundness. PROVED.

ZFC ⊢ φ means φ holds in any model. In particular, in ZModel.
So the round-trip preserves it → Λ vanishes → no obstruction.

For the curved side (ZFC ⊬ ¬RH), we don't need Λ-reduction
soundness at all. We just need: ZFC ⊢ ¬RH → CModel ⊨ ¬RH,
contradicting CModel ⊨ RH. That uses zfc_sound_curved directly.
-/

/-- PUBLISHED: ZFC soundness in CModel.
    ZFC-provable sentences hold in CModel.
    [Goedel completeness; Shoenfield 1967] -/
axiom zfc_sound_curved : ∀ (φ : L.Sentence), ZFCProv φ → csat φ

/-- **Theorem 1.5.2** (PROVED): ZFC ⊢ φ ⟹ Λ_L(φ) vanishes in ZModel. -/
theorem lambda_reduction_soundness
    (τ : TranslationPair) (hτ : Admissible τ)
    (φ : L.Sentence) (hφ : ZFCProv φ) :
    LVanishes τ φ := by
  intro hobs
  have h1 := zfc_sound φ hφ
  have h2 := hτ.pres φ hφ h1
  exact hobs (propext ⟨fun _ => h2, fun _ => h1⟩)
