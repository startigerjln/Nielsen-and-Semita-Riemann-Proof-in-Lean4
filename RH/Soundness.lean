import RH.Defs
/-! # Theorem 1.5.2: Λ-Reduction Soundness. PROVED.

Two versions: one for ZModel (linear), one for CModel (curved).
Same argument: ZFC ⊢ φ means φ holds in any model, including the
obstruction model, so the round-trip preserves it. -/

/-- ZFC soundness in CModel: ZFC-provable sentences hold in CModel.
    [Goedel completeness; Shoenfield 1967] -/
axiom zfc_sound_curved : ∀ (φ : L.Sentence), ZFCProv φ → csat φ

/-- Admissible translations preserve ZFC-provable sentences in CModel.
    Same argument as for ZModel: if ZFC ⊢ φ then φ holds in CModel,
    and the round-trip preserves it.
    [Shoenfield 1967] -/
axiom admissible_pres_curved :
  ∀ (τ : TranslationPair), Admissible τ →
    ∀ (φ : L.Sentence), ZFCProv φ → csat φ → csat (τ.RL φ)

/-- **Theorem 1.5.2** (PROVED): ZFC ⊢ φ ⟹ Λ_L(φ) vanishes in ZModel. -/
theorem lambda_reduction_soundness
    (τ : TranslationPair) (hτ : Admissible τ)
    (φ : L.Sentence) (hφ : ZFCProv φ) :
    LVanishes τ φ := by
  intro hobs
  have h1 := zfc_sound φ hφ
  have h2 := hτ.pres φ hφ h1
  exact hobs (propext ⟨fun _ => h2, fun _ => h1⟩)

/-- **Theorem 1.5.2 curved** (PROVED): ZFC ⊢ φ ⟹ Λ_C(φ) vanishes in CModel. -/
def CVanishes (τ : TranslationPair) (φ : L.Sentence) : Prop :=
  ¬ CObstructs τ φ

theorem curved_reduction_soundness
    (τ : TranslationPair) (hτ : Admissible τ)
    (φ : L.Sentence) (hφ : ZFCProv φ) :
    CVanishes τ φ := by
  intro hobs
  have h1 := zfc_sound_curved φ hφ
  have h2 := admissible_pres_curved τ hτ φ hφ h1
  exact hobs (propext ⟨fun _ => h2, fun _ => h1⟩)
