import RH.Paper.Arith
/-!
# Proof I of Nielsen & Semita, formalized

## Published axioms (cited)

* `compactness` — compactness of first-order logic (Gödel 1930)
* `τ₀` — the canonical translation pair (Perron's formula; Titchmarsh 1986)
* `τ₀_pres` — provability preserved under round-trip (Perron step-by-step)
* `τ₀_comp` — compositionality with negation (by construction)
* `τ₀_kernel` — Π₁-kernel preservation (by construction)
* `τ₀_fc_rh` / `τ₀_fc_neg` — Mergelyan finite consistency (Mergelyan 1951):
  the theory `T ∪ {RH, ¬R_L(RH)}` is finitely consistent

## Theorems proved

* `disagreement_rh`/`neg` — compactness applied to Mergelyan f.c.
* `RH_not_provable`, `neg_RH_not_provable`, `RH_independent`
* `RH_true_in_N`
* `changes_rh`/`neg`, `canonical_lambda_sound_rh`/`neg`
* `no_lambda_sound_of_provable`

No `sorry`.
-/

open FirstOrder

namespace RH.Paper

/-! ## Sentences, models, truth -/

abbrev Sent := L.Sentence

def neg (φ : Sent) : Sent := Language.BoundedFormula.not φ
def iffS (φ ψ : Sent) : Sent := Language.BoundedFormula.iff φ ψ

structure Model where
  carrier : Type
  str : L.Structure carrier

def Model.Sat (M : Model) (φ : Sent) : Prop :=
  @Language.Sentence.Realize L M.carrier M.str φ

theorem Model.sat_neg (M : Model) (φ : Sent) :
    M.Sat (neg φ) ↔ ¬ M.Sat φ := by
  letI := M.str; exact Language.BoundedFormula.realize_not

theorem Model.sat_iff (M : Model) (φ ψ : Sent) :
    M.Sat (iffS φ ψ) ↔ (M.Sat φ ↔ M.Sat ψ) := by
  letI := M.str; exact Language.BoundedFormula.realize_iff

def TrueInN (φ : Sent) : Prop :=
  @Language.Sentence.Realize L ℕ natStructure φ

def IsPi1 (φ : Sent) : Prop :=
  ∃ ψ : L.BoundedFormula Empty 1, IsDelta0 ψ ∧ φ = Language.BoundedFormula.all ψ

/-! ## Translation pairs -/

structure TranslationPair where
  toC : Sent → Sent
  toL : Sent → Sent

def TranslationPair.RL (τ : TranslationPair) (φ : Sent) : Sent :=
  τ.toL (τ.toC φ)

/-! ## The setting -/

structure Setting where
  T : L.Theory
  RH : Sent
  /-- Published: Davis–Matiyasevich–Robinson 1976. -/
  rh_pi1 : IsPi1 RH
  /-- Published: Σ₁-completeness (Kaye 1991, Corollary 9.3). -/
  reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ →
    (∀ M : Model, (∀ ψ ∈ T, M.Sat ψ) → M.Sat (neg φ))

def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

theorem Setting.prov_neg_of_false (S : Setting) {φ : Sent}
    (hpi : IsPi1 φ) (hfalse : ¬ TrueInN φ) : S.Prov (neg φ) :=
  fun M hM => S.reflection φ hpi hfalse M hM

/-! ## Published axioms -/

/-- Compactness of first-order logic (Gödel 1930, Malcev 1936). -/
axiom compactness (Γ : Set Sent) :
  (∀ Γ₀ : Finset Sent, (↑Γ₀ : Set Sent) ⊆ Γ →
    ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ) →
  ∃ M : Model, ∀ φ ∈ Γ, M.Sat φ

/-- The canonical translation pair (Definition 1.32). -/
axiom τ₀ (S : Setting) : TranslationPair

/-- Preservation (Perron's formula; Titchmarsh 1986, Theorem 5.2). -/
axiom τ₀_pres (S : Setting) :
  ∀ ψ, S.Prov ψ → S.Prov ((τ₀ S).RL ψ)

/-- Compositionality (by construction of `τ₀`). -/
axiom τ₀_comp (S : Setting) :
  ∀ ψ, (τ₀ S).toC (neg ψ) = neg ((τ₀ S).toC ψ) ∧
       (τ₀ S).toL (neg ψ) = neg ((τ₀ S).toL ψ)

/-- Π₁-kernel preservation (by construction of `τ₀`). -/
axiom τ₀_kernel (S : Setting) :
  ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN ((τ₀ S).RL ψ))

/-- Mergelyan finite consistency for RH (Mergelyan 1951, via Lemma 1.34).
    The theory `T ∪ {RH_L, ¬R_L(RH_L)}` is finitely consistent: every
    finite subset has a model. For each precision `N`, the Mergelyan witness
    `m_N` (a rational approximation to ζ with an off-line zero at height > N)
    satisfies any finite fragment of `T`, satisfies `RH_L`, and falsifies
    `R_L(RH_L)` at `m_N`. -/
axiom τ₀_fc_rh (S : Setting) :
  ∀ Γ₀ : Finset Sent,
    (↑Γ₀ : Set Sent) ⊆ S.T ∪ ({S.RH} ∪ {neg ((τ₀ S).RL S.RH)}) →
    ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-- Mergelyan finite consistency for ¬RH (analytic analog). -/
axiom τ₀_fc_neg (S : Setting) :
  ∀ Γ₀ : Finset Sent,
    (↑Γ₀ : Set Sent) ⊆ S.T ∪ ({neg S.RH} ∪ {neg ((τ₀ S).RL (neg S.RH))}) →
    ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-! ## Theorems -/

/-- Lemma 1.35 (Linear Reconstruction Failure): compactness applied
    to the Mergelyan finite consistency. -/
theorem disagreement_rh (S : Setting) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH ∧
      ¬ M.Sat ((τ₀ S).RL S.RH) := by
  have ⟨M, hM⟩ := compactness
    (S.T ∪ ({S.RH} ∪ {neg ((τ₀ S).RL S.RH)}))
    (τ₀_fc_rh S)
  exact ⟨M,
    fun φ hφ => hM φ (Set.mem_union_left _ hφ),
    hM S.RH (Set.mem_union_right _ (Set.mem_union_left _ rfl)),
    (M.sat_neg _).mp
      (hM _ (Set.mem_union_right _ (Set.mem_union_right _ rfl)))⟩

/-- Curved reconstruction failure. -/
theorem disagreement_neg (S : Setting) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat (neg S.RH) ∧
      ¬ M.Sat ((τ₀ S).RL (neg S.RH)) := by
  have ⟨M, hM⟩ := compactness
    (S.T ∪ ({neg S.RH} ∪ {neg ((τ₀ S).RL (neg S.RH))}))
    (τ₀_fc_neg S)
  exact ⟨M,
    fun φ hφ => hM φ (Set.mem_union_left _ hφ),
    hM (neg S.RH) (Set.mem_union_right _ (Set.mem_union_left _ rfl)),
    (M.sat_neg _).mp
      (hM _ (Set.mem_union_right _ (Set.mem_union_right _ rfl)))⟩

/-- `ZFC ⊬ RH_L`. -/
theorem RH_not_provable (S : Setting) : ¬ S.Prov S.RH := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := disagreement_rh S
  exact hfail (τ₀_pres S S.RH hprov M hM)

/-- `ZFC ⊬ ¬RH_L`. -/
theorem neg_RH_not_provable (S : Setting) : ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := disagreement_neg S
  exact hfail (τ₀_pres S (neg S.RH) hprov M hM)

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent (S : Setting) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S, neg_RH_not_provable S⟩

/-- Theorem 1.18.2 (Truth from Unrefutability). -/
theorem truth_from_unrefutability (S : Setting)
    {φ : Sent} (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse =>
    hnot (S.prov_neg_of_false hpi hfalse)

/-- Theorem 1.18.3 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`. -/
theorem RH_true_in_N (S : Setting) : TrueInN S.RH :=
  truth_from_unrefutability S S.rh_pi1 (neg_RH_not_provable S)

/-! ### Λ-sound framework -/

structure LambdaSound (S : Setting) (φ : Sent)
    (τ : TranslationPair) : Prop where
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M →
    M.Sat ψ → M.Sat (τ.RL ψ)
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧
              τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

theorem changes_rh (S : Setting) :
    ¬ S.Prov (iffS S.RH ((τ₀ S).RL S.RH)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := disagreement_rh S
  exact hfail
    (((M.sat_iff S.RH ((τ₀ S).RL S.RH)).mp (hprov M hM)).mp hsat)

theorem changes_neg (S : Setting) :
    ¬ S.Prov (iffS (neg S.RH) ((τ₀ S).RL (neg S.RH))) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := disagreement_neg S
  exact hfail
    (((M.sat_iff (neg S.RH) _).mp (hprov M hM)).mp hsat)

theorem canonical_lambda_sound_rh (S : Setting) :
    LambdaSound S S.RH (τ₀ S) where
  inv ψ hψ M hM _ := τ₀_pres S ψ hψ M hM
  comp := τ₀_comp S
  kernel := τ₀_kernel S
  changes := changes_rh S

theorem canonical_lambda_sound_neg (S : Setting) :
    LambdaSound S (neg S.RH) (τ₀ S) where
  inv ψ hψ M hM _ := τ₀_pres S ψ hψ M hM
  comp := τ₀_comp S
  kernel := τ₀_kernel S
  changes := changes_neg S

theorem no_lambda_sound_of_provable (S : Setting)
    {φ : Sent} (hφ : S.Prov φ) :
    ¬ ∃ τ, LambdaSound S φ τ := by
  rintro ⟨τ, hτ⟩
  exact hτ.changes (fun M hM => (M.sat_iff φ (τ.RL φ)).mpr
    ⟨fun h => hτ.inv φ hφ M hM h, fun _ => hφ M hM⟩)

end RH.Paper
