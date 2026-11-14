import RH.Paper.Arith
/-!
# Proof I of Nielsen & Semita, formalized as written

This file follows Section 1 of the paper in its version of May 16, 2026
(PhilArchive NIEPOT-5v52), in particular the central logical chain of
Remark 1.7.15:

1. RH is ZFC-birepresentable (Proposition 1.7.9).
2. The classical equivalence induces a canonical Λ-sound translation pair
   (Definition 1.7.11).
3. Round-trip adequacy: if `ZFC ⊢ RH_L` then `ZFC ⊢ RH_L ↔ R_L^can(RH_L)`
   (Theorem 1.7.13).
4. Obstruction models exist (Lemmas 1.10.2, 1.12.4, Corollary 1.10.6).
5. Hence `ZFC ⊬ RH_L`; then truth in ℕ by Π₁ witness reflection (§1.17, §1.18).

It contains no `axiom` and no `sorry`. The arithmetic form of RH is an
abstract Π₁ sentence; no number theory is used.

**Proved here:** Uniform Preservation (1.5.6), Λ-Reduction Soundness (1.5.2),
Round-Trip Adequacy (1.7.13), Independence from Obstruction Models (1.7.14),
Λ-irreducibility of RH (1.13.1), ZFC-undecidability (1.13.2), truth of RH in
ℕ (1.18.2, 1.18.3).

Provability is defined as truth in all models of ZFC, so soundness and
completeness are not assumptions.

**Assumed** (the structure `Hypotheses`): the Π₁ form of RH, Π₁ witness reflection, Λ-soundness of
the canonical pair, and the obstruction lemmas, each stated in the branch of
the case split in which the paper proves it: the linear and curved
obstructions for RH when RH holds in ℕ, and the curved obstruction for ¬RH
when RH fails in ℕ. Every theorem below is conditional on these.
-/

open FirstOrder

namespace RH.Paper

/-! ## Sentences, models, truth -/

abbrev Sent := L.Sentence

/-- Negation of a sentence. -/
def neg (φ : Sent) : Sent := Language.BoundedFormula.not φ

/-- Biconditional of two sentences. -/
def iffS (φ ψ : Sent) : Sent := Language.BoundedFormula.iff φ ψ

/-- An `L`-structure, bundled with its carrier. -/
structure Model where
  carrier : Type
  str : L.Structure carrier

/-- `M ⊨ φ`. -/
def Model.Sat (M : Model) (φ : Sent) : Prop :=
  @Language.Sentence.Realize L M.carrier M.str φ

theorem Model.sat_neg (M : Model) (φ : Sent) : M.Sat (neg φ) ↔ ¬ M.Sat φ := by
  letI := M.str
  exact Language.BoundedFormula.realize_not

theorem Model.sat_iff (M : Model) (φ ψ : Sent) :
    M.Sat (iffS φ ψ) ↔ (M.Sat φ ↔ M.Sat ψ) := by
  letI := M.str
  exact Language.BoundedFormula.realize_iff

/-- Truth in the standard model ℕ. -/
def TrueInN (φ : Sent) : Prop :=
  @Language.Sentence.Realize L ℕ natStructure φ

/-- Π₁ sentences: `∀ n, ψ(n)` with `ψ` a Δ₀ formula. -/
def IsPi1 (φ : Sent) : Prop :=
  ∃ ψ : L.BoundedFormula Empty 1, IsDelta0 ψ ∧ φ = Language.BoundedFormula.all ψ

/-! ## Translation pairs and round trips (Definitions 1.4.1, 1.4.2)

Sentences of both paradigms are coded as `L`-sentences. -/

structure TranslationPair where
  /-- `T_{L→C}` -/
  toC : Sent → Sent
  /-- `T_{C→L}` -/
  toL : Sent → Sent

/-- `R_L = T_{C→L} ∘ T_{L→C}` -/
def TranslationPair.RL (τ : TranslationPair) (φ : Sent) : Sent := τ.toL (τ.toC φ)

/-- `R_C = T_{L→C} ∘ T_{C→L}` -/
def TranslationPair.RC (τ : TranslationPair) (φ : Sent) : Sent := τ.toC (τ.toL φ)

/-! ## The setting -/

/-- The data the paper works with. -/
structure Setting where
  /-- The arithmetical theorems of ZFC, as a theory in `L`. -/
  T : L.Theory
  /-- The curved model class `M_C` (Section 1.3). -/
  Cur : Model → Prop
  /-- The arithmetic formulation `RH_L`. -/
  RH : Sent
  /-- The canonical translation pair (Definition 1.7.11). -/
  can : TranslationPair

/-- Models of ZFC, through the arithmetic sentences they satisfy. -/
def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ

/-- `ZFC ⊢ φ`: `φ` holds in every model of ZFC. By Gödel's Completeness
    Theorem this is the same as derivability; it is the notion of consequence
    Mathlib's model theory uses. Soundness and completeness then hold by
    definition and are not assumptions. -/
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

variable (S : Setting)

/-- Λ-sound translation pairs (Definition 1.4.3).

Condition (3) is stated for ZFC-provable sentences, which is how it is used
in Lemma 1.5.6 and Theorem 1.7.13. Stated for every sentence, it would say
`M ⊨ S → M ⊨ R_L(S)` in every model of ZFC, and then no Λ-sound pair could
have the obstruction model of Lemma 1.10.2. -/
structure LambdaSound (τ : TranslationPair) : Prop where
  /-- (3) Model invariance. -/
  inv : ∀ φ, S.Prov φ → ∀ M, S.ZFCModel M → M.Sat φ → M.Sat (τ.RL φ)
  /-- (1),(2) Translations of theorems hold in the curved paradigm. -/
  toC_sound : ∀ φ, S.Prov φ → ∀ M, S.Cur M → M.Sat (τ.toC φ)
  /-- (3) Model invariance, curved paradigm. -/
  inv_cur : ∀ φ, S.Prov φ → ∀ M, S.Cur M →
    M.Sat (τ.toC φ) → M.Sat (τ.RC (τ.toC φ))
  /-- Boolean structure is preserved (Definition 1.4.1): negation. -/
  comp : ∀ φ, τ.toC (neg φ) = neg (τ.toC φ) ∧ τ.toL (neg φ) = neg (τ.toL φ)
  /-- (4) Π₁-kernel preservation, at the level of truth in ℕ. -/
  kernel : ∀ φ, IsPi1 φ → (TrueInN φ ↔ TrueInN (τ.RL φ))

/-- `Λ_L(φ) ≠ 0` for the pair `τ` (Definition 1.5.3): some model of ZFC
    separates `φ` from its round trip. -/
def LObstructs (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M, S.ZFCModel M ∧ ¬ (M.Sat φ ↔ M.Sat (τ.RL φ))

/-- `Λ_C(T_{L→C}(φ)) ≠ 0` for the pair `τ` (Definitions 1.5.3, 1.5.5). -/
def CObstructs (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M, S.Cur M ∧ ¬ (M.Sat (τ.toC φ) ↔ M.Sat (τ.RC (τ.toC φ)))

/-- Λ-irreducibility (Definition 1.5.5). -/
def LIrreducible (φ : Sent) : Prop :=
  ∀ τ, LambdaSound S τ → LObstructs S τ φ ∧ CObstructs S τ φ

/-! ## What is assumed -/

/-- The assumptions of Proof I. -/
structure Hypotheses : Prop where
  /-- RH has a Π₁ form with Δ₀ kernel (Proposition 1.18.1). -/
  rh_pi1 : IsPi1 S.RH
  /-- Π₁ Witness Reflection (Theorem 1.17.1). -/
  reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)
  /-- The canonical pair is Λ-sound (Definition 1.7.11, via Theorem 1.7.5). -/
  can_sound : LambdaSound S S.can
  /-- Linear Reconstruction Failure (Lemma 1.10.2, Corollary 1.10.6), in the
      branch where RH holds in ℕ: for every Λ-sound pair there is a model of
      ZFC with `M ⊨ RH_L` and `M ⊭ R_L(RH_L)`. -/
  linear_failure : TrueInN S.RH → ∀ τ, LambdaSound S τ →
    ∃ M, S.ZFCModel M ∧ M.Sat S.RH ∧ ¬ M.Sat (τ.RL S.RH)
  /-- Analytic Reconstruction Failure (Lemma 1.12.4), in the branch where RH
      holds in ℕ: a curved model with `M ⊨ RH_C` and `M ⊭ R_C(RH_C)`. -/
  curved_failure : TrueInN S.RH → ∀ τ, LambdaSound S τ →
    ∃ M, S.Cur M ∧ M.Sat (τ.toC S.RH) ∧ ¬ M.Sat (τ.RC (τ.toC S.RH))
  /-- The obstruction for `¬RH`, in the branch where RH fails in ℕ (the
      symmetric case of Theorem 1.6.1): a curved model with `M ⊨ ¬RH_C` and
      `M ⊭ R_C(¬RH_C)`. -/
  curved_failure_neg : ¬ TrueInN S.RH → ∀ τ, LambdaSound S τ →
    ∃ M, S.Cur M ∧ M.Sat (τ.toC (neg S.RH)) ∧
      ¬ M.Sat (τ.RC (τ.toC (neg S.RH)))

variable {S}

/-! ## What is proved -/

/-- Lemma 1.5.6 (Uniform Preservation under ZFC-Provability). -/
theorem uniform_preservation {τ : TranslationPair}
    (hτ : LambdaSound S τ) {φ : Sent} (hφ : S.Prov φ) (M : Model)
    (hM : S.ZFCModel M) : M.Sat φ ↔ M.Sat (τ.RL φ) :=
  ⟨fun h => hτ.inv φ hφ M hM h, fun _ => hφ M hM⟩

/-- Theorem 1.5.2 (Λ-Reduction Soundness): `ZFC ⊢ φ` implies `Λ_L(φ) = 0`. -/
theorem lambda_reduction_soundness {τ : TranslationPair}
    (hτ : LambdaSound S τ) {φ : Sent} (hφ : S.Prov φ) : ¬ LObstructs S τ φ := by
  rintro ⟨M, hM, hne⟩
  exact hne (uniform_preservation hτ hφ M hM)

/-- Theorem 1.7.13 (Round-Trip Adequacy):
    `ZFC ⊢ φ` implies `ZFC ⊢ φ ↔ R_L^can(φ)`. -/
theorem round_trip_adequacy (H : Hypotheses S) {φ : Sent} (hφ : S.Prov φ) :
    S.Prov (iffS φ (S.can.RL φ)) :=
  fun M hM =>
    (M.sat_iff φ (S.can.RL φ)).mpr (uniform_preservation H.can_sound hφ M hM)

/-- Corollary 1.7.14 (Independence from Obstruction Models): a model of ZFC
    with `M ⊨ φ` and `M ⊭ R_L^can(φ)` gives `ZFC ⊬ φ`. -/
theorem not_provable_of_obstruction_model (H : Hypotheses S) {φ : Sent}
    (hobs : ∃ M, S.ZFCModel M ∧ M.Sat φ ∧ ¬ M.Sat (S.can.RL φ)) :
    ¬ S.Prov φ := by
  intro hφ
  obtain ⟨M, hM, h1, h2⟩ := hobs
  have hiff := round_trip_adequacy H hφ M hM
  exact h2 (((M.sat_iff φ (S.can.RL φ)).mp hiff).mp h1)

/-- Uniform Preservation, curved side. -/
theorem uniform_preservation_cur {τ : TranslationPair}
    (hτ : LambdaSound S τ) {φ : Sent} (hφ : S.Prov φ) (M : Model) (hM : S.Cur M) :
    M.Sat (τ.toC φ) ↔ M.Sat (τ.RC (τ.toC φ)) :=
  ⟨fun h => hτ.inv_cur φ hφ M hM h, fun _ => hτ.toC_sound φ hφ M hM⟩

/-- Theorem 1.18.3 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`.

    By cases. If RH holds in ℕ there is nothing to prove. If RH fails in ℕ,
    witness reflection gives `ZFC ⊢ ¬RH`; uniform preservation for the
    canonical pair then makes `¬RH_C` and its round trip agree in every
    curved model, contradicting the obstruction for `¬RH`. -/
theorem RH_true_in_N (H : Hypotheses S) : TrueInN S.RH := by
  by_contra hfalse
  have hprov : S.Prov (neg S.RH) := H.reflection S.RH H.rh_pi1 hfalse
  obtain ⟨M, hM, h1, h2⟩ := H.curved_failure_neg hfalse S.can H.can_sound
  exact h2 ((uniform_preservation_cur H.can_sound hprov M hM).mp h1)

/-- Theorem 1.13.1 (Λ-Irreducibility of RH). -/
theorem RH_lambda_irreducible (H : Hypotheses S) : LIrreducible S S.RH := by
  intro τ hτ
  have htrue := RH_true_in_N H
  constructor
  · obtain ⟨M, hM, h1, h2⟩ := H.linear_failure htrue τ hτ
    exact ⟨M, hM, fun hiff => h2 (hiff.mp h1)⟩
  · obtain ⟨M, hM, h1, h2⟩ := H.curved_failure htrue τ hτ
    exact ⟨M, hM, fun hiff => h2 (hiff.mp h1)⟩

/-- Corollary 1.13.2, first half: `ZFC ⊬ RH` (Remark 1.7.15, steps 3–5). -/
theorem RH_not_provable (H : Hypotheses S) : ¬ S.Prov S.RH :=
  not_provable_of_obstruction_model H
    (H.linear_failure (RH_true_in_N H) S.can H.can_sound)

/-- Corollary 1.13.2, second half: `ZFC ⊬ ¬RH`. The linear obstruction model
    is a model of ZFC in which `RH_L` holds. -/
theorem neg_RH_not_provable (H : Hypotheses S) : ¬ S.Prov (neg S.RH) := by
  intro hneg
  obtain ⟨M, hM, h1, _⟩ := H.linear_failure (RH_true_in_N H) S.can H.can_sound
  exact (M.sat_neg S.RH).mp (hneg M hM) h1

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent (H : Hypotheses S) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable H, neg_RH_not_provable H⟩

end RH.Paper
