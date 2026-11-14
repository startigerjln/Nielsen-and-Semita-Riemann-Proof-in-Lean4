import RH.Paper.Arith
/-!
# Proof I of Nielsen & Semita, formalized as written

This file follows Section 1 of the paper (version of May 16, 2026,
PhilArchive NIEPOT-5v52). The independence argument is the reductio of
Theorem 1.6.1 and Remark 1.6.2:

1. Suppose `ZFC ⊢ RH` (for reductio only).
2. Then a Λ-sound translation pair would have to exist (Theorem 1.7.6).
3. But under that supposition no Λ-sound pair can exist: by Round-Trip
   Adequacy (Theorem 1.7.13) its round trip of RH would be ZFC-equivalent to
   RH, while a Λ-sound pair changes RH (Lemma 1.7.12).
4. So `ZFC ⊬ RH`. The same argument applies to `¬RH`. Truth in ℕ then
   follows by Π₁ witness reflection (§1.17, §1.18).

The file contains no `axiom` and no `sorry`. The arithmetic form of RH is an
abstract Π₁ sentence. Provability is defined as truth in all models of ZFC,
so soundness and completeness are not assumptions.

**Proved here:** Uniform Preservation (1.5.6), Round-Trip Adequacy (1.7.13),
step 3 above, ZFC-undecidability of RH (1.13.2), truth of RH in ℕ (1.18.3).

**Assumed** (the structure `Hypotheses`):
* published: the Π₁ form of RH; Π₁ witness reflection;
* the paper's own: Theorem 1.7.6, for RH and for ¬RH — a ZFC proof of the
  sentence forces a Λ-sound translation pair to exist.

Every theorem that takes `H : Hypotheses S` is conditional on these.
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

/-- Implication of two sentences. -/
def impS (φ ψ : Sent) : Sent := Language.BoundedFormula.imp φ ψ

theorem Model.sat_imp (M : Model) (φ ψ : Sent) :
    M.Sat (impS φ ψ) ↔ (M.Sat φ → M.Sat ψ) := by
  letI := M.str
  exact Language.BoundedFormula.realize_imp

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
  /-- The arithmetic formulation `RH_L`. -/
  RH : Sent

/-- Models of ZFC, through the arithmetic sentences they satisfy. -/
def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ

/-- `ZFC ⊢ φ`: `φ` holds in every model of ZFC. By Gödel's Completeness
    Theorem this is the same as derivability. Soundness and completeness
    hold by definition. -/
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

variable (S : Setting)

/-- Λ-sound translation pairs, relative to the sentence `φ` whose two
    formulations are being identified.

    The first three fields are Definition 1.4.3 (with condition (3) for
    ZFC-provable sentences, as used in Lemma 1.5.6 and Theorem 1.7.13).
    The last field is Lemma 1.7.12: the round trip of `φ` is a different
    sentence, not ZFC-equivalent to `φ`. Without it the pair that sends
    every sentence to itself would be Λ-sound. -/
structure LambdaSound (φ : Sent) (τ : TranslationPair) : Prop where
  /-- (3) Model invariance. -/
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M → M.Sat ψ → M.Sat (τ.RL ψ)
  /-- Boolean structure is preserved (Definition 1.4.1): negation. -/
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  /-- (4) Π₁-kernel preservation, at the level of truth in ℕ. -/
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  /-- Lemma 1.7.12: the round trip changes `φ`. -/
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

/-! ## What is assumed -/

/-- The assumptions of Proof I. -/
structure Hypotheses : Prop where
  /-- RH has a Π₁ form with Δ₀ kernel (Proposition 1.18.1;
      Davis–Matiyasevich–Robinson). -/
  rh_pi1 : IsPi1 S.RH
  /-- Π₁ Witness Reflection (Theorem 1.17.1). -/
  reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)
  /-- Theorem 1.7.6 (Paradigm Dependence): a ZFC proof of RH forces a
      Λ-sound translation pair to exist. -/
  induced : S.Prov S.RH → ∃ τ, LambdaSound S S.RH τ
  /-- The symmetric case of Theorem 1.6.1, for `¬RH`. -/
  induced_neg : S.Prov (neg S.RH) → ∃ τ, LambdaSound S (neg S.RH) τ

variable {S}

/-! ## What is proved -/

/-- Lemma 1.5.6 (Uniform Preservation under ZFC-Provability). -/
theorem uniform_preservation {φ : Sent} {τ : TranslationPair}
    (hτ : LambdaSound S φ τ) {ψ : Sent} (hψ : S.Prov ψ) (M : Model)
    (hM : S.ZFCModel M) : M.Sat ψ ↔ M.Sat (τ.RL ψ) :=
  ⟨fun h => hτ.inv ψ hψ M hM h, fun _ => hψ M hM⟩

/-- Theorem 1.7.13 (Round-Trip Adequacy): `ZFC ⊢ ψ` implies
    `ZFC ⊢ ψ ↔ R_L(ψ)` for a Λ-sound pair. -/
theorem round_trip_adequacy {φ : Sent} {τ : TranslationPair}
    (hτ : LambdaSound S φ τ) {ψ : Sent} (hψ : S.Prov ψ) :
    S.Prov (iffS ψ (τ.RL ψ)) :=
  fun M hM => (M.sat_iff ψ (τ.RL ψ)).mpr (uniform_preservation hτ hψ M hM)

/-- Step 3 of the reductio (Remark 1.6.2): if `ZFC ⊢ φ`, no translation
    pair can be Λ-sound for `φ`. -/
theorem no_lambda_sound_of_provable {φ : Sent} (hφ : S.Prov φ) :
    ¬ ∃ τ, LambdaSound S φ τ := by
  rintro ⟨τ, hτ⟩
  exact hτ.changes (round_trip_adequacy hτ hφ)

/-- Theorem 1.6.1, one direction: if a ZFC proof of `φ` would force a
    Λ-sound pair for `φ` to exist, then `ZFC ⊬ φ`. -/
theorem not_provable_of_induced {φ : Sent}
    (hind : S.Prov φ → ∃ τ, LambdaSound S φ τ) : ¬ S.Prov φ :=
  fun hφ => no_lambda_sound_of_provable hφ (hind hφ)

/-- Given step 3, the hypothesis of Theorem 1.7.6 for `φ` says exactly
    that `ZFC ⊬ φ`. -/
theorem induced_iff_not_provable (φ : Sent) :
    (S.Prov φ → ∃ τ, LambdaSound S φ τ) ↔ ¬ S.Prov φ :=
  ⟨not_provable_of_induced, fun hnot hφ => absurd hφ hnot⟩

/-- `ZFC ⊬ RH`. -/
theorem RH_not_provable (H : Hypotheses S) : ¬ S.Prov S.RH :=
  not_provable_of_induced H.induced

/-- `ZFC ⊬ ¬RH`. -/
theorem neg_RH_not_provable (H : Hypotheses S) : ¬ S.Prov (neg S.RH) :=
  not_provable_of_induced H.induced_neg

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent (H : Hypotheses S) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable H, neg_RH_not_provable H⟩

/-- Theorem 1.18.2 (Truth of RH from Independence), for any Π₁ sentence. -/
theorem truth_from_unrefutability (H : Hypotheses S) {φ : Sent}
    (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (H.reflection φ hpi hfalse)

/-- Theorem 1.18.3 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`. -/
theorem RH_true_in_N (H : Hypotheses S) : TrueInN S.RH :=
  truth_from_unrefutability H H.rh_pi1 (neg_RH_not_provable H)

end RH.Paper
