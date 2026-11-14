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
abstract Π₁ sentence; no number theory is used. Provability is defined as
truth in all models of ZFC, so soundness and completeness are not assumptions.

**Proved here:** Uniform Preservation (1.5.6), Λ-Reduction Soundness (1.5.2),
Round-Trip Adequacy (1.7.13), Independence from Obstruction Models (1.7.14),
ZFC-undecidability of RH (1.13.2), truth of RH in ℕ (1.18.2, 1.18.3).

**Assumed** (the structure `Hypotheses`):
* published: the Π₁ form of RH; Π₁ witness reflection;
* the paper's own: Λ-soundness of the canonical pair; and the existence of
  the obstruction model, a model of ZFC in which `RH_L` is true and its
  canonical round trip is false.

Every theorem below is conditional on these four.
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
in Lemma 1.5.6 and Theorem 1.7.13. -/
structure LambdaSound (τ : TranslationPair) : Prop where
  /-- (3) Model invariance. -/
  inv : ∀ φ, S.Prov φ → ∀ M, S.ZFCModel M → M.Sat φ → M.Sat (τ.RL φ)
  /-- Boolean structure is preserved (Definition 1.4.1): negation. -/
  comp : ∀ φ, τ.toC (neg φ) = neg (τ.toC φ) ∧ τ.toL (neg φ) = neg (τ.toL φ)
  /-- (4) Π₁-kernel preservation, at the level of truth in ℕ. -/
  kernel : ∀ φ, IsPi1 φ → (TrueInN φ ↔ TrueInN (τ.RL φ))

/-- `Λ_L(φ) ≠ 0` for the pair `τ` (Definition 1.5.3): some model of ZFC
    separates `φ` from its round trip. -/
def LObstructs (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M, S.ZFCModel M ∧ ¬ (M.Sat φ ↔ M.Sat (τ.RL φ))

/-! ## What is assumed -/

/-- The assumptions of Proof I. The first two are published results. The
    last two are the paper's own. -/
structure Hypotheses : Prop where
  /-- RH has a Π₁ form with Δ₀ kernel (Proposition 1.18.1;
      Davis–Matiyasevich–Robinson). -/
  rh_pi1 : IsPi1 S.RH
  /-- Π₁ Witness Reflection (Theorem 1.17.1). -/
  reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)
  /-- The canonical pair is Λ-sound (Definition 1.7.11, via Theorem 1.7.5). -/
  can_sound : LambdaSound S S.can
  /-- The obstruction model (Lemma 1.10.2, Corollary 1.10.6): there is a
      model of ZFC in which `RH_L` is true and its canonical round trip is
      false. This is the mathematical content of Proof I. -/
  obstruction_model :
    ∃ M, S.ZFCModel M ∧ M.Sat S.RH ∧ ¬ M.Sat (S.can.RL S.RH)

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

/-- What Corollary 1.10.6 amounts to: a model of ZFC with `M ⊨ φ` and
    `M ⊭ R_L(φ)` exists exactly when ZFC does not prove `φ → R_L(φ)`. -/
theorem obstruction_model_iff_not_provable (τ : TranslationPair) (φ : Sent) :
    (∃ M, S.ZFCModel M ∧ M.Sat φ ∧ ¬ M.Sat (τ.RL φ)) ↔
      ¬ S.Prov (impS φ (τ.RL φ)) := by
  constructor
  · rintro ⟨M, hM, h1, h2⟩ hprov
    exact h2 ((M.sat_imp φ (τ.RL φ)).mp (hprov M hM) h1)
  · intro hnot
    by_contra hno
    apply hnot
    intro M hM
    rw [M.sat_imp]
    intro h1
    by_contra h2
    exact hno ⟨M, hM, h1, h2⟩

/-- `Λ_L(RH) ≠ 0` for the canonical pair (Corollary 1.10.3). -/
theorem RH_obstructed (H : Hypotheses S) : LObstructs S S.can S.RH := by
  obtain ⟨M, hM, h1, h2⟩ := H.obstruction_model
  exact ⟨M, hM, fun hiff => h2 (hiff.mp h1)⟩

/-- `ZFC ⊬ RH`. Reductio, entirely about ZFC and its models: if ZFC proved
    RH, the round trip would agree with RH in every model of ZFC; in the
    obstruction model it does not. -/
theorem RH_not_provable (H : Hypotheses S) : ¬ S.Prov S.RH :=
  not_provable_of_obstruction_model H H.obstruction_model

/-- `ZFC ⊬ ¬RH`: the obstruction model is a model of ZFC in which `RH_L`
    is true. -/
theorem neg_RH_not_provable (H : Hypotheses S) : ¬ S.Prov (neg S.RH) := by
  intro hneg
  obtain ⟨M, hM, h1, _⟩ := H.obstruction_model
  exact (M.sat_neg S.RH).mp (hneg M hM) h1

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
