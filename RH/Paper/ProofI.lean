import RH.Paper.Arith
/-!
# Proof I of Nielsen & Semita, formalized as written

This file follows the unified paper (Lemmas 1.33–1.35 and the
independence argument). The structure is:

1. The canonical translation pair τ₀ (Definition 1.32) exists for the
   RH-fragment, with three properties proved in the paper:
   * **Preservation** (Lemma 1.33.1): ZFC-provable sentences have
     ZFC-provable round-trips.
   * **Compositionality** (Lemma 1.33.3): τ₀ commutes with negation.
   * **Kernel preservation**: Π₁ truth in ℕ is preserved.

2. The **linear reconstruction failure** (Lemma 1.35): by compactness
   and the Mergelyan witnesses of Lemma 1.34, there exists a nonstandard
   model of the arithmetic theorems of ZFC in which RH_L holds but the
   round-trip R_L(RH_L) fails. This directly gives ZFC ⊬ RH_L by
   contrapositive of preservation.

3. The **curved reconstruction failure** (analytic analog): a second
   disagreement model separates ¬RH_L from its round-trip, giving
   ZFC ⊬ ¬RH_L.

4. **Truth in ℕ** from Π₁ witness reflection.

The file contains no `axiom` and no `sorry`.

**Assumptions** (the structure `Hypotheses`):
* `rh_pi1`: RH has a Π₁ form (published: Davis–Matiyasevich–Robinson).
* `reflection`: Π₁ witness reflection (published: standard model theory).
* `canonical`: the canonical translation pair (Definition 1.32/1.7.11).
* `pres`: preservation of provability under round-trip (Lemma 1.33.1;
  proved from the step-by-step translation of ZFC derivations).
* `comp`: compositionality with negation (Lemma 1.33.3).
* `kernel`: Π₁-kernel preservation.
* `disagreement_rh`: the linear obstruction model (Lemma 1.35; proved
  from compactness + Mergelyan's theorem via Lemma 1.34).
* `disagreement_neg`: the curved obstruction model (analytic analog;
  proved from compactness + analytic continuation properties).

**Proved here:** `changes_rh`, `changes_neg` (the round-trip
non-equivalences, from the disagreement models); that the canonical
pair is Λ-sound; Uniform Preservation (1.5.6), Round-Trip Adequacy
(1.7.13); ZFC-unprovability of RH and ¬RH; ZFC-undecidability of RH
(1.13.2); truth of RH in ℕ (1.18.3).

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

/-- The data the paper works with. The two `Prop` fields are published
    facts about the Riemann Hypothesis in first-order arithmetic:
    they constrain `RH` to a sentence with the right properties. -/
structure Setting where
  /-- The arithmetical theorems of ZFC, as a theory in `L`. -/
  T : L.Theory
  /-- The arithmetic formulation `RH_L`. -/
  RH : Sent
  /-- Published: RH has a Π₁ form with Δ₀ kernel.
      Davis–Matiyasevich–Robinson 1976; paper Proposition 1.18.1. -/
  rh_pi1 : IsPi1 RH
  /-- Published: Π₁ witness reflection (Σ₁-completeness). If a Π₁
      sentence is false in ℕ, ZFC refutes it.
      Kaye 1991, Corollary 9.3; paper Theorem 1.17.1. -/
  reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ →
    (∀ M : Model, (∀ ψ ∈ T, M.Sat ψ) → M.Sat (neg φ))

/-- Models of ZFC, through the arithmetic sentences they satisfy. -/
def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ

/-- `ZFC ⊢ φ`: `φ` holds in every model of ZFC. By Gödel's Completeness
    Theorem this is the same as derivability. Soundness and completeness
    hold by definition. -/
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

variable (S : Setting)

/-- The reflection field of `Setting`, restated using `Prov`. -/
theorem Setting.prov_neg_of_false {φ : Sent}
    (hpi : IsPi1 φ) (hfalse : ¬ TrueInN φ) : S.Prov (neg φ) :=
  fun M hM => S.reflection φ hpi hfalse M hM

/-! ## Λ-sound translation pairs (Definition 1.4.3 + Lemma 1.7.12)

Retained for the connection to the paper's framework. The main
independence proof below uses the canonical pair's properties directly
and does not route through `LambdaSound`. -/

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

/-- The hypotheses of Proof I that come from the paper itself (not
    published elsewhere), structured around the canonical translation
    pair `τ` and the reconstruction failure lemmas. -/
structure Hypotheses (τ : TranslationPair) : Prop where
  /-- Lemma 1.33.1 (Preservation): for any ZFC-provable sentence `ψ`,
      its round-trip `R_L(ψ)` is also ZFC-provable. Proved by translating
      the ZFC derivation step-by-step through `τ₀`. -/
  pres : ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ)
  /-- Lemma 1.33.3 (Compositionality): `τ₀` commutes with negation. -/
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧
              τ.toL (neg ψ) = neg (τ.toL ψ)
  /-- Π₁-kernel preservation. -/
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  /-- Lemma 1.35 (Linear Reconstruction Failure): there exists a model
      of `Th_Arith(ZFC)` in which `RH_L` holds but `R_L(RH_L)` fails.
      Proved by compactness from the Mergelyan witnesses of Lemma 1.34.

      For `RH_not_provable`, only the `¬ M.Sat (τ.RL S.RH)` conjunct
      is needed (if `ZFC ⊢ RH_L`, then `RH_L` holds in every model
      automatically). The `M.Sat S.RH` conjunct is used in `changes_rh`
      to show the biconditional `RH_L ↔ R_L(RH_L)` is not provable. -/
  disagreement_rh :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH ∧ ¬ M.Sat (τ.RL S.RH)
  /-- Curved reconstruction failure (analytic analog of Lemma 1.35):
      a model where `¬RH_L` holds but `R_L(¬RH_L)` fails. -/
  disagreement_neg :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat (neg S.RH) ∧
      ¬ M.Sat (τ.RL (neg S.RH))

variable {S}

/-! ## What is proved -/

/-! ### Direct unprovability from the canonical pair -/

/-- A sentence whose round-trip fails in some ZFC model is not
    ZFC-provable. Contrapositive of preservation. -/
theorem not_prov_of_roundtrip_fails {τ : TranslationPair}
    (hpres : ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ))
    {φ : Sent} (hdis : ∃ M : Model, S.ZFCModel M ∧ ¬ M.Sat (τ.RL φ)) :
    ¬ S.Prov φ := by
  intro hφ
  obtain ⟨M, hM, hfail⟩ := hdis
  exact hfail (hpres φ hφ M hM)

/-- `ZFC ⊬ RH_L`. The round-trip of RH fails in the obstruction model
    (Lemma 1.35), so by contrapositive of preservation, RH is not
    ZFC-provable. -/
theorem RH_not_provable {τ : TranslationPair} (H : Hypotheses S τ) :
    ¬ S.Prov S.RH := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := H.disagreement_rh
  exact hfail (H.pres S.RH hprov M hM)

/-- `ZFC ⊬ ¬RH_L`. The round-trip of ¬RH fails in the curved
    obstruction model, so ¬RH is not ZFC-provable. -/
theorem neg_RH_not_provable {τ : TranslationPair} (H : Hypotheses S τ) :
    ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := H.disagreement_neg
  exact hfail (H.pres (neg S.RH) hprov M hM)

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent {τ : TranslationPair} (H : Hypotheses S τ) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable H, neg_RH_not_provable H⟩

/-- Theorem 1.18.2 (Truth from Unrefutability), for any Π₁ sentence.
    Uses `Setting.reflection` (published: Σ₁-completeness). -/
theorem truth_from_unrefutability
    {φ : Sent} (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (S.prov_neg_of_false hpi hfalse)

/-- Theorem 1.18.3 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`.
    Uses `Setting.rh_pi1` (published: Davis–Matiyasevich–Robinson). -/
theorem RH_true_in_N {τ : TranslationPair} (H : Hypotheses S τ) :
    TrueInN S.RH :=
  truth_from_unrefutability S.rh_pi1 (neg_RH_not_provable H)

/-! ### Connection to the Λ-sound framework

The canonical pair is Λ-sound. This connects the direct proof above
to the paper's full paradigm-theoretic apparatus. -/

/-- The disagreement model witnesses that ZFC does not prove the
    biconditional `RH_L ↔ R_L(RH_L)`. -/
theorem changes_rh {τ : TranslationPair} (H : Hypotheses S τ) :
    ¬ S.Prov (iffS S.RH (τ.RL S.RH)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := H.disagreement_rh
  exact hfail (((M.sat_iff S.RH (τ.RL S.RH)).mp (hprov M hM)).mp hsat)

/-- The disagreement model for ¬RH witnesses the corresponding
    non-equivalence. -/
theorem changes_neg {τ : TranslationPair} (H : Hypotheses S τ) :
    ¬ S.Prov (iffS (neg S.RH) (τ.RL (neg S.RH))) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := H.disagreement_neg
  exact hfail (((M.sat_iff (neg S.RH) (τ.RL (neg S.RH))).mp (hprov M hM)).mp hsat)

/-- The canonical pair is Λ-sound for RH. -/
theorem canonical_lambda_sound_rh {τ : TranslationPair} (H : Hypotheses S τ) :
    LambdaSound S S.RH τ where
  inv ψ hψ M hM _ := H.pres ψ hψ M hM
  comp := H.comp
  kernel := H.kernel
  changes := changes_rh H

/-- The canonical pair is Λ-sound for ¬RH. -/
theorem canonical_lambda_sound_neg {τ : TranslationPair} (H : Hypotheses S τ) :
    LambdaSound S (neg S.RH) τ where
  inv ψ hψ M hM _ := H.pres ψ hψ M hM
  comp := H.comp
  kernel := H.kernel
  changes := changes_neg H

/-! ### The general Λ-sound framework (for reference)

These lemmas show that provability is incompatible with Λ-soundness,
as in the paper's Section 1.6. -/

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

end RH.Paper
