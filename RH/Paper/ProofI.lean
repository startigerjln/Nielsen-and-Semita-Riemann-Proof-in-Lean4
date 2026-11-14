import RH.Paper.Arith
/-!
# Deductive structure of Proof I of Nielsen & Semita

The arithmetic theory, its designated RH sentence, and the translation pair
are parameters. The theorem signatures give the premises for each deduction.
-/

open FirstOrder

namespace RH.Paper

/-! ## Sentences, models, truth -/

abbrev Sent := L.Sentence

def neg (φ : Sent) : Sent := Language.BoundedFormula.not φ
def iffS (φ ψ : Sent) : Sent := Language.BoundedFormula.iff φ ψ
def impS (φ ψ : Sent) : Sent := Language.BoundedFormula.imp φ ψ

structure Model where
  carrier : Type
  str : L.Structure carrier

def Model.Sat (M : Model) (φ : Sent) : Prop :=
  @Language.Sentence.Realize L M.carrier M.str φ

theorem Model.sat_neg (M : Model) (φ : Sent) : M.Sat (neg φ) ↔ ¬ M.Sat φ := by
  letI := M.str; exact Language.BoundedFormula.realize_not

theorem Model.sat_iff (M : Model) (φ ψ : Sent) :
    M.Sat (iffS φ ψ) ↔ (M.Sat φ ↔ M.Sat ψ) := by
  letI := M.str; exact Language.BoundedFormula.realize_iff

theorem Model.sat_imp (M : Model) (φ ψ : Sent) :
    M.Sat (impS φ ψ) ↔ (M.Sat φ → M.Sat ψ) := by
  letI := M.str; exact Language.BoundedFormula.realize_imp

def TrueInN (φ : Sent) : Prop :=
  @Language.Sentence.Realize L ℕ natStructure φ

def IsPi1 (φ : Sent) : Prop :=
  ∃ ψ : L.BoundedFormula Empty 1, IsDelta0 ψ ∧ φ = Language.BoundedFormula.all ψ

/-! ## Translation pairs and round trips -/

structure TranslationPair where
  toC : Sent → Sent
  toL : Sent → Sent

def TranslationPair.RL (τ : TranslationPair) (φ : Sent) : Sent := τ.toL (τ.toC φ)

/-! ## The setting -/

structure Setting where
  T : L.Theory
  RH : Sent

def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

variable (S : Setting)

def Setting.RoundTripFails (S : Setting) (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M : Model, S.ZFCModel M ∧ ¬ M.Sat (τ.RL φ)

def Setting.Disagrees (S : Setting) (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M : Model, S.ZFCModel M ∧ M.Sat φ ∧ ¬ M.Sat (τ.RL φ)

/-! ## Theorems -/

/-- Jenny Lorraine Nielsen observed that any witness to round-trip failure
    suffices: preservation would force the round trip to hold in that model. -/
theorem not_provable_of_round_trip_failure {τ : TranslationPair} {φ : Sent}
    (pres : S.Prov φ → S.Prov (τ.RL φ))
    (failure : S.RoundTripFails τ φ) : ¬ S.Prov φ := by
  intro hprov
  obtain ⟨M, hM, hfail⟩ := failure
  exact hfail (pres hprov M hM)

theorem RH_not_provable {τ : TranslationPair}
    (pres : S.Prov S.RH → S.Prov (τ.RL S.RH))
    (failure : S.RoundTripFails τ S.RH) : ¬ S.Prov S.RH :=
  not_provable_of_round_trip_failure S pres failure

theorem neg_RH_not_provable {τ : TranslationPair}
    (pres : S.Prov (neg S.RH) → S.Prov (τ.RL (neg S.RH)))
    (failure : S.RoundTripFails τ (neg S.RH)) : ¬ S.Prov (neg S.RH) :=
  not_provable_of_round_trip_failure S pres failure

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent {τ : TranslationPair}
    (pres : ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ))
    (failure_rh : S.RoundTripFails τ S.RH)
    (failure_neg : S.RoundTripFails τ (neg S.RH)) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S (pres S.RH) failure_rh,
    neg_RH_not_provable S (pres (neg S.RH)) failure_neg⟩

/-- Theorem 1.18.2 (Truth from Unrefutability). -/
theorem truth_from_unrefutability
    (reflection : ∀ ψ, IsPi1 ψ → ¬ TrueInN ψ → S.Prov (neg ψ))
    {φ : Sent} (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (reflection φ hpi hfalse)

/-- Theorem 1.18.3 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`. -/
theorem RH_true_in_N
    (rh_pi1 : IsPi1 S.RH)
    (reflection : ∀ ψ, IsPi1 ψ → ¬ TrueInN ψ → S.Prov (neg ψ))
    (hnot : ¬ S.Prov (neg S.RH)) : TrueInN S.RH :=
  truth_from_unrefutability S reflection rh_pi1 hnot

/-! ### Connection to the Λ-sound framework -/

structure LambdaSound (φ : Sent) (τ : TranslationPair) : Prop where
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M → M.Sat ψ → M.Sat (τ.RL ψ)
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

/-- A model in which the original sentence is true and its round trip
    fails refutes the biconditional. -/
theorem changes_of_disagreement {τ : TranslationPair} {φ : Sent}
    (disagreement : S.Disagrees τ φ) : ¬ S.Prov (iffS φ (τ.RL φ)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := disagreement
  exact hfail (((M.sat_iff φ (τ.RL φ)).mp (hprov M hM)).mp hsat)

theorem changes_rh {τ : TranslationPair} (disagreement : S.Disagrees τ S.RH) :
    ¬ S.Prov (iffS S.RH (τ.RL S.RH)) :=
  changes_of_disagreement S disagreement

theorem changes_neg {τ : TranslationPair}
    (disagreement : S.Disagrees τ (neg S.RH)) :
    ¬ S.Prov (iffS (neg S.RH) (τ.RL (neg S.RH))) :=
  changes_of_disagreement S disagreement

theorem lambda_sound_of_disagreement {τ : TranslationPair} {φ : Sent}
    (pres : ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ))
    (comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ))
    (kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ)))
    (disagreement : S.Disagrees τ φ) : LambdaSound S φ τ where
  inv ψ hψ M hM _ := pres ψ hψ M hM
  comp := comp
  kernel := kernel
  changes := changes_of_disagreement S disagreement

/-- Lemma 1.5.6 (Uniform Preservation). -/
theorem uniform_preservation {S' : Setting} {φ : Sent} {τ : TranslationPair}
    (hτ : LambdaSound S' φ τ) {ψ : Sent} (hψ : S'.Prov ψ) (M : Model)
    (hM : S'.ZFCModel M) : M.Sat ψ ↔ M.Sat (τ.RL ψ) :=
  ⟨fun h => hτ.inv ψ hψ M hM h, fun _ => hψ M hM⟩

/-- Theorem 1.7.13 (Round-Trip Adequacy). -/
theorem round_trip_adequacy {S' : Setting} {φ : Sent} {τ : TranslationPair}
    (hτ : LambdaSound S' φ τ) {ψ : Sent} (hψ : S'.Prov ψ) :
    S'.Prov (iffS ψ (τ.RL ψ)) :=
  fun M hM => (M.sat_iff ψ (τ.RL ψ)).mpr (uniform_preservation hτ hψ M hM)

/-- Remark 1.6.2: provability contradicts Λ-soundness. -/
theorem no_lambda_sound_of_provable {S' : Setting} {φ : Sent} (hφ : S'.Prov φ) :
    ¬ ∃ τ, LambdaSound S' φ τ := by
  rintro ⟨τ, hτ⟩
  exact hτ.changes (round_trip_adequacy hτ hφ)

end RH.Paper
