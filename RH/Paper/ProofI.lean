import RH.Paper.Arith
/-!
# Proof I: deductive structure of Nielsen & Semita

The manuscript uses nonstandard arithmetic, overspill and compactness,
not rational approximation with planted zeros. This module separates
the formal deductions from the outstanding RH-specific consistency
argument. No project axioms or sorry declarations are introduced.

Setting.T and Setting.RH are parameters; their intended instantiation
as the arithmetic consequences of ZFC and a concrete arithmetic RH,
and the bridge to Mathlib's RiemannHypothesis, remain to be supplied.
The translation maps below are arithmetic syntax placeholders for
the manuscript's two-language construction.
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
  /-- T is consistent: it has a model. (Standard assumption for ZFC.) -/
  consistent : ∃ M : Model, ∀ φ ∈ T, M.Sat φ

def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

/-! ## Explicit proof obligations -/

/-- Semantic finite satisfiability, in the same language as the manuscript's
    arithmetic reduct. -/
def FiniteSatisfiable (Γ : Set Sent) : Prop :=
  ∀ Γ₀ : Finset Sent, ↑Γ₀ ⊆ Γ → ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-- First-order compactness, stated as an explicit input until the
    corresponding Mathlib theorem is connected to Model.Sat. -/
def Compactness : Prop :=
  ∀ Γ : Set Sent, FiniteSatisfiable Γ → ∃ M : Model, ∀ φ ∈ Γ, M.Sat φ

/-- The arithmetic theory used in the manuscript's ZFC-level
    disagreement construction. For the initial linear obstruction the
    intended base is IΣ₁; for independence the intended base is the
    arithmetic consequences of ZFC. These are not interchangeable. -/
def disagreementTheory (S : Setting) (τ : TranslationPair) : Set Sent :=
  S.T ∪ {S.RH} ∪ {neg (τ.RL S.RH)}

/-- The manuscript's unresolved overspill/compactness input:
    finite fragments must be satisfiable even when they contain both
    RH and the negation of its round trip. Overspill alone does not
    establish this. It is a hypothesis for the specific setting and
    pair, not a theorem quantified over arbitrary settings. -/
def OverspillFiniteSatisfiability (S : Setting) (τ : TranslationPair) : Prop :=
  FiniteSatisfiable (disagreementTheory S τ)

/-- Σ₁ witness reflection, an explicit input for the intended
    arithmetic theory of ZFC. -/
def WitnessReflection (S : Setting) : Prop :=
  ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)

/-- Provability preservation for the specified round trip, a separate
    manuscript obligation (Uniform Preservation / Round-Trip Adequacy). -/
def RoundTripPreserves (S : Setting) (τ : TranslationPair) : Prop :=
  ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ)

/-! ## Deductions from the stated inputs -/

/-- Compactness converts the RH-specific finite-satisfiability input
    into the ZFC-level disagreement model, when S.T is the arithmetic
    theory of ZFC. -/
theorem canonical_disagreement_rh (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH ∧
      ¬ M.Sat (τ.RL S.RH) := by
  obtain ⟨M, hM⟩ := hc (disagreementTheory S τ) hf
  refine ⟨M, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hM φ (Set.mem_union_left _ (Set.mem_union_left _ hφ))
  · exact hM S.RH (Set.mem_union_left _
      (Set.mem_union_right _ rfl))
  · intro hsat
    have h := hM (neg (τ.RL S.RH)) (Set.mem_union_right _ rfl)
    exact ((M.sat_neg (τ.RL S.RH)).mp h) hsat

/-- Non-provability follows from round-trip preservation and the
    disagreement model. -/
theorem RH_not_provable (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ)
    (hp : RoundTripPreserves S τ) : ¬ S.Prov S.RH := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := canonical_disagreement_rh S τ hc hf
  exact hfail (hp S.RH hprov M hM)

/-- Non-refutability requires only a model of the base theory and RH;
    neither a round trip nor an analytic obstruction is needed here. -/
theorem neg_RH_not_provable_of_model (S : Setting)
    (hmodel : ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH) :
    ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, hsat⟩ := hmodel
  exact ((M.sat_neg S.RH).mp (hprov M hM)) hsat

theorem neg_RH_not_provable (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ) :
    ¬ S.Prov (neg S.RH) := by
  obtain ⟨M, hM, hsat, _⟩ := canonical_disagreement_rh S τ hc hf
  exact neg_RH_not_provable_of_model S ⟨M, hM, hsat⟩

theorem RH_independent (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ)
    (hp : RoundTripPreserves S τ) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S τ hc hf hp, neg_RH_not_provable S τ hc hf⟩

/-- Theorem 1.18.2: truth from non-refutability. -/
theorem truth_from_unrefutability (S : Setting)
    (hr : WitnessReflection S) {φ : Sent}
    (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (hr φ hpi hfalse)

/-- Theorem 1.18.3, minimal metamathematical route. -/
theorem RH_true_from_model (S : Setting)
    (hpi : IsPi1 S.RH) (hr : WitnessReflection S)
    (hmodel : ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH) :
    TrueInN S.RH :=
  truth_from_unrefutability S hr hpi (neg_RH_not_provable_of_model S hmodel)

/-- Conditional RH truth via the manuscript's compactness route.
    The RH-specific finite-satisfiability input is not proved here. -/
theorem RH_true_in_N (S : Setting) (τ : TranslationPair)
    (hpi : IsPi1 S.RH) (hr : WitnessReflection S)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ) :
    TrueInN S.RH :=
  truth_from_unrefutability S hr hpi (neg_RH_not_provable S τ hc hf)

/-! ## Provable-fragment preservation framework

This structure captures the conditions used in the deductive reductio,
not the entire two-language Definition 1.4.3 of the manuscript.
-/

structure LambdaSound (S : Setting) (φ : Sent) (τ : TranslationPair) : Prop where
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M → M.Sat ψ → M.Sat (τ.RL ψ)
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

theorem changes_rh (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ) :
    ¬ S.Prov (iffS S.RH (τ.RL S.RH)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := canonical_disagreement_rh S τ hc hf
  exact hfail (((M.sat_iff S.RH (τ.RL S.RH)).mp (hprov M hM)).mp hsat)

theorem canonical_lambda_sound_rh (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ)
    (hp : RoundTripPreserves S τ)
    (hcomp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ))
    (hk : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))) :
    LambdaSound S S.RH τ where
  inv ψ hψ M hM _ := hp ψ hψ M hM
  comp := hcomp
  kernel := hk
  changes := changes_rh S τ hc hf

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

#print axioms RH.Paper.RH_true_in_N
#print axioms RH.Paper.RH_independent
