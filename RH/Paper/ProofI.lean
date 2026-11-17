import RH.Paper.Arith
import Mathlib.ModelTheory.Satisfiability
/-!
# Proof I with explicit finite satisfiability

The positive disagreement theory's finite satisfiability is a local axiom
`hf`, not a consequence asserted from truth or overspill. The same `hf`
feeds both non-provability (with preservation) and non-refutability.
Compactness is proved below using mathlib. The existing LambdaSound
framework is retained. Published arithmetic inputs remain explicit:
`IsPi1` and `WitnessReflection`; see AXIOM_PROVENANCE.md.

A local axiom is a theorem parameter, not a universal assertion that every
setting and translation has a satisfiable disagreement theory.
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

/-! ## Published inputs -/

/-- Finite satisfiability of a set of sentences. -/
def FiniteSatisfiable (Γ : Set Sent) : Prop :=
  ∀ Γ₀ : Finset Sent, ↑Γ₀ ⊆ Γ → ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-- First-order compactness [Gödel 1930; Malcev 1936]. -/
def Compactness : Prop :=
  ∀ Γ : Set Sent, FiniteSatisfiable Γ → ∃ M : Model, ∀ φ ∈ Γ, M.Sat φ

/-- Compactness, discharged by mathlib rather than assumed. -/
theorem compactness : Compactness := by
  intro Γ hf
  have hfin : Language.Theory.IsFinitelySatisfiable Γ := by
    intro Γ₀ hsub
    obtain ⟨M, hM⟩ := hf Γ₀ hsub
    letI := M.str
    letI : Nonempty M.carrier := ⟨M.str.funMap zeroFunc Fin.elim0⟩
    letI : Language.Theory.Model M.carrier (↑Γ₀ : L.Theory) := ⟨hM⟩
    exact Language.Theory.Model.isSatisfiable M.carrier
  obtain ⟨M⟩ := Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfin
  refine ⟨⟨M, inferInstance⟩, ?_⟩
  intro φ hφ
  exact Language.Theory.realize_sentence_of_mem Γ hφ

/-- Σ₁ witness reflection (Kreisel): if a Π₁ sentence is false in ℕ,
    there is a standard witness to its failure, so its negation is
    provable.  Contrapositive: non-refutability implies truth.
    [Kreisel 1951; Kaye 1991] -/
def WitnessReflection (S : Setting) : Prop :=
  ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)

/-- Provability preservation for the round trip [Manuscript §1.5–1.7]. -/
def RoundTripPreserves (S : Setting) (τ : TranslationPair) : Prop :=
  ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ)

/-! ## Disagreement theory and the finite-satisfiability axiom -/

/-- The positive disagreement theory: RH holds but its
    round trip fails. -/
def disagreementTheory (S : Setting) (τ : TranslationPair) : Set Sent :=
  S.T ∪ {S.RH} ∪ {neg (τ.RL S.RH)}

/-- The single finite-satisfiability premise for the selected setting
and translation. It is assumed explicitly; no overspill derivation is claimed. -/
def FiniteSatisfiabilityAxiom (S : Setting) (τ : TranslationPair) : Prop :=
  FiniteSatisfiable (disagreementTheory S τ)

abbrev OverspillFiniteSatisfiability := FiniteSatisfiabilityAxiom

/-! ## Disagreement models from compactness -/

/-- Compactness converts finite satisfiability of the positive
    disagreement theory into a model where RH holds but its
    round trip fails. -/
theorem canonical_disagreement (S : Setting) (τ : TranslationPair)
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

/-! ## Reductio arguments from the same finite-satisfiability axiom -/

/-- Non-provability from finite satisfiability and the existing preservation premise. -/
theorem RH_not_provable (S : Setting) (τ : TranslationPair)
    (hf : FiniteSatisfiabilityAxiom S τ)
    (hp : RoundTripPreserves S τ) : ¬ S.Prov S.RH := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := canonical_disagreement S τ compactness hf
  exact hfail (hp S.RH hprov M hM)

/-- Non-refutability uses only positive finite satisfiability: a model
of T + RH cannot also satisfy a consequence ¬RH of T. -/
theorem neg_RH_not_provable (S : Setting) (τ : TranslationPair)
    (hf : FiniteSatisfiabilityAxiom S τ) : ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, hsat, -⟩ := canonical_disagreement S τ compactness hf
  exact ((M.sat_neg S.RH).mp (hprov M hM)) hsat

/-- Non-refutability via an explicit model of ZFC + RH.
    Useful when the model is obtained by other means. -/
theorem neg_RH_not_provable_of_model (S : Setting)
    (hmodel : ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH) :
    ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, hsat⟩ := hmodel
  exact ((M.sat_neg S.RH).mp (hprov M hM)) hsat

/-! ## Independence and truth -/

/-- Independence, retaining the existing theorem-preservation hypothesis. -/
theorem RH_independent (S : Setting) (τ : TranslationPair)
    (hf : FiniteSatisfiabilityAxiom S τ)
    (hp : RoundTripPreserves S τ) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S τ hf hp, neg_RH_not_provable S τ hf⟩

/-- Truth from non-refutability (Theorem 1.18.2).
    Kreisel reflection: a Π₁ sentence that is not refutable in a
    Σ₁-complete theory must be true in ℕ. -/
theorem truth_from_unrefutability (S : Setting)
    (hr : WitnessReflection S) {φ : Sent}
    (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (hr φ hpi hfalse)

/-- Standard truth from the finite-satisfiability axiom and the
published Π₁ / finite-witness inputs. No arithmetic soundness or
round-trip preservation is used in this theorem. -/
theorem RH_true_in_N (S : Setting) (τ : TranslationPair)
    (hpi : IsPi1 S.RH) (hr : WitnessReflection S)
    (hf : FiniteSatisfiabilityAxiom S τ) : TrueInN S.RH :=
  truth_from_unrefutability S hr hpi (neg_RH_not_provable S τ hf)

/-- Truth via model (minimal route, Theorem 1.18.3 variant). -/
theorem RH_true_from_model (S : Setting)
    (hpi : IsPi1 S.RH) (hr : WitnessReflection S)
    (hmodel : ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH) :
    TrueInN S.RH :=
  truth_from_unrefutability S hr hpi (neg_RH_not_provable_of_model S hmodel)

/-! ## Λ-soundness framework

This structure captures the conditions used in the deductive reductio,
not the entire two-language Definition 1.4.3 of the manuscript.
The `changes` field is derived from the disagreement model, which
is obtained from the explicit finite-satisfiability premise (see `changes_rh`).
-/

structure LambdaSound (S : Setting) (φ : Sent) (τ : TranslationPair) : Prop where
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M → M.Sat ψ → M.Sat (τ.RL ψ)
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

/-- The round-trip changes RH: derived from the disagreement model. -/
theorem changes_rh (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : OverspillFiniteSatisfiability S τ) :
    ¬ S.Prov (iffS S.RH (τ.RL S.RH)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := canonical_disagreement S τ hc hf
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

#print axioms RH.Paper.RH_not_provable
#print axioms RH.Paper.neg_RH_not_provable
#print axioms RH.Paper.RH_independent
#print axioms RH.Paper.RH_true_in_N
