import RH.Paper.Arith
import Mathlib.ModelTheory.Satisfiability
/-!
# Proof I: semantic obstruction and the finite-satisfiability obligation

Λ is a set of models on which a sentence and its specified round trip disagree.
It is not defined from the truth value of RH in ℕ. Soundness and obstruction
are separate conditions: nonzero obstruction is never a field of LambdaSound.

The reductios below assume a single, two-direction FiniteSatisfiabilityObligation.
Applying that assumption inside a reductio does not prove the assumption.
Compactness is proved from Mathlib. Uniformity separation can supply finite
satisfiability, but separation for the concrete RH reconstruction remains open
in this formalization. Quantifier shape alone is not a proof of separation.

Setting.T, Setting.RH and the translation maps are parameters. No theorem here
instantiates them as ZFC, arithmetic RH, or Mathlib's RiemannHypothesis.
See AXIOM_PROVENANCE.md for the complete list of explicit inputs.
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
  nonempty : Nonempty carrier

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
  /-- An explicit model-existence assumption on the chosen theory. -/
  consistent : ∃ M : Model, ∀ φ ∈ T, M.Sat φ

def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ
/-- Semantic consequence in the chosen arithmetic theory, not a syntactic ZFC calculus. -/
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ


/-! ## Semantic profiles and Λ -/

/-- The extension of a sentence over the fixed class of models of T. -/
def SemanticProfile (S : Setting) (φ : Sent) : Set Model :=
  {M | S.ZFCModel M ∧ M.Sat φ}

/-- The semantic discrepancy set. No evaluation of RH in ℕ enters this definition. -/
def LambdaObstruction (S : Setting) (τ : TranslationPair) (φ : Sent) : Set Model :=
  {M | S.ZFCModel M ∧ ¬ (M.Sat φ ↔ M.Sat (τ.RL φ))}

def LambdaZero (S : Setting) (τ : TranslationPair) (φ : Sent) : Prop :=
  ∀ M, S.ZFCModel M → (M.Sat φ ↔ M.Sat (τ.RL φ))

theorem lambdaZero_iff_profiles (S : Setting) (τ : TranslationPair) (φ : Sent) :
    LambdaZero S τ φ ↔ SemanticProfile S φ = SemanticProfile S (τ.RL φ) := by
  constructor
  · intro h
    ext M
    exact and_congr_right fun hM => h M hM
  · intro h M hM
    have he := Set.ext_iff.mp h M
    exact ⟨fun hφ => (he.mp ⟨hM, hφ⟩).2,
      fun hφ => (he.mpr ⟨hM, hφ⟩).2⟩

theorem lambdaZero_iff_empty (S : Setting) (τ : TranslationPair) (φ : Sent) :
    LambdaZero S τ φ ↔ LambdaObstruction S τ φ = ∅ := by
  classical
  simp only [LambdaZero, LambdaObstruction, Set.eq_empty_iff_forall_not_mem,
    Set.mem_setOf_eq, not_and, not_not]

/-- Preservation of consequences; it does not assume preservation of every
sentence at every individual model. That stronger condition would force Λ=0. -/
def RoundTripPreserves (S : Setting) (τ : TranslationPair) : Prop :=
  ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ)

/-- Conditions used by the deductive core. Obstruction is a separate hypothesis.
The full concrete two-language interpretation remains to be implemented. -/
structure LambdaSound (S : Setting) (τ : TranslationPair) : Prop where
  preserves : RoundTripPreserves S τ
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))

theorem uniform_preservation {S : Setting} {τ : TranslationPair}
    (hp : RoundTripPreserves S τ) {φ : Sent} (hφ : S.Prov φ) :
    LambdaZero S τ φ :=
  fun M hM => ⟨fun _ => hp φ hφ M hM, fun _ => hφ M hM⟩

theorem round_trip_adequacy {S : Setting} {τ : TranslationPair}
    (hp : RoundTripPreserves S τ) {φ : Sent} (hφ : S.Prov φ) :
    S.Prov (iffS φ (τ.RL φ)) :=
  fun M hM => (M.sat_iff φ (τ.RL φ)).mpr (uniform_preservation hp hφ M hM)

/-! ## Compactness from Mathlib -/

def FiniteSatisfiable (Γ : Set Sent) : Prop :=
  ∀ Γ₀ : Finset Sent, ↑Γ₀ ⊆ Γ → ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

def Compactness : Prop :=
  ∀ Γ : Set Sent, FiniteSatisfiable Γ → ∃ M : Model, ∀ φ ∈ Γ, M.Sat φ

/-- Standard first-order compactness, discharged by the pinned Mathlib theorem. -/
theorem firstOrderCompactness : Compactness := by
  intro Γ hf
  have hfin : Language.Theory.IsFinitelySatisfiable (Γ : L.Theory) := by
    intro Γ₀ hΓ₀
    obtain ⟨M, hM⟩ := hf Γ₀ hΓ₀
    letI : L.Structure M.carrier := M.str
    letI : Nonempty M.carrier := M.nonempty
    letI : Language.Theory.Model M.carrier (↑Γ₀ : L.Theory) :=
      ⟨fun φ hφ => hM φ hφ⟩
    exact Language.Theory.Model.isSatisfiable M.carrier
  have hsat := Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfin
  let N := hsat.some
  refine ⟨⟨N, inferInstance, inferInstance⟩, ?_⟩
  intro φ hφ
  exact Language.Theory.realize_sentence_of_mem Γ hφ

/-! ## One finite-satisfiability obligation, with both reductio directions -/

def disagreementTheoryFor (S : Setting) (τ : TranslationPair) (φ : Sent) : Set Sent :=
  S.T ∪ {φ} ∪ {neg (τ.RL φ)}

def disagreementTheory (S : Setting) (τ : TranslationPair) : Set Sent :=
  disagreementTheoryFor S τ S.RH

def negDisagreementTheory (S : Setting) (τ : TranslationPair) : Set Sent :=
  disagreementTheoryFor S τ (neg S.RH)

/-- The RH-specific assumption. This is an explicit theorem parameter, not a
universal axiom for arbitrary settings or translation maps. Neither direction
is attributed to overspill or to a published reverse-mathematics theorem. -/
structure FiniteSatisfiabilityObligation (S : Setting) (τ : TranslationPair) : Prop where
  positive : S.Prov S.RH → FiniteSatisfiable (disagreementTheory S τ)
  negative : S.Prov (neg S.RH) → FiniteSatisfiable (negDisagreementTheory S τ)

/-- Separation must use the SAME background theory and reconstruction as the
reductio. A separation theorem over IΣ₁ alone does not supply this input. -/
def UniformitySeparation (S : Setting) (τ : TranslationPair) (φ : Sent) : Prop :=
  ¬ ∀ M, S.ZFCModel M → M.Sat φ → M.Sat (τ.RL φ)

/-- A genuine separation result supplies a model and hence every finite fragment. -/
theorem finiteSatisfiable_of_uniformitySeparation (S : Setting)
    (τ : TranslationPair) (φ : Sent) (hsep : UniformitySeparation S τ φ) :
    FiniteSatisfiable (disagreementTheoryFor S τ φ) := by
  classical
  obtain ⟨M, hM, hφ, hfail⟩ : ∃ M, S.ZFCModel M ∧ M.Sat φ ∧ ¬ M.Sat (τ.RL φ) := by
    simpa only [UniformitySeparation, not_forall, exists_prop] using hsep
  intro Γ₀ hΓ₀
  refine ⟨M, ?_⟩
  intro ψ hψ
  rcases hΓ₀ hψ with (hT | hs) | hn
  · exact hM ψ hT
  · simpa only [Set.mem_singleton_iff.mp hs] using hφ
  · simpa only [Set.mem_singleton_iff.mp hn] using (M.sat_neg (τ.RL φ)).mpr hfail

/-- The proposed separation route, with its two actual premises visible. -/
theorem finiteSatisfiabilityObligation_of_separation (S : Setting) (τ : TranslationPair)
    (hpos : S.Prov S.RH → UniformitySeparation S τ S.RH)
    (hneg : S.Prov (neg S.RH) → UniformitySeparation S τ (neg S.RH)) :
    FiniteSatisfiabilityObligation S τ where
  positive h := finiteSatisfiable_of_uniformitySeparation S τ S.RH (hpos h)
  negative h := finiteSatisfiable_of_uniformitySeparation S τ (neg S.RH) (hneg h)

/-! ## Disagreement models and the reductios -/

theorem canonical_disagreement_for (S : Setting) (τ : TranslationPair) (φ : Sent)
    (hf : FiniteSatisfiable (disagreementTheoryFor S τ φ)) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat φ ∧ ¬ M.Sat (τ.RL φ) := by
  obtain ⟨M, hM⟩ := firstOrderCompactness (disagreementTheoryFor S τ φ) hf
  refine ⟨M, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact hM ψ (Set.mem_union_left _ (Set.mem_union_left _ hψ))
  · exact hM φ (Set.mem_union_left _ (Set.mem_union_right _ rfl))
  · exact (M.sat_neg (τ.RL φ)).mp (hM _ (Set.mem_union_right _ rfl))

theorem canonical_disagreement (S : Setting) (τ : TranslationPair)
    (hf : FiniteSatisfiable (disagreementTheory S τ)) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH ∧ ¬ M.Sat (τ.RL S.RH) :=
  canonical_disagreement_for S τ S.RH hf

theorem neg_canonical_disagreement (S : Setting) (τ : TranslationPair)
    (hf : FiniteSatisfiable (negDisagreementTheory S τ)) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat (neg S.RH) ∧ ¬ M.Sat (τ.RL (neg S.RH)) :=
  canonical_disagreement_for S τ (neg S.RH) hf

theorem obstruction_nonempty (S : Setting) (τ : TranslationPair) (φ : Sent)
    (hf : FiniteSatisfiable (disagreementTheoryFor S τ φ)) :
    (LambdaObstruction S τ φ).Nonempty := by
  obtain ⟨M, hM, hφ, hfail⟩ := canonical_disagreement_for S τ φ hf
  exact ⟨M, hM, fun h => hfail (h.mp hφ)⟩

theorem not_provable_of_obstruction (S : Setting) (τ : TranslationPair) (φ : Sent)
    (hp : RoundTripPreserves S τ) (hΛ : (LambdaObstruction S τ φ).Nonempty) :
    ¬ S.Prov φ := by
  intro hprov
  obtain ⟨M, hM, hfail⟩ := hΛ
  exact hfail (uniform_preservation hp hprov M hM)

theorem RH_not_provable (S : Setting) (τ : TranslationPair)
    (hfs : FiniteSatisfiabilityObligation S τ) (hp : RoundTripPreserves S τ) :
    ¬ S.Prov S.RH := by
  intro hprov
  exact not_provable_of_obstruction S τ S.RH hp
    (obstruction_nonempty S τ S.RH (hfs.positive hprov)) hprov

theorem neg_RH_not_provable (S : Setting) (τ : TranslationPair)
    (hfs : FiniteSatisfiabilityObligation S τ) (hp : RoundTripPreserves S τ) :
    ¬ S.Prov (neg S.RH) := by
  intro hprov
  exact not_provable_of_obstruction S τ (neg S.RH) hp
    (obstruction_nonempty S τ (neg S.RH) (hfs.negative hprov)) hprov

theorem RH_independent (S : Setting) (τ : TranslationPair)
    (hfs : FiniteSatisfiabilityObligation S τ) (hp : RoundTripPreserves S τ) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S τ hfs hp, neg_RH_not_provable S τ hfs hp⟩

/-- Σ₁ completeness / witness reflection, supplied for the chosen theory.
It is not a theorem for arbitrary Setting.T. -/
def WitnessReflection (S : Setting) : Prop :=
  ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)

theorem truth_from_unrefutability (S : Setting)
    (hr : WitnessReflection S) {φ : Sent}
    (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (hr φ hpi hfalse)

theorem RH_true_in_N (S : Setting) (τ : TranslationPair)
    (hpi : IsPi1 S.RH) (hr : WitnessReflection S)
    (hfs : FiniteSatisfiabilityObligation S τ) (hp : RoundTripPreserves S τ) :
    TrueInN S.RH :=
  truth_from_unrefutability S hr hpi (neg_RH_not_provable S τ hfs hp)

/-! ## Boundary checks: the hypotheses cannot silently assume disagreement -/

/-- Identity reconstruction has no semantic obstruction. -/
theorem identity_lambda_zero (S : Setting) (φ : Sent) :
    LambdaZero S ⟨id, id⟩ φ := fun _ _ => Iff.rfl

/-- Full pointwise forward preservation plus Boolean negation preservation
would force zero obstruction, even for sentences not provable in T. -/
theorem pointwise_preservation_forces_zero (S : Setting) (τ : TranslationPair)
    (hpoint : ∀ M, S.ZFCModel M → ∀ φ, M.Sat φ → M.Sat (τ.RL φ))
    (hneg : ∀ φ, τ.RL (neg φ) = neg (τ.RL φ)) (φ : Sent) :
    LambdaZero S τ φ := by
  intro M hM
  refine ⟨hpoint M hM φ, ?_⟩
  intro hround
  by_contra hφ
  have hn := hpoint M hM (neg φ) ((M.sat_neg φ).mpr hφ)
  rw [hneg φ] at hn
  exact (M.sat_neg (τ.RL φ)).mp hn hround

end RH.Paper

#print axioms RH.Paper.firstOrderCompactness
#print axioms RH.Paper.RH_not_provable
#print axioms RH.Paper.neg_RH_not_provable
#print axioms RH.Paper.RH_independent
#print axioms RH.Paper.RH_true_in_N
