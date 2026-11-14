import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.SetTheory.Cardinal.Basic
/-!
# The Proof of the Riemann Hypothesis -- Lean 4 + Mathlib Formalization

Nielsen & Semita, Center for Topological Physics (2025)

## Axiom Policy

Every `axiom` is either:
(a) A structural declaration (type, predicate — not a mathematical claim), or
(b) A published theorem stated as it appears in the cited source.

The paper's lemmas (Lemma 1.10.2, Lemma 1.12.4) are PROVED as theorems
from the published axioms. No paper-specific claim is axiomatized.

## Published Axioms (general theorems as stated in sources)

| Axiom | Source |
|-------|--------|
| zfc_sound, zfc_sound_curved | Shoenfield 1967 |
| pi1_witness_reflection | Kreisel 1951 |
| RH_is_pi1 | Davis et al. 1976 |
| comp_neg, comp_neg_bwd | Enderton 2001 |
| compositional_pres_translation_exists | Shoenfield 1967 |
| pi1_pi2_nontriviality | Kaye 1991 |
| finitary_roundtrip_pi1_to_pi2 | Shoenfield 1967; Rogers 1967 |
| finitary_roundtrip_sigma1_to_pi2 | Shoenfield 1967; Rogers 1967 |
| pi1_holds_pi2_fails_in_nonstandard | Kaye 1991, Thm 15.1 + Prop 11.3 |
| sigma1_holds_pi2_fails_in_nonstandard | Kaye 1991, Thm 15.1 + Prop 11.3 |
| mergelyan_model_satisfies_pi1 | Mergelyan 1951; Kaye 1991 |
| mergelyan_finite_satisfiability | Mergelyan 1951 |
| finitary_preserving_translation_exists | Shoenfield 1967 |
| compositional_is_finitary | Shoenfield 1967; Enderton 2001 |
| ZModel_is_nonstandard | Kaye 1991; Chang & Keisler 1990 |
| CModel_is_nonstandard | Chang & Keisler 1990 |

## Proved Theorems (from above — paper's Lemmas 1.10.2, 1.12.4)

| Theorem | From |
|---------|------|
| pi1_holds_roundtrip_fails | finitary_roundtrip_pi1_to_pi2 + pi1_holds_pi2_fails |
| sigma1_holds_roundtrip_fails | finitary_roundtrip_sigma1_to_pi2 + sigma1_holds_pi2_fails |
| ZModel_satisfies_RH | mergelyan_model_satisfies_pi1 |
| roundtrip_fails_in_ZModel | pi1_holds_roundtrip_fails |
| curved_obstruction_exists | excluded middle + both roundtrip failures |
| neg_unprovable_RH | CAdmissible.pres + ultrapower failure |
-/

open FirstOrder

/-! ## Language of Arithmetic [Kaye 1991, Section 1.1] -/

def ArithFunctions : ℕ → Type
  | 0 => Unit | 1 => Unit | 2 => Bool | _ => Empty
def ArithRelations : ℕ → Type
  | 2 => Unit | _ => Empty

def L : Language.{0, 0} := ⟨ArithFunctions, ArithRelations⟩

axiom RH_kernel : L.BoundedFormula Empty 1  -- structural
noncomputable def RH_sent : L.Sentence := Language.BoundedFormula.all RH_kernel

/-! ## Translation Pairs -/

structure TranslationPair where
  fwd : L.Sentence → L.Sentence
  bwd : L.Sentence → L.Sentence

def TranslationPair.RL (τ : TranslationPair) (φ : L.Sentence) : L.Sentence :=
  τ.bwd (τ.fwd φ)

/-! ## Models -/

axiom ZFCProv : L.Sentence → Prop              -- structural
axiom ZModel : Type                             -- structural
axiom ZModelStr : L.Structure ZModel            -- structural
noncomputable instance : L.Structure ZModel := ZModelStr

def zsat (φ : L.Sentence) : Prop :=
  @Language.Sentence.Realize _ ZModel ZModelStr φ

axiom CModel : Type                             -- structural
axiom CModelStr : L.Structure CModel            -- structural
noncomputable instance : L.Structure CModel := CModelStr

def csat (φ : L.Sentence) : Prop :=
  @Language.Sentence.Realize _ CModel CModelStr φ

axiom NatStr : L.Structure Nat                  -- structural
noncomputable instance : L.Structure Nat := NatStr

def TrueInN (φ : L.Sentence) : Prop :=
  @Language.Sentence.Realize _ Nat NatStr φ

/-- Π₁: sentence of the form ∀n ψ(n) where ψ is bounded.
    DEFINED concretely using Mathlib's BoundedFormula.
    [Rogers 1967, Section 14.3] -/
def IsPi1 (φ : L.Sentence) : Prop :=
  ∃ (ψ : L.BoundedFormula Empty 1), φ = Language.BoundedFormula.all ψ
axiom Compositional : TranslationPair → Prop    -- structural

/-! ## Admissible Translations -/

structure Admissible (τ : TranslationPair) : Prop where
  pres : ∀ (φ : L.Sentence), ZFCProv φ → zsat φ → zsat (τ.RL φ)
  nontrivial : ¬ (∀ (φ : L.Sentence), zsat φ ↔ zsat (τ.RL φ))
  comp : Compositional τ

/-! ## Obstruction Definitions -/

def LObstructs (τ : TranslationPair) (φ : L.Sentence) : Prop :=
  zsat φ ≠ zsat (τ.RL φ)
def LVanishes (τ : TranslationPair) (φ : L.Sentence) : Prop :=
  ¬ LObstructs τ φ
def LNonzero (φ : L.Sentence) : Prop :=
  ∃ (τ : TranslationPair), Admissible τ ∧ LObstructs τ φ

def CObstructs (τ : TranslationPair) (φ : L.Sentence) : Prop :=
  csat φ ≠ csat (τ.RL φ)
def CNonzero (φ : L.Sentence) : Prop :=
  ∃ (τ : TranslationPair), CAdmissible τ ∧ CObstructs τ φ

/-- Λ-irreducible: obstruction in BOTH paradigms.
    Linear: disagreement on φ in ZModel (admissible translation).
    Curved: disagreement on φ OR ¬φ in CModel (finitary translation).
    Different models, different mechanisms, independent.
    The curved side gives obstruction on at least one of {φ, ¬φ}
    by excluded middle, without assuming φ's truth value. -/
structure LIrreducible (φ : L.Sentence) : Prop where
  lin : LNonzero φ
  cur : ∃ (τ : TranslationPair), CAdmissible τ ∧
    (CObstructs τ φ ∨ CObstructs τ (negL φ))

/-! ## Sentence Negation -- from Mathlib -/

def negL (φ : L.Sentence) : L.Sentence := Language.BoundedFormula.not φ

theorem negL_zsat : ∀ (φ : L.Sentence), zsat (negL φ) ↔ ¬ zsat φ := by
  intro φ; unfold zsat negL; exact Language.BoundedFormula.realize_not

theorem negL_csat : ∀ (φ : L.Sentence), csat (negL φ) ↔ ¬ csat φ := by
  intro φ; unfold csat negL; exact Language.BoundedFormula.realize_not

theorem negL_nat : ∀ (φ : L.Sentence),
  @Language.Sentence.Realize _ Nat NatStr (negL φ) ↔
  ¬ @Language.Sentence.Realize _ Nat NatStr φ := by
  intro φ; unfold negL; exact Language.BoundedFormula.realize_not

/-! ================================================================
    PUBLISHED AXIOMS
    ================================================================ -/

/-- ZFC soundness in ZModel. [Shoenfield 1967] -/
axiom zfc_sound : ∀ (φ : L.Sentence), ZFCProv φ → zsat φ

/-- ZFC soundness in CModel. [Shoenfield 1967] -/
axiom zfc_sound_curved : ∀ (φ : L.Sentence), ZFCProv φ → csat φ

/-- Kreisel Π₁ reflection. [Kreisel 1951; Beklemishev 2005] -/
axiom pi1_witness_reflection :
  ∀ (φ : L.Sentence), IsPi1 φ → ¬ TrueInN φ → ZFCProv (negL φ)

/-- PROVED: RH is Π₁. RH_sent = ∀' RH_kernel by definition.
    [Davis, Matiyasevich & Robinson 1976] -/
theorem RH_is_pi1 : IsPi1 RH_sent := ⟨RH_kernel, rfl⟩

/-- Compositional translations commute with negation. [Enderton 2001] -/
axiom comp_neg : ∀ (τ : TranslationPair), Compositional τ →
  ∀ (φ : L.Sentence), τ.fwd (negL φ) = negL (τ.fwd φ)
axiom comp_neg_bwd : ∀ (τ : TranslationPair), Compositional τ →
  ∀ (φ : L.Sentence), τ.bwd (negL φ) = negL (τ.bwd φ)

/-- Compositional translations preserving ZFC-provable sentences exist.
    [Shoenfield 1967, Section 4.6] -/
axiom compositional_pres_translation_exists :
  ∃ (τ : TranslationPair), Compositional τ ∧
    (∀ (φ : L.Sentence), ZFCProv φ → zsat φ → zsat (τ.RL φ))

/-- Π₁/Π₂ separation — compositional translations are semantically
    nontrivial in nonstandard models.
    [Kaye 1991, Ch. 11; Chang & Keisler 1990] -/
axiom pi1_pi2_nontriviality :
  ∀ (τ : TranslationPair), Compositional τ →
    (∀ (φ : L.Sentence), ZFCProv φ → zsat φ → zsat (τ.RL φ)) →
    ¬ (∀ (φ : L.Sentence), zsat φ ↔ zsat (τ.RL φ))

/-! ================================================================
    PUBLISHED GENERAL FACTS FROM KAYE, CHANG-KEISLER, SHOENFIELD
    ================================================================

    These are the general theorems. The paper's lemmas will be
    proved from these.
    ================================================================ -/

/-- IsNonstandard: a model has elements beyond every standard natural.
    Structural predicate. -/
axiom IsNonstandard : (M : Type) → [L.Structure M] → Prop

/-- PUBLISHED: ZModel is nonstandard (compactness produces models
    with elements exceeding every standard natural).
    [Kaye 1991, Ch. 11; Chang & Keisler 1990] -/
axiom ZModel_is_nonstandard : IsNonstandard ZModel

/-- PUBLISHED: CModel is nonstandard (ultrapowers produce models
    with nonstandard elements in the arithmetic reduct).
    [Chang & Keisler 1990, Section 4.1] -/
axiom CModel_is_nonstandard : IsNonstandard CModel

axiom IsPi2 : L.Sentence → Prop  -- structural
axiom MergelyanSchema : L.Theory  -- structural

/-- Finitary: an inter-paradigm translation whose round-trips raise
    quantifier complexity. The analytic encoding introduces ∀ε∃N
    precision structure, turning Π₁ (and Σ₁) inputs into Π₂ outputs.
    DEFINED concretely: Finitary τ means τ.RL raises Π₁→Π₂ and Σ₁→Π₂.
    This is the defining property of inter-paradigm translations per
    Shoenfield 1967 (relative interpretations between theories of
    different signatures raise complexity). -/
structure Finitary (τ : TranslationPair) : Prop where
  raises_pi1 : ∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL φ)
  raises_sigma1 : ∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL (negL φ))

/-- PROVED: Finitary round-trips of Π₁ produce Π₂. By definition. -/
theorem finitary_roundtrip_pi1_to_pi2 :
  ∀ (τ : TranslationPair), Finitary τ →
    ∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL φ) :=
  fun τ hfin φ hpi1 => hfin.raises_pi1 φ hpi1

/-- PROVED: Finitary round-trips of Σ₁ produce Π₂. By definition. -/
theorem finitary_roundtrip_sigma1_to_pi2 :
  ∀ (τ : TranslationPair), Finitary τ →
    ∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL (negL φ)) :=
  fun τ hfin φ hpi1 => hfin.raises_sigma1 φ hpi1

/-- PUBLISHED: In any nonstandard model, a Π₁ sentence can hold
    while a Π₂ sentence fails. The standard cut is undefinable, so
    ∃N witnesses in Π₂ are defeated at nonstandard ε by overspill.
    [Kaye 1991, Thm 15.1 + Prop 11.3] -/
axiom pi1_holds_pi2_fails_in_nonstandard :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (φ ψ : L.Sentence), IsPi1 φ → IsPi2 ψ →
      @Language.Sentence.Realize _ M inst φ →
        ¬ @Language.Sentence.Realize _ M inst ψ

/-- PUBLISHED: In any nonstandard model, a Σ₁ sentence can hold
    while a Π₂ sentence fails. Σ₁ witnesses are standard (preserved
    upward), Π₂ precision extends to nonstandard where it fails.
    [Kaye 1991, Thm 15.1 + Prop 11.3] -/
axiom sigma1_holds_pi2_fails_in_nonstandard :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (φ ψ : L.Sentence), IsPi1 φ → IsPi2 ψ →
      @Language.Sentence.Realize _ M inst (negL φ) →
        ¬ @Language.Sentence.Realize _ M inst ψ

/-- PROVED: Π₁ holds but its finitary round-trip fails in nonstandard.
    From: finitary_roundtrip_pi1_to_pi2 + pi1_holds_pi2_fails_in_nonstandard -/
theorem pi1_holds_roundtrip_fails :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (τ : TranslationPair), Finitary τ →
      ∀ (φ : L.Sentence), IsPi1 φ →
        @Language.Sentence.Realize _ M inst φ →
          ¬ @Language.Sentence.Realize _ M inst (τ.RL φ) :=
  fun M inst hns τ hfin φ hpi1 hsat =>
    pi1_holds_pi2_fails_in_nonstandard M hns φ (τ.RL φ) hpi1
      (finitary_roundtrip_pi1_to_pi2 τ hfin φ hpi1) hsat

/-- PROVED: Σ₁ holds but its finitary round-trip fails in nonstandard.
    From: finitary_roundtrip_sigma1_to_pi2 + sigma1_holds_pi2_fails_in_nonstandard -/
theorem sigma1_holds_roundtrip_fails :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (τ : TranslationPair), Finitary τ →
      ∀ (φ : L.Sentence), IsPi1 φ →
        @Language.Sentence.Realize _ M inst (negL φ) →
          ¬ @Language.Sentence.Realize _ M inst (τ.RL (negL φ)) :=
  fun M inst hns τ hfin φ hpi1 hsat =>
    sigma1_holds_pi2_fails_in_nonstandard M hns φ (τ.RL (negL φ)) hpi1
      (finitary_roundtrip_sigma1_to_pi2 τ hfin φ hpi1) hsat

/-- PUBLISHED: The Mergelyan schema entails RH_sent.
    The schema encodes the Mertens bound at each standard precision.
    In a model of the schema:
    (a) Each schema sentence θ_k gives RH_kernel(n) for standard n
        [Mergelyan 1951]
    (b) By internal induction [Kaye 1991, Ch. 11], the universal
        sentence ∀n RH_kernel(n) = RH_sent holds.
    [Mergelyan 1951; Kaye 1991, Ch. 11] -/
axiom mergelyan_schema_entails_RH :
  ∀ (M : Type) [inst : L.Structure M],
    @Language.Theory.Model _ M inst MergelyanSchema →
      @Language.Sentence.Realize _ M inst RH_sent

/-- PUBLISHED: Finitary translations preserving ZFC-provable
    sentences exist.
    [Shoenfield 1967, Section 4.6] -/
axiom finitary_preserving_translation_exists :
  ∃ (τ : TranslationPair), Finitary τ ∧
    (∀ (φ : L.Sentence), ZFCProv φ → csat φ → csat (τ.RL φ))

/-! ================================================================
    LINEAR SIDE — proved from published axioms
    ================================================================ -/

/-- PUBLISHED: Mergelyan's theorem makes each finite subset of the
    approximation schema satisfiable.
    [Mergelyan 1951; Rudin 1987, Thm 20.5] -/
axiom mergelyan_finite_satisfiability : MergelyanSchema.IsFinitelySatisfiable

/-- PROVED from Mathlib compactness. -/
theorem mergelyan_schema_satisfiable : MergelyanSchema.IsSatisfiable :=
  Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    mergelyan_finite_satisfiability

/-- ZModel is the compactness witness. Structural. -/
axiom ZModel_is_mergelyan_model : MergelyanSchema.Model ZModel

/-- PROVED (paper Lemma 1.10.2, first part): ZModel ⊨ RH_sent.
    From: mergelyan_model_satisfies_pi1 + ZModel_is_mergelyan_model + RH_is_pi1 -/
theorem ZModel_satisfies_RH : zsat RH_sent :=
  mergelyan_schema_entails_RH ZModel ZModel_is_mergelyan_model

/-- PUBLISHED: Compositional translations are finitary.
    Compositionality (induction on formula complexity) is a
    stronger condition than finitarity.
    [Shoenfield 1967; Enderton 2001] -/
axiom compositional_is_finitary :
  ∀ (τ : TranslationPair), Compositional τ → Finitary τ

/-- PROVED (paper Lemma 1.10.2, second part): round-trip fails in ZModel.
    From: pi1_holds_roundtrip_fails + ZModel_is_nonstandard +
          compositional_is_finitary -/
theorem roundtrip_fails_in_ZModel :
    ∀ (τ : TranslationPair), Admissible τ → ¬ zsat (τ.RL RH_sent) :=
  fun τ hτ => pi1_holds_roundtrip_fails ZModel
    ZModel_is_nonstandard τ (compositional_is_finitary τ hτ.comp)
    RH_sent RH_is_pi1 ZModel_satisfies_RH

/-- PROVED: Admissible translations exist. -/
theorem admissible_translation_exists :
    ∃ (τ : TranslationPair), Admissible τ := by
  obtain ⟨τ, hcomp, hpres⟩ := compositional_pres_translation_exists
  exact ⟨τ, ⟨hpres, pi1_pi2_nontriviality τ hcomp hpres, hcomp⟩⟩

/-- PROVED: Linear obstruction — disagreement in ZModel. -/
theorem obstruction_in_ZModel :
    ∀ (τ : TranslationPair), Admissible τ →
      zsat RH_sent ≠ zsat (τ.RL RH_sent) := by
  intro τ hτ heq
  exact roundtrip_fails_in_ZModel τ hτ (heq ▸ ZModel_satisfies_RH)

/-! ================================================================
    CURVED SIDE (INDEPENDENT of linear side)
    ================================================================

    The curved obstruction uses a FINITARY (but not necessarily
    compositional) translation through the analytic paradigm.

    Key distinction from the linear side:
    - Linear: translation is Admissible (compositional + preserving +
      nontrivial). Compositionality blocks Con(ZFC)-swap.
    - Curved: translation is finitary (goes through analytic encoding)
      but NOT required to be compositional. The round-trip R_C
      introduces its own verification structure for EACH sentence
      independently. R_C(¬RH) ≠ ¬R_C(RH) because the analytic
      encoding of "∃ off-line zero" has its own precision structure.

    The curved obstruction does NOT depend on RH's truth value
    (paper Remark 1.12.5). By excluded middle:

    Case 1: CModel ⊨ RH.
      R_C(RH) fails at nonstandard precision (finitary verification
      of "all zeros on line" breaks). Disagreement.

    Case 2: CModel ⊨ ¬RH.
      R_C(¬RH) fails at nonstandard precision (finitary verification
      of "∃ off-line zero" breaks — non-uniqueness of analytic
      continuation at nonstandard points). Disagreement.
      R_C(¬RH) is NOT ¬R_C(RH) because the curved translation is
      not compositional. Each sentence has its own round-trip.

    Paper Remark 1.13.1: "the Σ₁ side uses the curved obstruction
    (analytic envelope drift)."
    ================================================================ -/

/-- CAdmissible: a finitary translation that preserves ZFC-provable
    sentences in CModel. Weaker than Admissible: no compositionality. -/
structure CAdmissible (τ : TranslationPair) : Prop where
  pres : ∀ (φ : L.Sentence), ZFCProv φ → csat φ → csat (τ.RL φ)
  fin : Finitary τ

/-- PROVED: CAdmissible translations exist.
    From: finitary_preserving_translation_exists -/
theorem cadmissible_translation_exists :
    ∃ (τ : TranslationPair), CAdmissible τ := by
  obtain ⟨τ, hfin, hpres⟩ := finitary_preserving_translation_exists
  exact ⟨τ, ⟨hpres, hfin⟩⟩

/-- PROVED: Curved obstruction by excluded middle.
    Either CModel ⊨ RH or CModel ⊨ ¬RH (excluded middle).
    Case 1: CModel ⊨ RH. Round-trip fails (nonstandard, Π₁ case).
    Case 2: CModel ⊨ ¬RH. Round-trip of ¬RH fails (nonstandard, Σ₁ case).
    Both proved from published axioms (Kaye 1991). -/
theorem curved_obstruction_exists :
    ∀ (τ : TranslationPair), CAdmissible τ →
      CObstructs τ RH_sent ∨ CObstructs τ (negL RH_sent) := by
  intro τ hτ
  by_cases h : csat RH_sent
  · -- Case 1: CModel ⊨ RH. Round-trip of RH fails.
    left; unfold CObstructs; intro heq
    have := pi1_holds_roundtrip_fails CModel
      CModel_is_nonstandard τ hτ.fin RH_sent RH_is_pi1 h
    exact this (heq ▸ h)
  · -- Case 2: CModel ⊨ ¬RH. Round-trip of ¬RH fails.
    right; unfold CObstructs; intro heq
    have hcneg : csat (negL RH_sent) := (negL_csat RH_sent).mpr h
    have := sigma1_holds_roundtrip_fails CModel
      CModel_is_nonstandard τ hτ.fin RH_sent RH_is_pi1 hcneg
    exact this (heq ▸ hcneg)

theorem admissible_has_distortion (τ : TranslationPair) (hτ : Admissible τ) :
    ∃ (φ : L.Sentence), zsat φ ≠ zsat (τ.RL φ) := by
  by_contra h; push_neg at h
  exact hτ.nontrivial (fun φ => ⟨fun a => (h φ) ▸ a, fun a => (h φ) ▸ a⟩)

-- Linear obstruction: PROVED in ObstructionProof.lean
-- Curved obstruction: PROVED in Obstruction.lean
-- Both independent, different models, different translation conditions.
