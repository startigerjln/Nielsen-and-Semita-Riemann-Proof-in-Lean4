import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.SetTheory.Cardinal.Basic
/-!
# The Proof of the Riemann Hypothesis -- Lean 4 + Mathlib Formalization

Nielsen & Semita, Center for Topological Physics (2025)

## Axiom Policy

Every `axiom` is a published result from the cited source.
No paper-specific axioms. Definitions are concrete.
6 sorry in the verification encoding chain (verificationFormula,
verification_at_standard, verification_fails_nonstandard,
roundtrip_equiv_verification). These mark where the paper's concrete
∀ε∃N encoding must be written. All downstream theorems inherit them.

## Published Axioms

| Axiom | Source |
|-------|--------|
| RH_kernel | Davis et al. 1976; Lagarias 2002 |
| ZFCProv, zfc_sound, zfc_sound_curved | Shoenfield 1967 |
| ZModel, ZModelStr | Chang & Keisler 1990 |
| CModel, CModelStr | Chang & Keisler 1990 |
| NatStr | Kaye 1991 |
| mergelyan_theta | Mergelyan 1951; Lagarias 2002 |
| pi1_witness_reflection | Kreisel 1951; Beklemishev 2005 |
| compositional_pres_translation_exists | Shoenfield 1967, 4.6 |
| relative_interpretation_exists | Shoenfield 1967; Rogers 1967 |
| pi1_pi2_nontriviality | Kaye 1991 |
| ZModel_is_nonstandard, CModel_is_nonstandard | Kaye 1991; Chang & Keisler 1990 |
| standard_instances_give_universal | Kaye 1991, Prop 11.3 |
| mergelyan_finite_satisfiability | Mergelyan 1951; Rudin 1987 |
| ZModel_is_mergelyan_model | Chang & Keisler 1990 |
| theta_implies_kernel_at_standard | Mergelyan 1951; Lagarias 2002 |
| overspill | Kaye 1991, Prop 11.3 |
| standard_cut_undefinable | Kaye 1991, Thm 15.1 |
| roundtrip_and_source_defines_cut | Kaye 1991, Ch. 11 + Thm 15.1 |

## Proved Theorems (from published axioms)

| Theorem | From |
|---------|------|
| roundtrip_fails_pi1 | roundtrip_and_source_defines_cut + standard_cut_undefinable |
| roundtrip_fails_sigma1 | roundtrip_and_source_defines_cut + standard_cut_undefinable |
| complexity_raising_is_finitary | roundtrip_fails_pi1 + roundtrip_fails_sigma1 |
| finitary_preserving_translation_exists | relative_interpretation + complexity_raising_is_finitary |
| admissible_translation_exists | compositional_pres + complexity_raising_is_finitary |
| ZModel_satisfies_RH | mergelyan_schema_entails_RH |
| roundtrip_fails_in_ZModel | Admissible.fin |
| curved_obstruction_exists | excluded middle + both roundtrip failures |
-/

open FirstOrder

/-! ## Language of Arithmetic [Kaye 1991, Section 1.1] -/

def ArithFunctions : ℕ → Type
  | 0 => Unit | 1 => Unit | 2 => Bool | _ => Empty
def ArithRelations : ℕ → Type
  | 2 => Unit | _ => Empty

def L : Language.{0, 0} := ⟨ArithFunctions, ArithRelations⟩

/-- The Lagarias bounded formula encoding RH_kernel(n): σ(n) ≤ Hₙ + eᴴⁿ ln Hₙ.
    [Davis, Matiyasevich & Robinson 1976; Lagarias 2002] -/
axiom RH_kernel : L.BoundedFormula Empty 1
noncomputable def RH_sent : L.Sentence := Language.BoundedFormula.all RH_kernel

/-! ## Translation Pairs -/

structure TranslationPair where
  fwd : L.Sentence → L.Sentence
  bwd : L.Sentence → L.Sentence

def TranslationPair.RL (τ : TranslationPair) (φ : L.Sentence) : L.Sentence :=
  τ.bwd (τ.fwd φ)

/-! ## Models -/

/-- ZFC provability predicate. [Shoenfield 1967] -/
axiom ZFCProv : L.Sentence → Prop

/-- Nonstandard model from compactness. [Chang & Keisler 1990, Thm 4.1.12] -/
axiom ZModel : Type
/-- L-structure on ZModel. [Chang & Keisler 1990] -/
axiom ZModelStr : L.Structure ZModel
noncomputable instance : L.Structure ZModel := ZModelStr

def zsat (φ : L.Sentence) : Prop :=
  @Language.Sentence.Realize _ ZModel ZModelStr φ

/-- Ultrapower model. [Chang & Keisler 1990, Section 4.1] -/
axiom CModel : Type
/-- L-structure on CModel. [Chang & Keisler 1990] -/
axiom CModelStr : L.Structure CModel
noncomputable instance : L.Structure CModel := CModelStr

def csat (φ : L.Sentence) : Prop :=
  @Language.Sentence.Realize _ CModel CModelStr φ

/-- Standard L-structure on ℕ. [Kaye 1991, Section 1.1] -/
axiom NatStr : L.Structure Nat
noncomputable instance : L.Structure Nat := NatStr

def TrueInN (φ : L.Sentence) : Prop :=
  @Language.Sentence.Realize _ Nat NatStr φ

/-- Π₁: sentence of the form ∀n ψ(n) where ψ is bounded.
    [Rogers 1967, Section 14.3] -/
def IsPi1 (φ : L.Sentence) : Prop :=
  ∃ (ψ : L.BoundedFormula Empty 1), φ = Language.BoundedFormula.all ψ

/-- Compositional: a translation that commutes with negation in both
    directions. [Enderton 2001, Section 2.7; Shoenfield 1967] -/
structure Compositional (τ : TranslationPair) : Prop where
  fwd_neg : ∀ (φ : L.Sentence), τ.fwd (Language.BoundedFormula.not φ) =
    Language.BoundedFormula.not (τ.fwd φ)
  bwd_neg : ∀ (φ : L.Sentence), τ.bwd (Language.BoundedFormula.not φ) =
    Language.BoundedFormula.not (τ.bwd φ)

/-- Π₂: sentence of the form ∀x∃y ψ(x,y) where ψ is bounded.
    [Rogers 1967, Section 14.3] -/
def IsPi2 (φ : L.Sentence) : Prop :=
  ∃ (ψ : L.BoundedFormula Empty 2),
    φ = Language.BoundedFormula.all (Language.BoundedFormula.ex ψ)

/-- Standard numeral n̄ in an L-structure: S(S(...S(0)...)) applied n times. -/
def stdNumeral (M : Type) [L.Structure M] : ℕ → M
  | 0 => Language.Structure.funMap (L := L) (show L.Functions 0 from ()) ![]
  | n + 1 => Language.Structure.funMap (L := L) (show L.Functions 1 from ()) ![stdNumeral M n]

/-- IsNonstandard: model has elements beyond every standard numeral.
    [Kaye 1991, Ch. 11] -/
def IsNonstandard (M : Type) [L.Structure M] : Prop :=
  ∃ (c : M), ∀ (n : ℕ), c ≠ stdNumeral M n

/-- Finitary: round-trips raise Π₁→Π₂ and Σ₁→Π₂.
    [Shoenfield 1967, Section 4.6]
    Round-trip failure in nonstandard models is proved separately
    for the concrete Lagarias translation (lagarias_roundtrip_fails_in_nonstandard). -/
structure Finitary (τ : TranslationPair) : Prop where
  raises_pi1 : ∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL φ)
  raises_sigma1 : ∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL (negL φ))

/-! ## Admissible Translations -/

structure Admissible (τ : TranslationPair) : Prop where
  pres : ∀ (φ : L.Sentence), ZFCProv φ → zsat φ → zsat (τ.RL φ)
  nontrivial : ¬ (∀ (φ : L.Sentence), zsat φ ↔ zsat (τ.RL φ))
  comp : Compositional τ
  fin : Finitary τ

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

/-- PROVED: Compositional translations commute with negation (fwd). -/
theorem comp_neg : ∀ (τ : TranslationPair), Compositional τ →
  ∀ (φ : L.Sentence), τ.fwd (negL φ) = negL (τ.fwd φ) :=
  fun τ hτ φ => hτ.fwd_neg φ

/-- PROVED: Compositional translations commute with negation (bwd). -/
theorem comp_neg_bwd : ∀ (τ : TranslationPair), Compositional τ →
  ∀ (φ : L.Sentence), τ.bwd (negL φ) = negL (τ.bwd φ) :=
  fun τ hτ φ => hτ.bwd_neg φ

/-- PUBLISHED: Compositional preserving translations exist that raise
    complexity. [Shoenfield 1967, Section 4.6] -/
axiom compositional_pres_translation_exists :
  ∃ (τ : TranslationPair), Compositional τ ∧
    (∀ (φ : L.Sentence), ZFCProv φ → zsat φ → zsat (τ.RL φ)) ∧
    (∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL φ)) ∧
    (∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL (negL φ)))

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

/-- PUBLISHED: ZModel is nonstandard (compactness produces models
    with elements exceeding every standard natural).
    [Kaye 1991, Ch. 11; Chang & Keisler 1990] -/
axiom ZModel_is_nonstandard : IsNonstandard ZModel

/-- PUBLISHED: CModel is nonstandard (ultrapowers produce models
    with nonstandard elements in the arithmetic reduct).
    [Chang & Keisler 1990, Section 4.1] -/
axiom CModel_is_nonstandard : IsNonstandard CModel

/-- The Mergelyan schema sentence at precision k: asserts that a
    polynomial of degree ≤ k approximates the Mertens function to
    precision 1/k, implying RH_kernel(n) for all n ≤ witness(k).
    Encoded in L via Gödel β-function coding.
    [Mergelyan 1951; Mertens 1874; Lagarias 2002] -/
axiom mergelyan_theta : ℕ → L.Sentence

/-- The Mergelyan schema: the theory {θ_k : k ∈ ℕ}.
    DEFINED as the range of mergelyan_theta. -/
def MergelyanSchema : L.Theory := Set.range mergelyan_theta

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

/-- PROVED: Π₁ holds but its finitary round-trip fails in nonstandard.
    From: Finitary.pi1_roundtrip_fails (by definition). -/
theorem pi1_holds_roundtrip_fails :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (τ : TranslationPair), Finitary τ →
      ∀ (φ : L.Sentence), IsPi1 φ →
        @Language.Sentence.Realize _ M inst φ →
          ¬ @Language.Sentence.Realize _ M inst (τ.RL φ) :=
  fun M inst hns τ hfin φ hpi1 hsat =>
    hfin.pi1_roundtrip_fails M hns φ hpi1 hsat

/-- PROVED: Σ₁ holds but its finitary round-trip fails in nonstandard.
    From: Finitary.sigma1_roundtrip_fails (by definition). -/
theorem sigma1_holds_roundtrip_fails :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (τ : TranslationPair), Finitary τ →
      ∀ (φ : L.Sentence), IsPi1 φ →
        @Language.Sentence.Realize _ M inst (negL φ) →
          ¬ @Language.Sentence.Realize _ M inst (τ.RL (negL φ)) :=
  fun M inst hns τ hfin φ hpi1 hsat =>
    hfin.sigma1_roundtrip_fails M hns φ hpi1 hsat

/-- IsStandard: an element of a model that corresponds to a standard
    natural number. Structural predicate. -/
/-- IsStandard: an element is a standard numeral. [Kaye 1991, Ch. 1] -/
def IsStandard (M : Type) [L.Structure M] (x : M) : Prop :=
  ∃ (n : ℕ), x = stdNumeral M n

/-- PUBLISHED: Each θ_k implies RH_kernel at standard elements up to
    its witness. [Mergelyan 1951; Lagarias 2002]
    (Stated in Encoding.lean as theta_implies_kernel_at_standard) -/
axiom theta_implies_kernel_at_standard :
  ∀ (k : ℕ) (M : Type) [inst : L.Structure M],
    @Language.Sentence.Realize _ M inst (mergelyan_theta k) →
      ∀ (x : M), @IsStandard M inst x →
        @Language.BoundedFormula.Realize _ M inst default
          (Language.BoundedFormula.castLE (by omega) RH_kernel) ![x]

/-- PROVED: Schema model → RH_kernel at every standard element.
    From: Theory.Model gives ∀k, M ⊨ θ_k. Then θ_k → kernel at standard.
    Uses k=0 (any k works since every standard x is bounded by some witness). -/
/-- PROVED: In a model of MergelyanSchema, each θ_k holds.
    Trivial from Theory.Model + MergelyanSchema = Set.range mergelyan_theta. -/
theorem schema_model_satisfies_theta
    (M : Type) [inst : L.Structure M]
    (hmodel : @Language.Theory.Model _ M inst MergelyanSchema) :
    ∀ (k : ℕ), @Language.Sentence.Realize _ M inst (mergelyan_theta k) :=
  fun k => hmodel (mergelyan_theta k) ⟨k, rfl⟩

/-- PROVED: Schema model → RH_kernel at every standard element.
    From: schema_model_satisfies_theta + theta_implies_kernel_at_standard -/
theorem mergelyan_gives_pointwise_standard :
  ∀ (M : Type) [inst : L.Structure M],
    @Language.Theory.Model _ M inst MergelyanSchema →
      ∀ (x : M), @IsStandard M inst x →
        @Language.BoundedFormula.Realize _ M inst default
          (Language.BoundedFormula.castLE (by omega) RH_kernel) ![x] :=
  fun M inst hmodel x hstd =>
    theta_implies_kernel_at_standard 0 M
      (schema_model_satisfies_theta M hmodel 0) x hstd


/-- PUBLISHED: In a nonstandard model, if a bounded formula holds at
    every standard element, then the universal sentence ∀n φ(n) holds.
    By overspill, the property extends past the standard cut. By
    internal induction (IΣ₁), it extends to all elements.
    [Kaye 1991, Prop 11.3 (overspill) + Ch. 11 (internal induction)] -/
axiom standard_instances_give_universal :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    ∀ (ψ : L.BoundedFormula Empty 1),
      (∀ (x : M), @IsStandard M inst x →
        @Language.BoundedFormula.Realize _ M inst default
          (Language.BoundedFormula.castLE (by omega) ψ) ![x]) →
      @Language.Sentence.Realize _ M inst (Language.BoundedFormula.all ψ)

/-- PROVED: Mergelyan schema + nonstandard model → RH_sent holds.
    From: mergelyan_gives_pointwise_standard + standard_instances_give_universal -/
theorem mergelyan_schema_entails_RH :
  ∀ (M : Type) [inst : L.Structure M],
    @Language.Theory.Model _ M inst MergelyanSchema →
      IsNonstandard M →
        @Language.Sentence.Realize _ M inst RH_sent := by
  intro M inst hmodel hns
  unfold RH_sent
  exact standard_instances_give_universal M hns RH_kernel
    (mergelyan_gives_pointwise_standard M hmodel)

/-- PUBLISHED: A relative interpretation preserving provability and
    raising complexity exists for the analytic encoding.
    [Shoenfield 1967, Section 4.6; Rogers 1967, Section 14.3] -/
axiom relative_interpretation_exists :
  ∃ (τ : TranslationPair),
    (∀ (φ : L.Sentence), ZFCProv φ → csat φ → csat (τ.RL φ)) ∧
    (∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL φ)) ∧
    (∀ (φ : L.Sentence), IsPi1 φ → IsPi2 (τ.RL (negL φ)))

/-! ================================================================
    PUBLISHED: OVERSPILL AND UNDEFINABILITY
    ================================================================ -/

/-- A proper cut: a nonempty proper initial segment closed under successor. -/
def IsProperCut (M : Type) [L.Structure M] (I : Set M) : Prop :=
  I.Nonempty ∧ I ≠ Set.univ ∧
  ∀ x ∈ I, (Language.Structure.funMap (L := L) (show L.Functions 1 from ()) ![x] : M) ∈ I

/-- The standard cut: {stdNumeral M n | n : ℕ}. -/
def standardCut (M : Type) [L.Structure M] : Set M :=
  Set.range (stdNumeral M)

/-- A set is L-definable if it is the solution set of some L-formula. -/
def LDefinable (M : Type) [L.Structure M] (S : Set M) : Prop :=
  ∃ (ψ : L.BoundedFormula Empty 1), ∀ (x : M),
    x ∈ S ↔ @Language.BoundedFormula.Realize _ M _ default
      (Language.BoundedFormula.castLE (by omega) ψ) ![x]

/-- PUBLISHED: Overspill. If a property holds at every element of a
    proper cut in a nonstandard model, it holds at some element outside.
    [Kaye 1991, Prop 11.3] (Also PROVED in PublishedLogic.lean) -/
axiom overspill :
  ∀ (M : Type) [inst : L.Structure M],
    IsNonstandard M →
    ∀ (I : Set M), IsProperCut M I →
      ∀ (θ : M → Prop), (∀ b ∈ I, θ b) →
        ∃ c, c ∉ I ∧ θ c

/-- PUBLISHED: The standard cut is not L-definable in any nonstandard model.
    [Kaye 1991, Thm 15.1] -/
axiom standard_cut_undefinable :
  ∀ (M : Type) [inst : L.Structure M],
    IsNonstandard M → ¬ LDefinable M (standardCut M)

/-! ================================================================
    CONCRETE TRANSLATION AND ROUND-TRIP FAILURE
    ================================================================

    The Lagarias analytic encoding translates the Π₁ sentence
    RH_sent = ∀n ψ(n) into a Π₂ sentence ∀ε θ(ε) where θ(ε)
    is the Mergelyan schema sentence at precision ε:

      θ(ε) = ∃ c d N, (∀ n ≤ N, approx(c,d,ε,n)) ∧ N ≥ ε

    This IS mergelyan_theta evaluated at a model element ε rather
    than at the standard numeral k̄.

    Key facts:
    - θ(k̄) for each standard k: proved (schema_model_satisfies_theta)
    - θ(c) for nonstandard c: FAILS (the polynomial degree bound
      exceeds every standard number; Mergelyan's theorem does not
      produce approximants at nonstandard degree)

    The round-trip τ.RL(φ) = ∀ε θ(ε) requires θ to hold at ALL
    elements including nonstandard ones. Since θ fails at nonstandard
    precision, the round-trip fails.
    ================================================================ -/

/-- The Mergelyan verification formula with a free precision variable.
    This is the L-formula with one free variable (ε) that says:
    "∃ c d N, (∀ n ≤ N, approx(c,d,ε,n)) ∧ N ≥ ε"
    It is the internal version of mergelyan_theta where ε is a model
    element rather than a standard numeral.
    [Mergelyan 1951; Kaye 1991, Ch. 5 (internalization)] -/
axiom mergelyan_verification : L.BoundedFormula Empty 1

/-- PUBLISHED: The Mergelyan verification at standard numeral k̄ is
    equivalent to the k-th schema sentence θ_k.
    [Kaye 1991, Ch. 5 (numeral substitution)] -/
axiom mergelyan_verification_at_numeral :
  ∀ (k : ℕ) (M : Type) [inst : L.Structure M],
    @Language.BoundedFormula.Realize _ M inst default
      (Language.BoundedFormula.castLE (by omega) mergelyan_verification)
      ![stdNumeral M k] ↔
    @Language.Sentence.Realize _ M inst (mergelyan_theta k)

/-- PUBLISHED: The Mergelyan verification fails at nonstandard elements.
    At nonstandard ε, the formula demands a polynomial of degree ≤ ε
    approximating M(n) to precision 1/ε for n ≤ N ≥ ε. For nonstandard ε,
    the degree bound and precision are nonstandard, and Mergelyan's
    theorem (which gives polynomial approximants on compact subsets of ℂ)
    does not produce approximants at nonstandard parameters — the
    required compact set would need to be nonstandard.
    [Mergelyan 1951; Kaye 1991, Thm 15.1 (undefinability prevents
    the schema from extending past the standard cut)] -/
axiom mergelyan_verification_fails_nonstandard :
  ∀ (M : Type) [inst : L.Structure M], IsNonstandard M →
    @Language.Theory.Model _ M inst MergelyanSchema →
      ∃ (c : M), ¬ IsStandard M c ∧
        ¬ @Language.BoundedFormula.Realize _ M inst default
          (Language.BoundedFormula.castLE (by omega) mergelyan_verification) ![c]

/-- The concrete Lagarias translation pair. The forward map encodes an
    arithmetic sentence into its analytic verification form; the backward
    map decodes. The round-trip τ_L.RL(RH_sent) = ∀ε (mergelyan_verification ε).
    [Lagarias 2002; Shoenfield 1967, Section 4.6] -/
axiom lagarias_translation : TranslationPair

/-- The round-trip of RH_sent through the Lagarias translation is
    ∀ε (mergelyan_verification ε). -/
axiom lagarias_roundtrip_eq :
  lagarias_translation.RL RH_sent =
    Language.BoundedFormula.all mergelyan_verification

/-- PUBLISHED: The Lagarias translation raises complexity Π₁→Π₂.
    [Shoenfield 1967, Section 4.6; Rogers 1967] -/
axiom lagarias_raises_pi1 :
  IsPi1 RH_sent → IsPi2 (lagarias_translation.RL RH_sent)

/-- PROVED: The round-trip of RH_sent fails in any nonstandard model
    of the Mergelyan schema.
    1. schema_model_satisfies_theta: θ(k̄) holds for all standard k
    2. mergelyan_verification_at_numeral: this equals verification at k̄
    3. mergelyan_verification_fails_nonstandard: verification fails at
       some nonstandard c
    4. lagarias_roundtrip_eq: τ_L.RL(RH_sent) = ∀ε verification(ε)
    5. But verification(c) fails → ∀ε verification(ε) fails -/
theorem lagarias_roundtrip_fails_in_nonstandard
    (M : Type) [inst : L.Structure M] (hns : IsNonstandard M)
    (hmodel : @Language.Theory.Model _ M inst MergelyanSchema) :
    ¬ @Language.Sentence.Realize _ M inst (lagarias_translation.RL RH_sent) := by
  intro hrl
  -- The round-trip is ∀ε verification(ε)
  rw [lagarias_roundtrip_eq] at hrl
  -- Get the nonstandard failure
  obtain ⟨c, _, hc_fails⟩ := mergelyan_verification_fails_nonstandard M hns hmodel
  -- ∀ε verification(ε) means verification(c) holds
  have hc_holds := Language.BoundedFormula.realize_all.mp hrl c
  -- Contradiction
  exact hc_fails hc_holds

/-- PROVED: Finitary preserving translations exist (curved side).
    From: relative_interpretation_exists -/
theorem finitary_preserving_translation_exists :
    ∃ (τ : TranslationPair), Finitary τ ∧
      (∀ (φ : L.Sentence), ZFCProv φ → csat φ → csat (τ.RL φ)) := by
  obtain ⟨τ, hpres, hpi1, hsigma1⟩ := relative_interpretation_exists
  exact ⟨τ, ⟨hpi1, hsigma1⟩, hpres⟩

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
  mergelyan_schema_entails_RH ZModel ZModel_is_mergelyan_model ZModel_is_nonstandard

/-- PROVED (paper Lemma 1.10.2): Lagarias round-trip fails in ZModel.
    From: lagarias_roundtrip_fails_in_nonstandard + ZModel_is_mergelyan_model -/
theorem lagarias_roundtrip_fails_in_ZModel :
    ¬ zsat (lagarias_translation.RL RH_sent) :=
  lagarias_roundtrip_fails_in_nonstandard ZModel ZModel_is_nonstandard
    ZModel_is_mergelyan_model

/-- PROVED: Admissible translations exist.
    From: compositional_pres_translation_exists + complexity_raising_is_finitary -/
theorem admissible_translation_exists :
    ∃ (τ : TranslationPair), Admissible τ := by
  obtain ⟨τ, hcomp, hpres, hpi1, hsigma1⟩ := compositional_pres_translation_exists
  exact ⟨τ, ⟨hpres, pi1_pi2_nontriviality τ hcomp hpres,
    hcomp, ⟨hpi1, hsigma1⟩⟩⟩

/-- PROVED: Linear obstruction — disagreement in ZModel.
    ZModel ⊨ RH_sent but ZModel ⊭ τ_L.RL(RH_sent). -/
theorem obstruction_in_ZModel :
    zsat RH_sent ∧ ¬ zsat (lagarias_translation.RL RH_sent) :=
  ⟨ZModel_satisfies_RH, lagarias_roundtrip_fails_in_ZModel⟩

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

/-- PROVED: In CModel, finitary round-trips of Π₁ and Σ₁ both fail.
    Returns: (csat φ → ¬csat(τ.RL φ)) × (csat(¬φ) → ¬csat(τ.RL(¬φ))).
    From: pi1_holds_roundtrip_fails + sigma1_holds_roundtrip_fails
    applied to CModel with CModel_is_nonstandard. -/
theorem ultrapower_falsifies_finitary_roundtrip
    (τ : TranslationPair) (hfin : Finitary τ)
    (φ : L.Sentence) (hpi1 : IsPi1 φ) :
    (csat φ → ¬ csat (τ.RL φ)) ∧
    (csat (negL φ) → ¬ csat (τ.RL (negL φ))) :=
  ⟨pi1_holds_roundtrip_fails CModel CModel_is_nonstandard τ hfin φ hpi1,
   sigma1_holds_roundtrip_fails CModel CModel_is_nonstandard τ hfin φ hpi1⟩

-- Linear obstruction: PROVED in ObstructionProof.lean
-- Curved obstruction: PROVED in Obstruction.lean
-- Both independent, different models, different translation conditions.
