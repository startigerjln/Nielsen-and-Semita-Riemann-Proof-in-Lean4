import RH.Paper.Arith
/-!
# Proof I of Nielsen & Semita, formalized as written

This file follows Section 1 of `unified.tex`. It contains no `axiom` and no
`sorry`.

The arithmetic form of RH is an abstract Π₁ sentence `S.RH`. No number
theory is used.

The paper's argument has two kinds of ingredients:

* **Deductions**, which are proved here: Uniform Preservation, Λ-Reduction
  Soundness, the Lambda Irreducibility Theorem, Λ-irreducibility of RH,
  ZFC-independence of RH, and truth of RH in ℕ.

* **Lemmas whose proofs in the paper are prose arguments** about translations
  and models that are not given explicitly enough for Lean to check. These
  are collected in the structure `Hypotheses`, each with a pointer to the
  place in the paper where it is stated. They are assumptions of every
  theorem below, not established facts.

So what is machine-checked is: *if* the items in `Hypotheses` hold, *then*
the paper's conclusions follow.
-/

open FirstOrder

namespace RH.Paper

/-! ## Sentences, models, truth -/

abbrev Sent := L.Sentence

/-- Negation of a sentence. -/
def neg (φ : Sent) : Sent := Language.BoundedFormula.not φ

/-- An `L`-structure, bundled with its carrier. -/
structure Model where
  carrier : Type
  str : L.Structure carrier

/-- `M ⊨ φ`. -/
def Model.Sat (M : Model) (φ : Sent) : Prop :=
  @Language.Sentence.Realize L M.carrier M.str φ

/-- Truth in the standard model ℕ. -/
def TrueInN (φ : Sent) : Prop :=
  @Language.Sentence.Realize L ℕ natStructure φ

/-- Π₁ sentences: `∀ n, ψ(n)` with `ψ` a Δ₀ formula. -/
def IsPi1 (φ : Sent) : Prop :=
  ∃ ψ : L.BoundedFormula Empty 1, IsDelta0 ψ ∧ φ = Language.BoundedFormula.all ψ

/-! ## Translation pairs and round trips (Definitions 1.4.1, 1.4.2)

Following the paper's remark on the Lean formalization, sentences of both
paradigms are coded as `L`-sentences. -/

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
  /-- `ZFC ⊢ φ` for (arithmetized) sentences. -/
  Prov : Sent → Prop
  /-- The model class of the linear paradigm. -/
  Lin : Model → Prop
  /-- The model class of the curved paradigm. -/
  Cur : Model → Prop
  /-- The arithmetic formulation `RH_L`. -/
  RH : Sent

variable (S : Setting)

/-- Λ-sound translation pairs (Definition 1.4.3), in the form in which the
    conditions are used in the proofs of Theorem 1.5.2 and Lemma 1.5.5. -/
structure LambdaSound (τ : TranslationPair) : Prop where
  /-- (3) Model invariance, linear paradigm. -/
  inv_lin : ∀ φ, S.Prov φ → ∀ M, S.Lin M → M.Sat φ → M.Sat (τ.RL φ)
  /-- (1),(2) Translations of theorems hold in the curved paradigm. -/
  toC_sound : ∀ φ, S.Prov φ → ∀ M, S.Cur M → M.Sat (τ.toC φ)
  /-- (3) Model invariance, curved paradigm. -/
  inv_cur : ∀ φ, S.Prov φ → ∀ M, S.Cur M →
    M.Sat (τ.toC φ) → M.Sat (τ.RC (τ.toC φ))
  /-- (4) Π₁-kernel preservation, at the level of truth in ℕ. -/
  kernel : ∀ φ, IsPi1 φ → (TrueInN φ ↔ TrueInN (τ.RL φ))

/-- Linear Λ-obstruction is nonzero: some linear model separates `φ` from
    its round trip (Definition 1.5.3). -/
def LObstructs (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M, S.Lin M ∧ ¬ (M.Sat φ ↔ M.Sat (τ.RL φ))

/-- Curved Λ-obstruction of `T_{L→C}(φ)` is nonzero (Definitions 1.5.3, 1.5.4). -/
def CObstructs (τ : TranslationPair) (φ : Sent) : Prop :=
  ∃ M, S.Cur M ∧ ¬ (M.Sat (τ.toC φ) ↔ M.Sat (τ.RC (τ.toC φ)))

/-- Λ-irreducibility (Definition 1.5.4), for every Λ-sound pair as in
    Theorem 1.13.1. -/
def LIrreducible (φ : Sent) : Prop :=
  ∀ τ, LambdaSound S τ → LObstructs S τ φ ∧ CObstructs S τ φ

/-! ## What is assumed -/

/-- The paper's lemmas that are taken as hypotheses. -/
structure Hypotheses : Prop where
  /-- Soundness of ZFC for the linear model class. Used in Theorem 1.5.2. -/
  sound : ∀ φ, S.Prov φ → ∀ M, S.Lin M → M.Sat φ
  /-- RH has a Π₁ form with Δ₀ kernel (Proposition 1.17.1, citing
      Davis–Matiyasevich–Robinson). -/
  rh_pi1 : IsPi1 S.RH
  /-- Π₁ Witness Reflection (Theorem 1.16.1). -/
  reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)
  /-- Λ-Exhaustiveness (Theorem 1.7.5) as used in the proof of
      Theorem 1.6.1: a ZFC derivation of RH or of ¬RH induces a Λ-sound
      translation pair. -/
  exhaustive : (S.Prov S.RH ∨ S.Prov (neg S.RH)) → ∃ τ, LambdaSound S τ
  /-- Linear Reconstruction Failure (Lemmas 1.10.2, 1.10.3): for every
      Λ-sound pair there is a linear model with `M ⊨ RH_L` and
      `M ⊭ R_L(RH_L)`. -/
  linear_failure : ∀ τ, LambdaSound S τ →
    ∃ M, S.Lin M ∧ M.Sat S.RH ∧ ¬ M.Sat (τ.RL S.RH)
  /-- Analytic Reconstruction Failure (Lemma 1.12.4): a curved model with
      `M ⊨ RH_C` and `M ⊭ R_C(RH_C)`. -/
  curved_failure : ∀ τ, LambdaSound S τ →
    ∃ M, S.Cur M ∧ M.Sat (τ.toC S.RH) ∧ ¬ M.Sat (τ.RC (τ.toC S.RH))
  /-- The Σ₁ side (Remark after Corollary 1.13.2): a curved model with
      `M ⊨ ¬RH_C` and `M ⊭ R_C(¬RH_C)`. -/
  curved_failure_neg : ∀ τ, LambdaSound S τ →
    ∃ M, S.Cur M ∧ M.Sat (τ.toC (neg S.RH)) ∧
      ¬ M.Sat (τ.RC (τ.toC (neg S.RH)))

variable {S}

/-! ## What is proved -/

/-- Lemma 1.5.5 (Uniform Preservation under ZFC-Provability), linear side. -/
theorem uniform_preservation_lin (H : Hypotheses S) {τ : TranslationPair}
    (hτ : LambdaSound S τ) {φ : Sent} (hφ : S.Prov φ) (M : Model) (hM : S.Lin M) :
    M.Sat φ ↔ M.Sat (τ.RL φ) :=
  ⟨fun h => hτ.inv_lin φ hφ M hM h, fun _ => H.sound φ hφ M hM⟩

/-- Lemma 1.5.5, curved side. -/
theorem uniform_preservation_cur {τ : TranslationPair}
    (hτ : LambdaSound S τ) {φ : Sent} (hφ : S.Prov φ) (M : Model) (hM : S.Cur M) :
    M.Sat (τ.toC φ) ↔ M.Sat (τ.RC (τ.toC φ)) :=
  ⟨fun h => hτ.inv_cur φ hφ M hM h, fun _ => hτ.toC_sound φ hφ M hM⟩

/-- Theorem 1.5.2 (Λ-Reduction Soundness): if `ZFC ⊢ φ` then the
    Λ-obstruction of `φ` vanishes in both paradigms. -/
theorem lambda_reduction_soundness (H : Hypotheses S) {τ : TranslationPair}
    (hτ : LambdaSound S τ) {φ : Sent} (hφ : S.Prov φ) :
    ¬ LObstructs S τ φ ∧ ¬ CObstructs S τ φ := by
  constructor
  · rintro ⟨M, hM, hne⟩
    exact hne (uniform_preservation_lin H hτ hφ M hM)
  · rintro ⟨M, hM, hne⟩
    exact hne (uniform_preservation_cur hτ hφ M hM)

/-- Theorem 1.6.1 (Lambda Irreducibility Theorem), one direction: if every
    Λ-sound pair has nonzero obstruction on `φ` in one of the paradigms, and
    a derivation of `φ` would induce a Λ-sound pair, then `ZFC ⊬ φ`. -/
theorem not_provable_of_obstruction (H : Hypotheses S) {φ : Sent}
    (hobs : ∀ τ, LambdaSound S τ → LObstructs S τ φ ∨ CObstructs S τ φ)
    (hex : S.Prov φ → ∃ τ, LambdaSound S τ) :
    ¬ S.Prov φ := by
  intro hφ
  obtain ⟨τ, hτ⟩ := hex hφ
  have hvanish := lambda_reduction_soundness H hτ hφ
  rcases hobs τ hτ with h | h
  · exact hvanish.1 h
  · exact hvanish.2 h

/-- Theorem 1.13.1 (Λ-Irreducibility of RH). -/
theorem RH_lambda_irreducible (H : Hypotheses S) : LIrreducible S S.RH := by
  intro τ hτ
  constructor
  · obtain ⟨M, hM, h1, h2⟩ := H.linear_failure τ hτ
    exact ⟨M, hM, fun hiff => h2 (hiff.mp h1)⟩
  · obtain ⟨M, hM, h1, h2⟩ := H.curved_failure τ hτ
    exact ⟨M, hM, fun hiff => h2 (hiff.mp h1)⟩

/-- Corollary 1.13.2, first half: `ZFC ⊬ RH`. -/
theorem RH_not_provable (H : Hypotheses S) : ¬ S.Prov S.RH :=
  not_provable_of_obstruction H
    (fun τ hτ => Or.inl (RH_lambda_irreducible H τ hτ).1)
    (fun h => H.exhaustive (Or.inl h))

/-- Corollary 1.13.2, second half: `ZFC ⊬ ¬RH`, via the curved obstruction
    of `¬RH`. -/
theorem neg_RH_not_provable (H : Hypotheses S) : ¬ S.Prov (neg S.RH) :=
  not_provable_of_obstruction H
    (fun τ hτ => by
      obtain ⟨M, hM, h1, h2⟩ := H.curved_failure_neg τ hτ
      exact Or.inr ⟨M, hM, fun hiff => h2 (hiff.mp h1)⟩)
    (fun h => H.exhaustive (Or.inr h))

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent (H : Hypotheses S) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable H, neg_RH_not_provable H⟩

/-- Theorem 1.18.1 (Truth of RH from Independence), for any Π₁ sentence. -/
theorem truth_from_unrefutability (H : Hypotheses S) {φ : Sent}
    (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (H.reflection φ hpi hfalse)

/-- Theorem 1.18.2 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`. -/
theorem RH_true_in_N (H : Hypotheses S) : TrueInN S.RH :=
  truth_from_unrefutability H H.rh_pi1 (neg_RH_not_provable H)

end RH.Paper
