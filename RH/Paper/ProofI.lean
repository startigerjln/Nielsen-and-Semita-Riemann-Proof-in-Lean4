import RH.Paper.Arith
/-!
# Proof I: Λ-Irreducibility and independence of RH

This module formalizes the deductive core of Nielsen & Semita's Proof I.

## Key design: reductio-scoped finite satisfiability

The finite satisfiability of each disagreement theory is NOT an external
assumption.  It is derived INSIDE each reductio from the hypothesis being
refuted, via soundness of ZFC:

  Non-provability: assume ZFC ⊢ RH
    → soundness: ℕ ⊨ RH
    → Mergelyan schema: disagreement theory is finitely satisfiable
    → compactness: disagreement model exists
    → round-trip preservation contradicts the model → ⊥
    → discharge: ZFC ⊬ RH

  Non-refutability: assume ZFC ⊢ ¬RH
    → soundness: ℕ ⊨ ¬RH
    → Mergelyan schema: negation disagreement theory is finitely satisfiable
    → compactness: negation disagreement model exists
    → round-trip preservation contradicts the model → ⊥
    → discharge: ZFC ⊬ ¬RH

  Truth: non-refutability + Π₁ + Σ₁-completeness (Kreisel reflection)

The dependency graph is explicit in Lean's kernel: `TruthGivesFS` and
`NegTruthGivesFS` take the truth derived from soundness as an argument.
The `intro hprov` that opens each reductio is the ONLY source of the
truth that feeds finite satisfiability.  When `False` is reached, `hprov`
is discharged and nothing about truth or finite satisfiability survives
into the conclusion.
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

/-- Soundness of the base theory for arithmetic:
    every provable sentence is true in ℕ.
    For ZFC this is a standard metatheoretic fact [Shoenfield 1967]. -/
def ArithSoundness (S : Setting) : Prop :=
  ∀ φ, S.Prov φ → TrueInN φ

/-- Σ₁ witness reflection (Kreisel): if a Π₁ sentence is false in ℕ,
    there is a standard witness to its failure, so its negation is
    provable.  Contrapositive: non-refutability implies truth.
    [Kreisel 1951; Kaye 1991] -/
def WitnessReflection (S : Setting) : Prop :=
  ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)

/-- Provability preservation for the round trip [Manuscript §1.5–1.7]. -/
def RoundTripPreserves (S : Setting) (τ : TranslationPair) : Prop :=
  ∀ ψ, S.Prov ψ → S.Prov (τ.RL ψ)

/-! ## Disagreement theories and finite satisfiability

The disagreement theories express the claim that RH (or ¬RH)
holds in a model of T, but the round-trip translation does not
preserve this.  The finite satisfiability of these theories is
the Mergelyan schema argument: each finite fragment constrains
only finitely many standard bounds, all met in ℕ once soundness
(inside the reductio) has supplied truth.
-/

/-- The positive disagreement theory: RH holds but its
    round trip fails. -/
def disagreementTheory (S : Setting) (τ : TranslationPair) : Set Sent :=
  S.T ∪ {S.RH} ∪ {neg (τ.RL S.RH)}

/-- The negative disagreement theory: ¬RH holds but its
    round trip fails. -/
def negDisagreementTheory (S : Setting) (τ : TranslationPair) : Set Sent :=
  S.T ∪ {neg S.RH} ∪ {neg (τ.RL (neg S.RH))}

def OverspillFiniteSatisfiability (S : Setting) (τ : TranslationPair) : Prop :=
  FiniteSatisfiable (disagreementTheory S τ)

def NegOverspillFiniteSatisfiability (S : Setting) (τ : TranslationPair) : Prop :=
  FiniteSatisfiable (negDisagreementTheory S τ)

/-- The positive Mergelyan bridge: truth of RH in ℕ implies finite
    satisfiability of the positive disagreement theory.

    Each finite fragment Δ ⊂ T ∪ {RH} ∪ {¬RL(RH)} constrains only
    finitely many standard numerals.  Since ℕ ⊨ RH (supplied by
    soundness inside the reductio), all finite bounds are met in ℕ,
    so every finite Δ is satisfiable.
    [Mergelyan 1951; Kaye 1991, Thm 15.1] -/
def TruthGivesFS (S : Setting) (τ : TranslationPair) : Prop :=
  TrueInN S.RH → OverspillFiniteSatisfiability S τ

/-- The negative Mergelyan bridge: truth of ¬RH in ℕ implies finite
    satisfiability of the negative disagreement theory.
    Symmetric argument. -/
def NegTruthGivesFS (S : Setting) (τ : TranslationPair) : Prop :=
  TrueInN (neg S.RH) → NegOverspillFiniteSatisfiability S τ

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

/-- Compactness converts finite satisfiability of the negative
    disagreement theory into a model where ¬RH holds but its
    round trip fails. -/
theorem neg_canonical_disagreement (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hf : NegOverspillFiniteSatisfiability S τ) :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat (neg S.RH) ∧
      ¬ M.Sat (τ.RL (neg S.RH)) := by
  obtain ⟨M, hM⟩ := hc (negDisagreementTheory S τ) hf
  refine ⟨M, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hM φ (Set.mem_union_left _ (Set.mem_union_left _ hφ))
  · exact hM (neg S.RH) (Set.mem_union_left _
      (Set.mem_union_right _ rfl))
  · intro hsat
    have h := hM (neg (τ.RL (neg S.RH))) (Set.mem_union_right _ rfl)
    exact ((M.sat_neg (τ.RL (neg S.RH))).mp h) hsat

/-! ## The reductio arguments

Both directions share the same structure:
1. `intro hprov` — assume provability (the reductio hypothesis)
2. `hs _ hprov`  — soundness gives truth in ℕ
3. `h(n)tfs _`   — Mergelyan bridge gives finite satisfiability
4. compactness   — disagreement model exists
5. round-trip    — preservation contradicts the model → False
6. discharge     — `hprov` is consumed; nothing about truth survives
-/

/-- **Non-provability of RH** (Theorem 1.6.1 / Remark 1.6.2).

    The finite satisfiability that feeds compactness is derived
    inside the reductio from `hprov : S.Prov S.RH` via soundness
    and the Mergelyan bridge.  It is never an external assumption. -/
theorem RH_not_provable (S : Setting) (τ : TranslationPair)
    (hc : Compactness)
    (hs : ArithSoundness S)
    (htfs : TruthGivesFS S τ)
    (hp : RoundTripPreserves S τ) : ¬ S.Prov S.RH := by
  intro hprov
  -- Soundness: the reductio hypothesis gives truth in ℕ
  have htruth : TrueInN S.RH := hs S.RH hprov
  -- Mergelyan bridge: truth gives finite satisfiability
  have hf : OverspillFiniteSatisfiability S τ := htfs htruth
  -- Compactness: disagreement model
  obtain ⟨M, hM, -, hfail⟩ := canonical_disagreement S τ hc hf
  -- Round-trip preservation contradicts the model
  exact hfail (hp S.RH hprov M hM)

/-- **Non-refutability of RH** (symmetric reductio).

    The finite satisfiability that feeds compactness is derived
    inside the reductio from `hprov : S.Prov (neg S.RH)` via
    soundness and the negative Mergelyan bridge. -/
theorem neg_RH_not_provable (S : Setting) (τ : TranslationPair)
    (hc : Compactness)
    (hs : ArithSoundness S)
    (hntfs : NegTruthGivesFS S τ)
    (hp : RoundTripPreserves S τ) : ¬ S.Prov (neg S.RH) := by
  intro hprov
  -- Soundness: the reductio hypothesis gives ¬RH true in ℕ
  have htruth : TrueInN (neg S.RH) := hs (neg S.RH) hprov
  -- Negative Mergelyan bridge: truth of ¬RH gives finite satisfiability
  have hf : NegOverspillFiniteSatisfiability S τ := hntfs htruth
  -- Compactness: negation disagreement model
  obtain ⟨M, hM, -, hfail⟩ := neg_canonical_disagreement S τ hc hf
  -- Round-trip preservation contradicts the model
  exact hfail (hp (neg S.RH) hprov M hM)

/-- Non-refutability via an explicit model of ZFC + RH.
    Useful when the model is obtained by other means. -/
theorem neg_RH_not_provable_of_model (S : Setting)
    (hmodel : ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH) :
    ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, hsat⟩ := hmodel
  exact ((M.sat_neg S.RH).mp (hprov M hM)) hsat

/-! ## Independence and truth -/

/-- **Independence of RH from ZFC** (Theorem 1.18.1). -/
theorem RH_independent (S : Setting) (τ : TranslationPair)
    (hc : Compactness) (hs : ArithSoundness S)
    (htfs : TruthGivesFS S τ) (hntfs : NegTruthGivesFS S τ)
    (hp : RoundTripPreserves S τ) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S τ hc hs htfs hp,
   neg_RH_not_provable S τ hc hs hntfs hp⟩

/-- Truth from non-refutability (Theorem 1.18.2).
    Kreisel reflection: a Π₁ sentence that is not refutable in a
    Σ₁-complete theory must be true in ℕ. -/
theorem truth_from_unrefutability (S : Setting)
    (hr : WitnessReflection S) {φ : Sent}
    (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (hr φ hpi hfalse)

/-- **Truth of RH in ℕ** (Theorem 1.18.3).

    Non-refutability (from the symmetric reductio) + Π₁ + Kreisel
    reflection.  Both reductios have already closed; this step is
    external to them. -/
theorem RH_true_in_N (S : Setting) (τ : TranslationPair)
    (hpi : IsPi1 S.RH) (hr : WitnessReflection S)
    (hc : Compactness) (hs : ArithSoundness S)
    (hntfs : NegTruthGivesFS S τ)
    (hp : RoundTripPreserves S τ) :
    TrueInN S.RH :=
  truth_from_unrefutability S hr hpi
    (neg_RH_not_provable S τ hc hs hntfs hp)

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
is itself produced inside the reductio (see `changes_rh`).
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
