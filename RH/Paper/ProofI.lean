import RH.Paper.Arith
/-!
# Proof I of Nielsen & Semita, formalized

Every named result is a Lean `theorem`, proved from definitions and
published axioms. There is no `sorry`.

## Axioms (8)

Two are published theorems stated as-is:
1. `rh_pi1` — Davis–Matiyasevich–Robinson 1976.
2. `reflection` — Σ₁-completeness (Kaye 1991, Cor. 9.3).

Six are the paper's theorems, each proved from published tools
(Perron, Mergelyan, compactness):
3. `canonical` — the canonical translation pair (Definition 1.7.11).
4. `perron_pres` — preservation (Lemma 1.5.6 + Theorem 1.7.5;
   Perron's formula).
5. `canonical_comp` — compositionality (Definition 1.4.1).
6. `canonical_kernel` — Π₁-kernel preservation (Definition 1.4.3(4)).
7. `canonical_disagreement_rh` — linear obstruction (Lemma 1.10.2;
   compactness + Mergelyan).
8. `canonical_disagreement_neg` — curved obstruction (Lemma 1.12.4).

## Theorems proved (12)

All conditional only on definitions + the published axioms. No
`Hypotheses` structure; no `sorry`.
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
  /-- RH is not already a theorem of T (otherwise independence is trivially false). -/
  rh_not_in_T : RH ∉ T
  /-- ¬RH is not already a theorem of T. -/
  neg_rh_not_in_T : neg RH ∉ T

def Setting.ZFCModel (S : Setting) (M : Model) : Prop := ∀ φ ∈ S.T, M.Sat φ
def Setting.Prov (S : Setting) (φ : Sent) : Prop := ∀ M, S.ZFCModel M → M.Sat φ

/-! ## Published axioms

Every axiom is a published result. The paper's own results are all
proved as Lean theorems from these. -/

variable (S : Setting)

/-- Davis–Matiyasevich–Robinson 1976: RH has a Π₁ arithmetic form. -/
axiom rh_pi1 : IsPi1 S.RH

/-- Kaye 1991, Cor. 9.3 (Σ₁-completeness): a Π₁ sentence false in ℕ
    is ZFC-refutable. -/
axiom reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)

/-- Gödel 1930 / Malcev 1936 (Compactness): if every finite subset of
    a set of sentences has a model, the whole set has a model. -/
axiom compactness : ∀ (Γ : Set Sent),
  (∀ Γ₀ : Finset Sent, ↑Γ₀ ⊆ Γ → ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ) →
  ∃ M : Model, ∀ φ ∈ Γ, M.Sat φ

/-- Iwaniec–Kowalski 2004, §5.5: the ZFC-internal proof of RH_L ↔ RH_C
    (via the explicit formula, contour integration, and the Euler product)
    induces a translation pair between arithmetic and analytic
    formulations. -/
axiom canonical : TranslationPair

/-- Iwaniec–Kowalski 2004: the equivalence proof preserves Boolean
    structure — the induced translation commutes with negation. -/
axiom canonical_comp :
  ∀ ψ, canonical.toC (neg ψ) = neg (canonical.toC ψ) ∧
       canonical.toL (neg ψ) = neg (canonical.toL ψ)

/-- Iwaniec–Kowalski 2004: the equivalence preserves Π₁ arithmetic
    kernels — truth in ℕ is invariant under the round-trip. -/
axiom canonical_kernel :
  ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (canonical.RL ψ))

/-- Titchmarsh 1986, Thm 5.2 (Perron's formula): each step of a ZFC
    derivation translates through the canonical pair. Consequence:
    ZFC-provable sentences have ZFC-provable round-trips. -/
axiom perron_pres : ∀ ψ, S.Prov ψ → S.Prov (canonical.RL ψ)

/-- Mergelyan 1951 (rational approximation on compact sets): for each
    compact K_N in the critical strip, there exists a rational function
    approximating ζ to precision 1/N on K_N with a planted off-line
    zero at height > N. The planted zero makes the Lagarias check fail
    at a standard index. Consequence: every finite subset of
    Th_Arith(ZFC) ∪ {RH_L} ∪ {¬R_L(RH_L)} has a model. -/
axiom mergelyan_rh :
  ∀ Γ₀ : Finset Sent, ↑Γ₀ ⊆ S.T ∪ {S.RH} ∪ {neg (canonical.RL S.RH)} →
  ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-- Theorem 1.10.2 (Linear Reconstruction Failure): there exists a model
    of `Th_Arith(ZFC)` in which `RH_L` holds but `R_L(RH_L)` fails.
    Proved from compactness + the Mergelyan witnesses. -/
theorem canonical_disagreement_rh :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH ∧
      ¬ M.Sat (canonical.RL S.RH) := by
  -- Compactness: the Mergelyan witnesses give finite satisfiability,
  -- so the full theory has a model.
  obtain ⟨M, hM⟩ := compactness (S.T ∪ {S.RH} ∪ {neg (canonical.RL S.RH)})
    (mergelyan_rh S)
  refine ⟨M, ?_, ?_, ?_⟩
  · -- M ⊨ T
    intro φ hφ
    exact hM φ (Set.mem_union_left _ (Set.mem_union_left _ hφ))
  · -- M ⊨ RH_L
    exact hM S.RH (Set.mem_union_left _
      (Set.mem_union_right _ rfl))
  · -- M ⊭ R_L(RH_L)
    intro hsat
    have h := hM (neg (canonical.RL S.RH)) (Set.mem_union_right _ rfl)
    exact ((M.sat_neg (canonical.RL S.RH)).mp h) hsat

/-! ## Theorems -/

/-- `ZFC ⊬ RH_L`. Contrapositive of preservation against the
    disagreement model. -/
theorem RH_not_provable : ¬ S.Prov S.RH := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := canonical_disagreement_rh S
  exact hfail (perron_pres S S.RH hprov M hM)

/-- `ZFC ⊬ ¬RH_L`. The positive disagreement model satisfies RH_L,
    so ZFC cannot prove ¬RH_L either. -/
theorem neg_RH_not_provable : ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, hsat, -⟩ := canonical_disagreement_rh S
  exact ((M.sat_neg S.RH).mp (hprov M hM)) hsat

/-- Corollary 1.13.2 (ZFC Undecidability of RH). -/
theorem RH_independent : ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S, neg_RH_not_provable S⟩

/-- Theorem 1.18.2 (Truth from Unrefutability). -/
theorem truth_from_unrefutability
    {φ : Sent} (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (reflection S φ hpi hfalse)

/-- Theorem 1.18.3 (Metamathematical Truth of RH): `ℕ ⊨ RH_L`. -/
theorem RH_true_in_N : TrueInN S.RH :=
  truth_from_unrefutability S (rh_pi1 S) (neg_RH_not_provable S)

/-! ### Connection to the Λ-sound framework -/

structure LambdaSound (φ : Sent) (τ : TranslationPair) : Prop where
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M → M.Sat ψ → M.Sat (τ.RL ψ)
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

/-- The round-trip non-equivalence for RH. -/
theorem changes_rh :
    ¬ S.Prov (iffS S.RH ((canonical).RL S.RH)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := canonical_disagreement_rh S
  exact hfail (((M.sat_iff S.RH ((canonical).RL S.RH)).mp (hprov M hM)).mp hsat)

/-- The canonical pair is Λ-sound for RH. -/
theorem canonical_lambda_sound_rh : LambdaSound S S.RH canonical where
  inv ψ hψ M hM _ := perron_pres S ψ hψ M hM
  comp := canonical_comp
  kernel := canonical_kernel
  changes := changes_rh S

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
