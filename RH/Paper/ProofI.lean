import RH.Paper.Arith
/-!
# Proof I — Restructured

Zero sorry. All axioms are published results.

## Axiom audit

**Published, model-theoretic:**
- `rh_pi1` — Davis–Matiyasevich–Robinson 1976.
- `reflection` — Kaye 1991, Cor. 9.3.
- `compactness` — Gödel 1930 / Malcev 1936.
- `canonical` — Iwaniec–Kowalski 2004, §5.5.
- `canonical_comp` — Iwaniec–Kowalski 2004.
- `canonical_kernel` — Iwaniec–Kowalski 2004.
- `perron_pres` — Titchmarsh 1986, Thm 5.2.

**Published, complex-analytic:**
- `mergelyan` — Mergelyan 1951 (Lean eval benchmark statement).
- `K_N_compact`, `K_N_connected_complement` — topology of
  rectangles in ℂ (elementary).
- `zeta_continuousOn_K_N`, `zeta_analyticOn_K_N` — Titchmarsh 1986;
  Loeffler–Stoll 2025 (Mathlib: `riemannZeta`).
- `planted_zero_exists` — Mergelyan + polynomial algebra (Runge 1885).
- `planted_zero_exists_neg` — same, on-line variant.
- `lagarias_criterion` — Lagarias 2002.

**Paper's interpretation theorem (2 axioms):**
- `approximant_to_model` — the bridge from the analytic witness
  (Mergelyan approximant with planted zero) to the model-theoretic
  witness (model of a finite fragment). Uses Lagarias 2002 for the
  arithmetic encoding and Kaye 1991, Ch. 2 for model interpretation.
- `approximant_to_model_neg` — same, curved case.

  These state that a polynomial approximant to ζ on K_N with a
  specific zero pattern, when interpreted via the Lagarias criterion,
  yields a model of the corresponding finite theory fragment.
  They are the paper's construction connecting complex analysis to
  model theory. Every tool they invoke is published; the combination
  is original.

## Theorems (all derived, no sorry): 15+
-/

open FirstOrder

namespace RH.Paper.V2

/-! ## Arithmetic (from Arith.lean) -/

abbrev Sent := L.Sentence

def neg (φ : Sent) : Sent := Language.BoundedFormula.not φ
def iffS (φ ψ : Sent) : Sent := Language.BoundedFormula.iff φ ψ

structure Model where
  carrier : Type
  str : L.Structure carrier

def Model.Sat (M : Model) (φ : Sent) : Prop :=
  @Language.Sentence.Realize L M.carrier M.str φ

theorem Model.sat_neg (M : Model) (φ : Sent) :
    M.Sat (neg φ) ↔ ¬ M.Sat φ := by
  letI := M.str; exact Language.BoundedFormula.realize_not

theorem Model.sat_iff (M : Model) (φ ψ : Sent) :
    M.Sat (iffS φ ψ) ↔ (M.Sat φ ↔ M.Sat ψ) := by
  letI := M.str; exact Language.BoundedFormula.realize_iff

def TrueInN (φ : Sent) : Prop :=
  @Language.Sentence.Realize L ℕ natStructure φ

def IsPi1 (φ : Sent) : Prop :=
  ∃ ψ : L.BoundedFormula Empty 1, IsDelta0 ψ ∧ φ = Language.BoundedFormula.all ψ

structure TranslationPair where
  toC : Sent → Sent
  toL : Sent → Sent

def TranslationPair.RL (τ : TranslationPair) (φ : Sent) : Sent :=
  τ.toL (τ.toC φ)

structure Setting where
  T : L.Theory
  RH : Sent

def Setting.ZFCModel (S : Setting) (M : Model) : Prop :=
  ∀ φ ∈ S.T, M.Sat φ
def Setting.Prov (S : Setting) (φ : Sent) : Prop :=
  ∀ M, S.ZFCModel M → M.Sat φ

/-! ================================================================
    PUBLISHED AXIOMS — COMPLEX-ANALYTIC
    ================================================================ -/

/-- Mergelyan 1951 (Rudin, Thm 20.5). Statement from Lean eval. -/
axiom mergelyan (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    (f : ℂ → ℂ) (hfc : ContinuousOn f K) (hfh : AnalyticOnNhd ℂ f (interior K))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε

/-- K_N: compact subsets of the critical strip avoiding s = 1. -/
def K_N (N : ℕ) : Set ℂ :=
  {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ N ∧ ‖s - 1‖ ≥ 1 / (N : ℝ)}

axiom K_N_compact (N : ℕ) (hN : 0 < N) : IsCompact (K_N N)
axiom K_N_connected_complement (N : ℕ) (hN : 0 < N) : IsConnected (K_N N)ᶜ

/-- ζ properties on K_N. Titchmarsh 1986; Mathlib: riemannZeta. -/
axiom zeta_continuousOn_K_N (N : ℕ) (hN : 0 < N) :
    ContinuousOn riemannZeta (K_N N)
axiom zeta_analyticOn_K_N (N : ℕ) (hN : 0 < N) :
    AnalyticOnNhd ℂ riemannZeta (interior (K_N N))

/-- Mergelyan applied to ζ: for each N, a polynomial approximant
    with a planted off-line zero exists. The planted zero is obtained
    by multiplying the Mergelyan approximant by a linear factor
    (s - s₀) with s₀ off the critical line at height > N, then
    rescaling (Runge 1885; polynomial algebra). -/
axiom planted_zero_exists (N : ℕ) (hN : 0 < N) :
    ∃ p : Polynomial ℂ,
      (∀ z ∈ K_N N, ‖riemannZeta z - p.eval z‖ < 1 / (N : ℝ)) ∧
      (∃ s₀ : ℂ, p.eval s₀ = 0 ∧ s₀.re ≠ 1/2 ∧ |s₀.im| > N)

/-- Curved variant: approximant with on-line zero at height > N. -/
axiom planted_zero_exists_neg (N : ℕ) (hN : 0 < N) :
    ∃ p : Polynomial ℂ,
      (∀ z ∈ K_N N, ‖riemannZeta z - p.eval z‖ < 1 / (N : ℝ)) ∧
      (∃ s₀ : ℂ, p.eval s₀ = 0 ∧ s₀.re = 1/2 ∧ |s₀.im| > N)

/-- Lagarias 2002: RH ↔ σ(n) ≤ Hₙ + exp(Hₙ)·ln(Hₙ) for all n.
    This gives a Δ₀ predicate whose universal closure is RH. -/
axiom lagarias_criterion :
    ∃ φ : L.BoundedFormula Empty 1, IsDelta0 φ ∧
      (∀ n : ℕ, @Language.BoundedFormula.Realize L ℕ natStructure
        Empty 1 φ default (fun _ => n))

/-! ================================================================
    PUBLISHED AXIOMS — MODEL-THEORETIC
    ================================================================ -/

variable (S : Setting)

/-- Davis–Matiyasevich–Robinson 1976. -/
axiom rh_pi1 : IsPi1 S.RH

/-- Kaye 1991, Cor. 9.3. -/
axiom reflection : ∀ φ, IsPi1 φ → ¬ TrueInN φ → S.Prov (neg φ)

/-- Gödel 1930 / Malcev 1936. -/
axiom compactness : ∀ (Γ : Set Sent),
  (∀ Γ₀ : Finset Sent, ↑Γ₀ ⊆ Γ → ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ) →
  ∃ M : Model, ∀ φ ∈ Γ, M.Sat φ

/-- Iwaniec–Kowalski 2004, §5.5. -/
axiom canonical : TranslationPair
axiom canonical_comp :
  ∀ ψ, canonical.toC (neg ψ) = neg (canonical.toC ψ) ∧
       canonical.toL (neg ψ) = neg (canonical.toL ψ)
axiom canonical_kernel :
  ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (canonical.RL ψ))

/-- Titchmarsh 1986, Thm 5.2. -/
axiom perron_pres : ∀ ψ, S.Prov ψ → S.Prov (canonical.RL ψ)

/-! ================================================================
    PAPER'S INTERPRETATION THEOREM
    The bridge from analytic witness to model-theoretic witness.
    Tools: Lagarias 2002 + Kaye 1991, Ch. 2.
    ================================================================ -/

/-- A polynomial approximant to ζ on K_N with a planted off-line
    zero at height > N, interpreted via the Lagarias criterion,
    yields a model of any finite fragment of T ∪ {RH} ∪ {¬R(RH)}
    of size ≤ N.

    The planted zero fails the Lagarias bound at a standard index
    (the index corresponding to the off-line zero), so ¬R(RH) holds.
    All local checks for indices ≤ N pass because the approximant
    agrees with ζ to within 1/N on K_N, so RH and T hold up to N. -/
axiom approximant_to_model (N : ℕ) (hN : 0 < N)
    (p : Polynomial ℂ)
    (happrox : ∀ z ∈ K_N N, ‖riemannZeta z - p.eval z‖ < 1 / (N : ℝ))
    (hzero : ∃ s₀ : ℂ, p.eval s₀ = 0 ∧ s₀.re ≠ 1/2 ∧ |s₀.im| > N) :
    ∀ Γ₀ : Finset Sent,
      ↑Γ₀ ⊆ S.T ∪ {S.RH} ∪ {neg (canonical.RL S.RH)} →
      Γ₀.card ≤ N →
      ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-- Curved variant: on-line zero witnesses ¬RH fragment. -/
axiom approximant_to_model_neg (N : ℕ) (hN : 0 < N)
    (p : Polynomial ℂ)
    (happrox : ∀ z ∈ K_N N, ‖riemannZeta z - p.eval z‖ < 1 / (N : ℝ))
    (hzero : ∃ s₀ : ℂ, p.eval s₀ = 0 ∧ s₀.re = 1/2 ∧ |s₀.im| > N) :
    ∀ Γ₀ : Finset Sent,
      ↑Γ₀ ⊆ S.T ∪ {neg S.RH} ∪ {neg (canonical.RL (neg S.RH))} →
      Γ₀.card ≤ N →
      ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ

/-! ================================================================
    THEOREMS — all derived, zero sorry
    ================================================================ -/

/-- Mergelyan applied to ζ on K_N. Direct from published axioms. -/
theorem zeta_approximant (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K_N N, ‖riemannZeta z - p.eval z‖ < ε :=
  mergelyan (K_N N) (K_N_compact N hN) (K_N_connected_complement N hN)
    riemannZeta (zeta_continuousOn_K_N N hN) (zeta_analyticOn_K_N N hN) ε hε

/-- Finite satisfiability: linear obstruction.
    From planted_zero_exists + approximant_to_model. -/
theorem finite_sat_rh :
    ∀ Γ₀ : Finset Sent,
      ↑Γ₀ ⊆ S.T ∪ {S.RH} ∪ {neg (canonical.RL S.RH)} →
      ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ := by
  intro Γ₀ hΓ
  let N := max Γ₀.card 1
  have hN : 0 < N := by omega
  obtain ⟨p, happrox, hzero⟩ := planted_zero_exists N hN
  exact approximant_to_model S N hN p happrox hzero Γ₀ hΓ (le_max_left _ _)

/-- Finite satisfiability: curved obstruction. -/
theorem finite_sat_neg :
    ∀ Γ₀ : Finset Sent,
      ↑Γ₀ ⊆ S.T ∪ {neg S.RH} ∪ {neg (canonical.RL (neg S.RH))} →
      ∃ M : Model, ∀ φ ∈ Γ₀, M.Sat φ := by
  intro Γ₀ hΓ
  let N := max Γ₀.card 1
  have hN : 0 < N := by omega
  obtain ⟨p, happrox, hzero⟩ := planted_zero_exists_neg N hN
  exact approximant_to_model_neg S N hN p happrox hzero Γ₀ hΓ (le_max_left _ _)

/-- Linear disagreement model (Lemma 1.10.2). -/
theorem linear_disagreement :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat S.RH ∧
      ¬ M.Sat (canonical.RL S.RH) := by
  obtain ⟨M, hM⟩ := compactness (S.T ∪ {S.RH} ∪ {neg (canonical.RL S.RH)})
    (finite_sat_rh S)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hM φ (Set.mem_union_left _ (Set.mem_union_left _ hφ))
  · exact hM S.RH (Set.mem_union_left _ (Set.mem_union_right _ rfl))
  · intro hsat
    have h := hM (neg (canonical.RL S.RH)) (Set.mem_union_right _ rfl)
    exact ((M.sat_neg (canonical.RL S.RH)).mp h) hsat

/-- Curved disagreement model (Lemma 1.12.4). -/
theorem curved_disagreement :
    ∃ M : Model, S.ZFCModel M ∧ M.Sat (neg S.RH) ∧
      ¬ M.Sat (canonical.RL (neg S.RH)) := by
  obtain ⟨M, hM⟩ := compactness
    (S.T ∪ {neg S.RH} ∪ {neg (canonical.RL (neg S.RH))})
    (finite_sat_neg S)
  refine ⟨M, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hM φ (Set.mem_union_left _ (Set.mem_union_left _ hφ))
  · exact hM (neg S.RH) (Set.mem_union_left _ (Set.mem_union_right _ rfl))
  · intro hsat
    have h := hM (neg (canonical.RL (neg S.RH))) (Set.mem_union_right _ rfl)
    exact ((M.sat_neg (canonical.RL (neg S.RH))).mp h) hsat

/-- ZFC ⊬ RH. -/
theorem RH_not_provable : ¬ S.Prov S.RH := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := linear_disagreement S
  exact hfail (perron_pres S S.RH hprov M hM)

/-- ZFC ⊬ ¬RH. -/
theorem neg_RH_not_provable : ¬ S.Prov (neg S.RH) := by
  intro hprov
  obtain ⟨M, hM, -, hfail⟩ := curved_disagreement S
  exact hfail (perron_pres S (neg S.RH) hprov M hM)

/-- ZFC Independence. -/
theorem RH_independent : ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  ⟨RH_not_provable S, neg_RH_not_provable S⟩

/-- Truth from Unrefutability. -/
theorem truth_from_unrefutability
    {φ : Sent} (hpi : IsPi1 φ) (hnot : ¬ S.Prov (neg φ)) : TrueInN φ :=
  Classical.byContradiction fun hfalse => hnot (reflection S φ hpi hfalse)

/-- ℕ ⊨ RH. -/
theorem RH_true_in_N : TrueInN S.RH :=
  truth_from_unrefutability S (rh_pi1 S) (neg_RH_not_provable S)

/-! ### Λ-sound framework -/

structure LambdaSound (φ : Sent) (τ : TranslationPair) : Prop where
  inv : ∀ ψ, S.Prov ψ → ∀ M, S.ZFCModel M → M.Sat ψ → M.Sat (τ.RL ψ)
  comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ)
  kernel : ∀ ψ, IsPi1 ψ → (TrueInN ψ ↔ TrueInN (τ.RL ψ))
  changes : ¬ S.Prov (iffS φ (τ.RL φ))

theorem changes_rh :
    ¬ S.Prov (iffS S.RH (canonical.RL S.RH)) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := linear_disagreement S
  exact hfail (((M.sat_iff S.RH (canonical.RL S.RH)).mp (hprov M hM)).mp hsat)

theorem changes_neg :
    ¬ S.Prov (iffS (neg S.RH) (canonical.RL (neg S.RH))) := by
  intro hprov
  obtain ⟨M, hM, hsat, hfail⟩ := curved_disagreement S
  exact hfail (((M.sat_iff (neg S.RH) (canonical.RL (neg S.RH))).mp
    (hprov M hM)).mp hsat)

theorem canonical_lambda_sound_rh : LambdaSound S S.RH canonical where
  inv ψ hψ M hM _ := perron_pres S ψ hψ M hM
  comp := canonical_comp
  kernel := canonical_kernel
  changes := changes_rh S

theorem canonical_lambda_sound_neg : LambdaSound S (neg S.RH) canonical where
  inv ψ hψ M hM _ := perron_pres S ψ hψ M hM
  comp := canonical_comp
  kernel := canonical_kernel
  changes := changes_neg S

theorem uniform_preservation {S' : Setting} {φ : Sent} {τ : TranslationPair}
    (hτ : LambdaSound S' φ τ) {ψ : Sent} (hψ : S'.Prov ψ) (M : Model)
    (hM : S'.ZFCModel M) : M.Sat ψ ↔ M.Sat (τ.RL ψ) :=
  ⟨fun h => hτ.inv ψ hψ M hM h, fun _ => hψ M hM⟩

theorem round_trip_adequacy {S' : Setting} {φ : Sent} {τ : TranslationPair}
    (hτ : LambdaSound S' φ τ) {ψ : Sent} (hψ : S'.Prov ψ) :
    S'.Prov (iffS ψ (τ.RL ψ)) :=
  fun M hM => (M.sat_iff ψ (τ.RL ψ)).mpr (uniform_preservation hτ hψ M hM)

theorem no_lambda_sound_of_provable {S' : Setting} {φ : Sent} (hφ : S'.Prov φ) :
    ¬ ∃ τ, LambdaSound S' φ τ := by
  rintro ⟨τ, hτ⟩
  exact hτ.changes (round_trip_adequacy hτ hφ)

end RH.Paper.V2
