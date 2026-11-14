import RH.Paper.Arith
import Mathlib.ModelTheory.Satisfiability
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

/-- The first-order shape in Lemma 1.7.12. The variables are the candidate
    zero index and the precision, in that order. -/
def precisionSentence (check : L.BoundedFormula Empty 2) : Sent :=
  check.all.all

/-- Failure of the precision sentence supplies an actual failing pair
    in the model. -/
theorem Model.not_sat_precisionSentence (M : Model)
    (check : L.BoundedFormula Empty 2) :
    ¬ M.Sat (precisionSentence check) ↔
      ∃ n k : M.carrier, ¬ @Language.BoundedFormula.Realize L M.carrier M.str
        Empty 2 check (fun e => Empty.elim e) (Fin.snoc (Fin.snoc Fin.elim0 n) k) := by
  classical
  letI := M.str
  change (¬ ∀ n k : M.carrier, check.Realize (default : Empty → M.carrier)
    (Fin.snoc (Fin.snoc (default : Fin 0 → M.carrier) n) k)) ↔ _
  have emptyAssignment : (default : Empty → M.carrier) = fun e => Empty.elim e :=
    funext (fun e => nomatch e)
  have noBoundVariables : (default : Fin 0 → M.carrier) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  rw [emptyAssignment, noBoundVariables]
  simp only [not_forall]

/-- An extra unbounded universal variable alone can leave the truth
    value unchanged. This applies to nonstandard models as well. -/
theorem Model.sat_vacuous_precision (M : Model) (check : L.BoundedFormula Empty 1)
    [Nonempty M.carrier] :
    M.Sat (precisionSentence (check.liftAt 1 1)) ↔ M.Sat check.all := by
  letI := M.str
  change (∀ n : M.carrier, ((check.liftAt 1 1).all).Realize
    (default : Empty → M.carrier) (Fin.snoc (default : Fin 0 → M.carrier) n)) ↔
    ∀ n : M.carrier, check.Realize (default : Empty → M.carrier)
      (Fin.snoc (default : Fin 0 → M.carrier) n)
  simp only [Language.BoundedFormula.realize_all_liftAt_one_self]

/-- If the standard model satisfies the precision sentence, any model of
    its complete theory satisfies it too. A nonstandard element by itself
    cannot witness the failure required by Lemma 1.10.2. -/
theorem Model.sat_precision_of_completeTheory (M : Model)
    (hM : ∀ φ ∈ L.completeTheory ℕ, M.Sat φ)
    (check : L.BoundedFormula Empty 2) (hcheck : TrueInN (precisionSentence check)) :
    M.Sat (precisionSentence check) :=
  hM _ (Language.mem_completeTheory.mpr hcheck)

/-- In the standard arithmetic structure, the finite fragment consisting
    just of the negated precision sentence already requires a failing
    pair. Compare the finite satisfiability step in Lemma 1.10.2. -/
theorem not_trueInN_neg_precisionSentence (check : L.BoundedFormula Empty 2)
    (hcheck : TrueInN (precisionSentence check)) :
    ¬ TrueInN (neg (precisionSentence check)) :=
  fun hneg => ((Model.sat_neg ⟨ℕ, natStructure⟩ (precisionSentence check)).mp hneg) hcheck

/-- The finite satisfiability argument in Lemma 1.10.2 cannot use the
    standard model for the singleton containing the negated precision
    sentence if all its checks succeed there. -/
theorem not_finitely_satisfied_in_N (check : L.BoundedFormula Empty 2)
    (hcheck : TrueInN (precisionSentence check)) :
    ¬ (∀ Γ : Finset Sent, (Γ : L.Theory) ⊆ insert (neg (precisionSentence check)) S.T →
      ∀ φ ∈ Γ, TrueInN φ) := by
  classical
  intro h
  let bad := neg (precisionSentence check)
  have subset : (({bad} : Finset Sent) : L.Theory) ⊆ insert bad S.T := by
    intro φ hφ
    have heq : φ = bad := Finset.mem_singleton.mp hφ
    exact heq ▸ Set.mem_insert bad S.T
  exact not_trueInN_neg_precisionSentence check hcheck
    (h {bad} subset bad (Finset.mem_singleton.mpr rfl))

/-- Mathlib's compactness theorem gives a model of the target theory that
    falsifies a sentence when adjoining its negation is finitely satisfiable. -/
theorem sentence_failure_of_finite_satisfiability {φ : Sent}
    (finite : (insert (neg φ) S.T).IsFinitelySatisfiable) :
    ∃ M : Model, S.ZFCModel M ∧ ¬ M.Sat φ := by
  let T := insert (neg φ) S.T
  have satisfiable : T.IsSatisfiable :=
    Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr finite
  obtain ⟨N⟩ := satisfiable
  let M : Model := ⟨N.Carrier, inferInstance⟩
  have hneg : M.Sat (neg φ) :=
    Language.Theory.realize_sentence_of_mem (M := N.Carrier)
      (T := T) (Set.mem_insert _ _)
  refine ⟨M, fun ψ hψ => ?_, (M.sat_neg φ).mp hneg⟩
  exact Language.Theory.realize_sentence_of_mem (M := N.Carrier)
    (T := T) (Set.mem_insert_of_mem _ hψ)

/-- The finite-satisfiability claim is equivalent to non-entailment of
    the sentence over the target theory. Every arithmetic model is
    nonempty because it interprets the constant zero. -/
theorem finitely_satisfiable_neg_iff_not_provable (φ : Sent) :
    (insert (neg φ) S.T).IsFinitelySatisfiable ↔ ¬ S.Prov φ := by
  classical
  constructor
  · intro finite hprov
    obtain ⟨M, hM, hfail⟩ := sentence_failure_of_finite_satisfiability S finite
    exact hfail (hprov M hM)
  · intro hnot
    have witness : ∃ M : Model, S.ZFCModel M ∧ ¬ M.Sat φ := by
      by_contra h
      apply hnot
      intro M hM
      exact Classical.byContradiction (fun hfail => h ⟨M, hM, hfail⟩)
    obtain ⟨M, hM, hfail⟩ := witness
    letI : L.Structure M.carrier := M.str
    letI : Nonempty M.carrier := ⟨M.str.funMap zeroFunc (fun i => Fin.elim0 i)⟩
    let T := insert (neg φ) S.T
    letI : T.Model M.carrier :=
      ⟨fun ψ hψ => by
        rcases Set.mem_insert_iff.mp hψ with hneg | hbase
        · subst ψ
          exact (M.sat_neg φ).mpr hfail
        · exact hM ψ hbase⟩
    exact (Language.Theory.Model.isSatisfiable (T := T) M.carrier).isFinitelySatisfiable

/-- A two-variable precision matrix can succeed at every input in every
    model. Its quantifier shape gives no counterexample, even at a
    nonstandard input. -/
theorem precision_shape_does_not_imply_finite_satisfiability
    (check : L.BoundedFormula Empty 2) :
    ¬ (insert (neg (precisionSentence (check.imp check))) S.T).IsFinitelySatisfiable := by
  intro finite
  apply (finitely_satisfiable_neg_iff_not_provable S _).mp finite
  intro M _
  letI : L.Structure M.carrier := M.str
  change ∀ n k : M.carrier, check.Realize _ _ → check.Realize _ _
  exact fun _ _ h => h

theorem round_trip_failure_of_finite_satisfiability {τ : TranslationPair} {φ : Sent}
    (finite : (insert (neg (τ.RL φ)) S.T).IsFinitelySatisfiable) :
    S.RoundTripFails τ φ :=
  sentence_failure_of_finite_satisfiability S finite

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

/-- The linear deduction with the precision formula left abstract.
    The identification of the round trip with the precision sentence
    is required only in models of the target theory. -/
theorem RH_not_provable_of_finite_precision_failure {τ : TranslationPair}
    (check : L.BoundedFormula Empty 2)
    (roundTrip : S.Prov (iffS (τ.RL S.RH) (precisionSentence check)))
    (pres : S.Prov S.RH → S.Prov (τ.RL S.RH))
    (finite : (insert (neg (precisionSentence check)) S.T).IsFinitelySatisfiable) :
    ¬ S.Prov S.RH := by
  obtain ⟨M, hM, hfail⟩ := sentence_failure_of_finite_satisfiability S finite
  have agreement := (M.sat_iff (τ.RL S.RH) (precisionSentence check)).mp (roundTrip M hM)
  exact RH_not_provable S pres ⟨M, hM, fun h => hfail (agreement.mp h)⟩

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

/-- The two directions also follow from preservation for RH and a
    single model satisfying RH while falsifying its round trip. -/
theorem RH_independent_of_disagreement {τ : TranslationPair}
    (pres : S.Prov S.RH → S.Prov (τ.RL S.RH))
    (disagreement : S.Disagrees τ S.RH) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) := by
  obtain ⟨M, hM, hRH, hfail⟩ := disagreement
  exact ⟨RH_not_provable S pres ⟨M, hM, hfail⟩,
    fun hneg => ((M.sat_neg S.RH).mp (hneg M hM)) hRH⟩

/-- The compactness step of Lemma 1.10.2 with the original RH sentence
    included in the theory and the precision matrix left abstract. -/
theorem RH_disagrees_of_finite_precision_failure {τ : TranslationPair}
    (check : L.BoundedFormula Empty 2)
    (roundTrip : S.Prov (iffS (τ.RL S.RH) (precisionSentence check)))
    (finite : (insert (neg (precisionSentence check)) (insert S.RH S.T)).IsFinitelySatisfiable) :
    S.Disagrees τ S.RH := by
  let extended : Setting := { S with T := insert S.RH S.T }
  obtain ⟨M, hExtended, hfail⟩ := sentence_failure_of_finite_satisfiability extended finite
  have hBase : S.ZFCModel M := fun ψ hψ => hExtended ψ (Set.mem_insert_of_mem _ hψ)
  have hRH : M.Sat S.RH := hExtended S.RH (Set.mem_insert _ _)
  have agreement := (M.sat_iff (τ.RL S.RH) (precisionSentence check)).mp (roundTrip M hBase)
  exact ⟨M, hBase, hRH, fun h => hfail (agreement.mp h)⟩

/-- The exact finite-satisfiability obligation of the linear argument,
    expressed as a semantic consequence test in the original theory. -/
theorem RH_finite_precision_failure_iff (check : L.BoundedFormula Empty 2) :
    (insert (neg (precisionSentence check)) (insert S.RH S.T)).IsFinitelySatisfiable ↔
      ¬ S.Prov (impS S.RH (precisionSentence check)) := by
  let extended : Setting := { S with T := insert S.RH S.T }
  have entailment : extended.Prov (precisionSentence check) ↔
      S.Prov (impS S.RH (precisionSentence check)) := by
    constructor
    · intro h M hBase
      apply (M.sat_imp _ _).mpr
      intro hRH
      apply h M
      intro ψ hψ
      rcases Set.mem_insert_iff.mp hψ with heq | hmem
      · exact heq ▸ hRH
      · exact hBase ψ hmem
    · intro h M hExtended
      have hBase : S.ZFCModel M := fun ψ hψ => hExtended ψ (Set.mem_insert_of_mem _ hψ)
      exact (M.sat_imp _ _).mp (h M hBase) (hExtended S.RH (Set.mem_insert _ _))
  exact (finitely_satisfiable_neg_iff_not_provable extended _).trans (not_congr entailment)

/-- The single-model deduction from the full compactness premise. -/
theorem RH_independent_of_finite_precision_failure {τ : TranslationPair}
    (check : L.BoundedFormula Empty 2)
    (roundTrip : S.Prov (iffS (τ.RL S.RH) (precisionSentence check)))
    (pres : S.Prov S.RH → S.Prov (τ.RL S.RH))
    (finite : (insert (neg (precisionSentence check)) (insert S.RH S.T)).IsFinitelySatisfiable) :
    ¬ S.Prov S.RH ∧ ¬ S.Prov (neg S.RH) :=
  RH_independent_of_disagreement S pres (RH_disagrees_of_finite_precision_failure S check roundTrip finite)

/-! ### The fresh constant in Lemma 1.10.2 -/

/-- The formula `∃ k, ¬check(n,k)` with its index exposed as a free variable. -/
def failedPrecisionAt (check : L.BoundedFormula Empty 2) : L.Formula Unit :=
  (check.not.ex.toFormula).relabel (fun _ => ())

/-- In the expanded language, the free index is named by the new constant. -/
def namedPrecisionFailure (check : L.BoundedFormula Empty 2) : L[[Unit]].Sentence :=
  Language.Formula.equivSentence (failedPrecisionAt check)

/-- The expanded theory containing RH_L and the sentence asserting a
    failed check at the newly named index. -/
def Setting.precisionFailureTheory (check : L.BoundedFormula Empty 2) : L[[Unit]].Theory :=
  insert (namedPrecisionFailure check) ((L.lhomWithConstants Unit).onTheory (insert S.RH S.T))

theorem Model.realize_failedPrecisionAt (M : Model) (check : L.BoundedFormula Empty 2)
    (n : M.carrier) :
    @Language.Formula.Realize L M.carrier M.str Unit (failedPrecisionAt check) (fun _ => n) ↔
      ∃ k : M.carrier, ¬ @Language.BoundedFormula.Realize L M.carrier M.str
        Empty 2 check (fun e => Empty.elim e) (Fin.snoc (Fin.snoc Fin.elim0 n) k) := by
  letI : L.Structure M.carrier := M.str
  unfold failedPrecisionAt
  rw [Language.Formula.realize_relabel, Language.BoundedFormula.realize_toFormula,
    Language.BoundedFormula.realize_ex]
  change (∃ k : M.carrier, check.not.Realize (fun _ : Empty => n)
    (Fin.snoc (fun _ : Fin 1 => n) k)) ↔ _
  have freeAssignment : (fun _ : Empty => n) = fun e => Empty.elim e :=
    funext (fun e => nomatch e)
  have indexAssignment : (fun _ : Fin 1 => n) = Fin.snoc Fin.elim0 n := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [freeAssignment, indexAssignment]
  simp only [Language.BoundedFormula.realize_not]

/-- If every precision check holds in ℕ, every interpretation of the
    fresh constant in ℕ falsifies the added failure sentence. -/
theorem named_precision_failure_false_in_N (check : L.BoundedFormula Empty 2)
    (hcheck : TrueInN (precisionSentence check)) (n : ℕ) :
    ¬ @Language.Sentence.Realize (L[[Unit]]) ℕ
      (@Language.withConstantsStructure L ℕ natStructure Unit
        (Language.constantsOn.structure (fun _ => n))) (namedPrecisionFailure check) := by
  letI := Language.constantsOn.structure (fun _ : Unit => n)
  intro named
  have failed := (Language.Formula.realize_equivSentence ℕ (failedPrecisionAt check)).mp named
  let M : Model := ⟨ℕ, natStructure⟩
  have atIndex : @Language.Formula.Realize L ℕ natStructure Unit
      (failedPrecisionAt check) (fun _ => n) := by
    simpa only [show (fun a : Unit => (L.con a : ℕ)) = (fun _ => n) from rfl] using failed
  obtain ⟨k, hk⟩ := (M.realize_failedPrecisionAt check n).mp atIndex
  exact (M.not_sat_precisionSentence check).mpr ⟨n, k, hk⟩ hcheck

/-- Compactness in the expanded language, followed by forgetting the
    fresh constant. Any finitely satisfiable extension supplies the same
    deduction, including extensions with additional conditions on the index. -/
theorem RH_disagrees_of_named_precision_failure {τ : TranslationPair}
    (check : L.BoundedFormula Empty 2)
    (roundTrip : S.Prov (iffS (τ.RL S.RH) (precisionSentence check)))
    {Γ : L[[Unit]].Theory} (includes : S.precisionFailureTheory check ⊆ Γ)
    (finite : Γ.IsFinitelySatisfiable) :
    S.Disagrees τ S.RH := by
  have sat := Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr finite
  obtain ⟨N⟩ := sat
  let incl := L.lhomWithConstants Unit
  letI : L.Structure N.Carrier := incl.reduct N.Carrier
  let M : Model := ⟨N.Carrier, incl.reduct N.Carrier⟩
  have base (φ : Sent) (hφ : φ ∈ insert S.RH S.T) : M.Sat φ := by
    apply (incl.realize_onSentence (M := N.Carrier) φ).mp
    apply Language.Theory.realize_sentence_of_mem Γ
    exact includes (Set.mem_insert_of_mem _ (Language.LHom.mem_onTheory.mpr ⟨φ, hφ, rfl⟩))
  have named : N.Carrier ⊨ namedPrecisionFailure check :=
    Language.Theory.realize_sentence_of_mem Γ (includes (Set.mem_insert _ _))
  have failed := (Language.Formula.realize_equivSentence N.Carrier (failedPrecisionAt check)).mp named
  have hfail : ¬ M.Sat (precisionSentence check) := by
    apply (M.not_sat_precisionSentence check).mpr
    let n : M.carrier := L.con ()
    have atIndex : @Language.Formula.Realize L M.carrier M.str Unit
        (failedPrecisionAt check) (fun _ => n) := by
      have same : (fun a : Unit => (L.con a : M.carrier)) = fun _ => n :=
        funext (fun a => by cases a; rfl)
      simpa only [same] using failed
    obtain ⟨k, hk⟩ := (M.realize_failedPrecisionAt check n).mp atIndex
    exact ⟨n, k, hk⟩
  have hBase : S.ZFCModel M := fun φ hφ => base φ (Set.mem_insert_of_mem _ hφ)
  have hRH : M.Sat S.RH := base S.RH (Set.mem_insert _ _)
  have agreement := (M.sat_iff (τ.RL S.RH) (precisionSentence check)).mp (roundTrip M hBase)
  exact ⟨M, hBase, hRH, fun h => hfail (agreement.mp h)⟩

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

/-- Negation reverses the truth values of the two sentences in the
    disagreement model, so the biconditional for ¬RH also fails there. -/
theorem changes_neg_of_RH_disagreement {τ : TranslationPair}
    (comp : ∀ ψ, τ.toC (neg ψ) = neg (τ.toC ψ) ∧ τ.toL (neg ψ) = neg (τ.toL ψ))
    (disagreement : S.Disagrees τ S.RH) :
    ¬ S.Prov (iffS (neg S.RH) (τ.RL (neg S.RH))) := by
  intro hprov
  obtain ⟨M, hM, hRH, hfail⟩ := disagreement
  have roundTripNeg : τ.RL (neg S.RH) = neg (τ.RL S.RH) := by
    unfold TranslationPair.RL
    rw [(comp S.RH).1, (comp (τ.toC S.RH)).2]
  have htranslated : M.Sat (τ.RL (neg S.RH)) := by
    rw [roundTripNeg]
    exact (M.sat_neg (τ.RL S.RH)).mpr hfail
  have hiff := (M.sat_iff (neg S.RH) (τ.RL (neg S.RH))).mp (hprov M hM)
  exact ((M.sat_neg S.RH).mp (hiff.mpr htranslated)) hRH

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
