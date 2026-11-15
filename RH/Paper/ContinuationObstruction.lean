import RH.Paper.ProofI
import RH.Paper.RationalApproximation

open FirstOrder

namespace RH.Paper.PlantedZero

/-- The continuation code, its local validity check, and its zero check. -/
def certificateLanguage : Language.{0, 0} :=
  ⟨fun | 0 => Unit | _ + 1 => Empty, fun | 2 | 3 => Unit | _ => Empty⟩

abbrev ObstructionLanguage := L.sum certificateLanguage

private def code {v : Type} : ObstructionLanguage.Term v :=
  .func ((show ObstructionLanguage.Functions 0 from Sum.inr ())) Fin.elim0

private def numeral {v : Type} : ℕ → ObstructionLanguage.Term v
  | 0 => .func (Sum.inl zeroFunc) Fin.elim0
  | n + 1 => .func (Sum.inl succFunc) ![numeral n]

/-- Each standard instance asserts a lower bound on the code and local validity. -/
def standardCheck (k : ℕ) : ObstructionLanguage.Sentence :=
  (Language.BoundedFormula.rel (Sum.inl leRel) ![code, numeral k]).not ⊓
    (Language.BoundedFormula.rel (show ObstructionLanguage.Relations 2 from Sum.inr ()) ![code, numeral k])

/-- The named code passes at every candidate zero and precision. -/
def globalZeroCheck : ObstructionLanguage.Sentence :=
  (Language.BoundedFormula.rel (show ObstructionLanguage.Relations 3 from Sum.inr ())
    ![code, Language.Term.var (Sum.inr (0 : Fin 2)),
      Language.Term.var (Sum.inr (1 : Fin 2))]).all.all

/-- The named code fails at some candidate zero and precision. -/
def zeroCheckFailure : ObstructionLanguage.Sentence := globalZeroCheck.not

/-- A local validity stage uses a compatible Taylor family and a finite
    Dirichlet sum on the checked regions. -/
def localValidity (K D : ℕ → Set ℂ) (m k : ℕ) : Prop :=
  ∃ (f : RationalFunction) (p : Polynomial ℂ) (J : ℕ), Encodable.encode f = m ∧
    (∀ z ∈ K k, ‖evalComplex f z - riemannZeta z‖ < (1 / 2 : ℝ) ^ k) ∧
    (∀ a z : ℂ, (p.comp (Polynomial.X + Polynomial.C a)).eval (z - a) =
      evalComplex f z) ∧
    (∀ z ∈ D k, ‖evalComplex f z - (∑ j ∈ Finset.range J, LSeries.term 1 z j)‖ <
      (1 / 2 : ℝ) ^ k)

private def certificateStructure (K D : ℕ → Set ℂ) (m : ℕ) :
    certificateLanguage.Structure ℕ where
  funMap := fun {n} f _ => match n, f with
    | 0, _ => m
    | _ + 1, f => nomatch f
  RelMap := fun {n} r x => match n, r with
    | 2, _ => localValidity K D (x 0) (x 1)
    | 3, _ => passes (x 0) (x 1) (x 2)
    | 0, r | 1, r | _ + 4, r => nomatch r

private theorem realize_numeral {v : Type} [certificateLanguage.Structure ℕ]
    (x : v → ℕ) (k : ℕ) : (numeral k).realize x = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (numeral k).realize x + 1 = k + 1
    rw [ih]

def obstructionTheory (T : L.Theory) : ObstructionLanguage.Theory :=
  insert zeroCheckFailure ((Language.LHom.sumInl : L →ᴸ ObstructionLanguage).onTheory T ∪
    Set.range standardCheck)

/-- Compactness for the explicitly defined finite analytic checks in the
    expanded language. The analytic witness satisfies each finite prefix in
    the standard structure. This theorem does not identify the new relation
    symbols with formulas in the original arithmetic language. -/
theorem continuation_obstruction (T : L.Theory)
    (standard : ∀ φ ∈ T, TrueInN φ)
    (K D : ℕ → Set ℂ) (growsK : Monotone K) (growsD : Monotone D)
    (compactK : ∀ N, IsCompact (K N)) (connected : ∀ N, IsConnected (K N)ᶜ)
    (poleOutside : ∀ N, (1 : ℂ) ∉ K N)
    (zerosOutside : ∀ N, ∀ w ∈ plantedRoots N, w.toComplex ∉ K N)
    (compactD : ∀ N, IsCompact (D N)) (contained : ∀ N, D N ⊆ K N)
    (convergence : ∀ N, ∀ z ∈ D N, 1 < z.re) :
    (obstructionTheory T).IsSatisfiable := by
  classical
  let base := insert zeroCheckFailure
    ((Language.LHom.sumInl : L →ᴸ ObstructionLanguage).onTheory T)
  change (insert zeroCheckFailure
    ((Language.LHom.sumInl : L →ᴸ ObstructionLanguage).onTheory T ∪
      Set.range standardCheck)).IsSatisfiable
  rw [← Set.insert_union]
  by_contra h
  obtain ⟨N, bad⟩ := (standard_checks_unsatisfiable_iff_finite_prefix
    base standardCheck).mp h
  obtain ⟨f, p, J, large, near, charts, dirichlet, failure⟩ :=
    finite_taylor_dirichlet_checks_with_standard_failure (K N) N
      (compactK N) (connected N) (poleOutside N) (zerosOutside N)
      (D N) (compactD N) (contained N) (convergence N)
  letI : certificateLanguage.Structure ℕ := certificateStructure K D (Encodable.encode f)
  apply bad
  have model : ℕ ⊨ base ∪ standardCheck '' Set.Iic N := by
    constructor
    intro ψ hψ
    rcases hψ with hbase | ⟨k, hk, rfl⟩
    · rcases hbase with rfl | hT
      · change zeroCheckFailure.Realize ℕ
        unfold zeroCheckFailure globalZeroCheck
        rw [Language.Sentence.realize_not]
        intro all
        change ∀ n k : ℕ, passes (Encodable.encode f) n k at all
        exact failure (all (Encodable.encode (plantedPoint N)) 3)
      · obtain ⟨φ, hφ, rfl⟩ := Language.LHom.mem_onTheory.mp hT
        exact (Language.LHom.realize_onSentence ℕ Language.LHom.sumInl φ).mpr (standard φ hφ)
    · have hk' : k ≤ N := hk
      change (standardCheck k).Realize ℕ
      unfold Language.Sentence.Realize Language.Formula.Realize standardCheck
      rw [Language.BoundedFormula.realize_inf, Language.BoundedFormula.realize_not]
      simp only [Language.BoundedFormula.Realize]
      rw [show Language.Structure.RelMap (L := ObstructionLanguage) (M := ℕ) (Sum.inl leRel) =
        (fun (x : Fin 2 → ℕ) => x 0 ≤ x 1) from rfl]
      rw [show Language.Structure.RelMap (L := ObstructionLanguage) (M := ℕ)
        (show ObstructionLanguage.Relations 2 from Sum.inr ()) =
          (fun (x : Fin 2 → ℕ) => localValidity K D (x 0) (x 1)) from rfl]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have codeValue (x : Empty ⊕ Fin 0 → ℕ) : code.realize x = Encodable.encode f := rfl
      simp only [codeValue, realize_numeral]
      refine ⟨not_le_of_gt (hk'.trans_lt large), f, p, J, rfl, ?_, charts, ?_⟩
      · intro z hz
        exact (near z (growsK hk' hz)).trans_le
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk')
      · exact fun z hz => dirichlet k hk' z (growsD hk' hz)
  letI := model
  exact Language.Theory.Model.isSatisfiable ℕ

/-- Positive existential output of the construction: a model of the base
theory satisfying every standard local check and falsifying the global check.
Failure is the target conclusion. The predicates here belong to the expanded
language; no identification with RH or its canonical round trip is asserted. -/
theorem continuation_failure_witness (T : L.Theory)
    (standard : ∀ φ ∈ T, TrueInN φ)
    (K D : ℕ → Set ℂ) (growsK : Monotone K) (growsD : Monotone D)
    (compactK : ∀ N, IsCompact (K N)) (connected : ∀ N, IsConnected (K N)ᶜ)
    (poleOutside : ∀ N, (1 : ℂ) ∉ K N)
    (zerosOutside : ∀ N, ∀ w ∈ plantedRoots N, w.toComplex ∉ K N)
    (compactD : ∀ N, IsCompact (D N)) (contained : ∀ N, D N ⊆ K N)
    (convergence : ∀ N, ∀ z ∈ D N, 1 < z.re) :
    ∃ M : Language.Theory.ModelType.{0, 0, 0}
        ((Language.LHom.sumInl : L →ᴸ ObstructionLanguage).onTheory T),
      (∀ k : ℕ, M.Carrier ⊨ standardCheck k) ∧ ¬ (M.Carrier ⊨ globalZeroCheck) := by
  obtain ⟨M⟩ := continuation_obstruction T standard K D growsK growsD compactK
    connected poleOutside zerosOutside compactD contained convergence
  let B := M.subtheoryModel
    (T' := (Language.LHom.sumInl : L →ᴸ ObstructionLanguage).onTheory T)
    (fun _ h => Set.mem_insert_of_mem _ (Or.inl h))
  refine ⟨B, ?_, ?_⟩
  · intro k
    exact Language.Theory.realize_sentence_of_mem (T := obstructionTheory T)
      (Set.mem_insert_of_mem _ (Or.inr ⟨k, rfl⟩))
  · have failure : M.Carrier ⊨ zeroCheckFailure :=
      Language.Theory.realize_sentence_of_mem (T := obstructionTheory T) (Set.mem_insert _ _)
    exact (Language.Sentence.realize_not M.Carrier (φ := globalZeroCheck)).mp failure

end RH.Paper.PlantedZero
