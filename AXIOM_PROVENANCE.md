# Provenance of the Lean formalization

`RH/Paper/Arith.lean` defines the arithmetic language, its standard model,
and bounded formulas. `RH/Paper/ProofI.lean` checks the deductions below.
Both files use Mathlib's first-order semantics and declare no custom
axioms.

Section and theorem numbers below refer to Nielsen and Semita's
32-page manuscript with the May 16, 2026 update (`OLDGOODRIEMANN.pdf`).

| Deduction | Explicit premises |
|---|---|
| `Model.not_sat_precisionSentence` | None. Failure of the sentence in Lemma 1.7.12 is equivalent to the existence of a candidate index and precision at which the matrix fails. |
| `Model.sat_vacuous_precision` | A nonempty model. Adding a universal precision variable unused by the matrix preserves satisfaction. |
| `Model.sat_precision_of_completeTheory` | The precision sentence holds in ℕ and the model satisfies the complete theory of ℕ. This verifies that adjoining a nonstandard parameter using the complete theory alone cannot give a failing check. |
| `not_finitely_satisfied_in_N` | The precision sentence holds in ℕ. The singleton containing its negation cannot be satisfied in ℕ. |
| `finitely_satisfiable_neg_iff_not_provable` | None. Adjoining the negation of a sentence is finitely satisfiable exactly when the original theory does not entail the sentence. |
| `precision_shape_does_not_imply_finite_satisfiability` | None. For any two-variable matrix `check`, the matrix `check → check` gives a precision sentence whose negation is unsatisfiable over any arithmetic theory. |
| `round_trip_failure_of_finite_satisfiability` | Finite satisfiability of the theory with the negated round trip added, using Mathlib's compactness theorem |
| `RH_not_provable_of_finite_precision_failure` | The round trip is equivalent over the target theory to the abstract precision sentence, preservation holds for RH_L, and adjoining the negated precision sentence is finitely satisfiable. |
| `RH_not_provable` | Preservation for RH_L (Lemma 1.5.6) and failure in a model of the target theory (Lemma 1.10.2 and Corollary 1.7.14) |
| `neg_RH_not_provable` | Preservation and round-trip failure for ¬RH_L in the target theory |
| `RH_independent` | Preservation and round-trip failure for both polarities (Corollary 1.13.2) |
| `RH_independent_of_disagreement` | Preservation for RH_L and one model satisfying RH_L while falsifying its round trip |
| `changes_rh` and `changes_neg` | A model satisfying the original sentence and falsifying its round trip |
| `changes_neg_of_RH_disagreement` | Commutation with negation and a model satisfying RH_L while falsifying its round trip. This is a consequence about the arithmetic biconditional. Lemma 1.12.4 concerns the analytic round trip. |
| `lambda_sound_of_disagreement` | Preservation, commutation with negation, Π₁ truth preservation in ℕ, and disagreement |
| `RH_true_in_N` | The Π₁ form, reflection for the given theory (via Σ₁-completeness for ZFC), and unrefutability |
| `uniform_preservation` and `round_trip_adequacy` | Λ-soundness and provability of the input sentence |

Jenny Lorraine Nielsen observed that unprovability uses only round-trip
failure in an eligible model. The deduction applies preservation to
whichever model witnesses the existential premise. The stronger
disagreement premise is used to refute the biconditional.

`Setting` supplies an arithmetic theory and a designated sentence.
`Setting.Prov` is semantic consequence in the bundled models.
`TranslationPair` supplies two maps on arithmetic syntax. The manuscript's
canonical pair is defined on the RH fragment (Definitions 1.7.10–1.7.11).
Its arithmetic round trip has a precision parameter (Lemma 1.7.12).
The Lean definition `precisionSentence` captures the quantifier shape.
Its matrix is a parameter. The linear deduction uses the round-trip
equivalence and preservation for that parameter. The remaining step in
Lemma 1.10.2 is to prove finite satisfiability with the failing check
included. The standard model cannot satisfy that check if it satisfies
the universal precision sentence. Over the target theory this finite
satisfiability claim is equivalent to non-entailment of the precision
sentence. The quantifier shape alone gives neither, as the example
`∀ n k, (check n k → check n k)` shows. The analytic obstruction in
Lemma 1.12.4 also remains open here.
