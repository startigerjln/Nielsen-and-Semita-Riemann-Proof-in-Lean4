# Provenance of the Lean formalization

`RH/Paper/Arith.lean` defines the arithmetic language, its standard model,
and bounded formulas. `RH/Paper/ProofI.lean` checks the deductions below.
Both files use Mathlib's first-order semantics and declare no custom
axioms. `RH/Paper/Lagarias.lean` imports a published arithmetic criterion
for Mathlib's `RiemannHypothesis`.

Section and theorem numbers below refer to Nielsen and Semita's
32-page manuscript with the May 16, 2026 update (`OLDGOODRIEMANN.pdf`).

| Axiom | Published statement |
|---|---|
| `lagarias_theorem_1_1` | Lagarias, *An Elementary Problem Equivalent to the Riemann Hypothesis*, American Mathematical Monthly 109 (2002), 534–543, Theorem 1.1. The divisor-sum inequality holds for every positive integer, with equality only at one, if and only if RH holds. |

| Deduction | Explicit premises |
|---|---|
| `riemannHypothesis_iff_dyadic_precision` | None. The analytic critical-line condition is equivalent to the dyadic inequalities at all natural precisions, by the Archimedean property of ℝ. |
| `lagarias_iff_dyadic_precision` | Lagarias, Theorem 1.1, composed with the analytic precision equivalence. |
| `Model.not_sat_precisionSentence` | None. Failure of the sentence in Lemma 1.7.12 is equivalent to the existence of a candidate index and precision at which the matrix fails. |
| `Model.sat_vacuous_precision` | A nonempty model. Adding a universal precision variable unused by the matrix preserves satisfaction. |
| `Model.sat_precision_of_completeTheory` | The precision sentence holds in ℕ and the model satisfies the complete theory of ℕ. This verifies that adjoining a nonstandard parameter using the complete theory alone cannot give a failing check. |
| `round_trip_failure_of_finite_satisfiability` | Finite satisfiability of the theory with the negated round trip added, using Mathlib's compactness theorem |
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
Its matrix is a parameter. In Lemma 1.10.2, each finite fragment that
contains the asserted failing check still needs a model realizing that
failure. Introducing a nonstandard parameter supplies no such proof.
Applying the deductions to RH requires implementing that fragment and
the two maps, defining the precision predicate, and proving preservation
and the obstruction lemmas for those definitions. The arithmetic theorem
also needs a first-order encoding of an equivalent arithmetic criterion.
Lagarias's theorem supplies an equivalence with Mathlib's
`RiemannHypothesis` for the real-valued divisor-sum criterion. Proofs II
and III remain outside this development.
