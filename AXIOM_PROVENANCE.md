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
| `RH_disagrees_of_finite_precision_failure` | Round-trip equivalence and finite satisfiability after adjoining both RH_L and the negated precision sentence (§1.10.2). |
| `RH_finite_precision_failure_iff` | None. The full finite-satisfiability condition is equivalent to the target theory failing to entail the implication from RH_L to the precision sentence. |
| `RH_independent_of_finite_precision_failure` | The same compactness premises plus preservation for RH_L. |
| `RH_disagrees_of_named_precision_failure` | Round-trip equivalence and finite satisfiability of the expanded theory with the fresh constant in §1.10.2. The named failure survives forgetting the new constant. |
| `named_precision_failure_false_in_N` | The precision sentence holds in ℕ. For every interpretation of the fresh constant in ℕ, the added sentence asserting a failed check is false. |
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

## Planted-zero argument in the unified manuscript

The following modules address Lemmas 1.34–1.35 of the unified manuscript.
They use Jenny Lorraine Nielsen's observation that the planted zero is a
standard counterexample for a direct check of the coded function.

| Declaration | Scope |
|---|---|
| `mergelyan` | The published polynomial approximation theorem for a compact plane set with connected complement, a continuous function holomorphic in the interior, and positive uniform tolerance. |
| `approximate_with_polynomial_factor` | Proves that one can approximate with a prescribed polynomial factor that is nonzero on the compact set. The proof uses Mergelyan's theorem. |
| `approximate_with_prescribed_zeros` | Uses Mergelyan's theorem to prove uniform approximation with exact zeros at a prescribed finite set disjoint from the compact. |
| `PlantedZero.planted_code_fails` | Proves by exact rational arithmetic that the candidate code for the planted point fails at precision 3, provided the denominator is nonzero there. |
| `PlantedZero.finite_checks_with_failure` | Combines the failing candidate with any finite list of bounds and local validity checks, given codes that pass the initial validity checks and exceed the cutoff. |
| `PlantedZero.approximate_polynomial_by_rational_coefficients` | Proves uniform approximation of a complex polynomial on a compact set by Gaussian-rational coefficient lists. |
| `PlantedZero.cauchy_coefficient_error_le` | Uses Mathlib's Cauchy integral to bound the degree-`n` coefficient of the error by the uniform boundary error divided by the disc radius to the power `n`. |
| `PlantedZero.finite_zeta_approximations_with_standard_failure` | Uses Mergelyan's theorem to produce a single rational code above the cutoff, satisfying all the specified compact-set approximation tolerances for ζ and failing the direct zero-location check. The common compact must avoid the pole and the planted roots and have connected complement. |
| `PlantedZero.finite_zeta_approximations_with_recovery_and_failure` | Uses Mergelyan and Perron to obtain one rational code that also recovers any finite collection of standard Mertens sums after rounding. The approximation compact must contain the chosen Perron contour. |

The point code directly names rational coordinates. This implementation
checks zeros given by those coordinates. The finite approximation
theorem uses uniform error on specified compact regions. Connecting it
to the manuscript's validity schema requires showing that these estimates
imply its Taylor-overlap and Dirichlet checks for the same code. Connecting
the direct zero-location test to the first-order round trip also requires
a proof.

## Perron's formula

`RH/Paper/Perron.lean` states Montgomery and Vaughan, *Multiplicative
Number Theory I: Classical Theory* (2007), Theorem 5.1. The declaration
`perron_formula` requires convergence of the ordinary Dirichlet series
in a half-plane. It gives the limit along symmetric vertical contours
and counts an integer cutoff with half weight. The theorem
`perron_formula_of_nonintegral_cutoff` deduces the ordinary summatory
formula away from integer cutoffs.

`perron_formula_of_vertical_agreement` transfers the limit to a function
that agrees exactly with the Dirichlet series on the integration line.
`perronIntegral_sub_le_of_integrand_bound` bounds the finite-contour
error for a replacement function from an estimate on the weighted
integrand. `PerronRecovery.lean` proves an explicit reciprocal error
bound and the existence of one contour height and tolerance for any
finite family of standard Mertens sums. The same file verifies
compatibility with sufficiently late Dirichlet partial sums at any
fixed standard point in the convergence half-plane.

Lemma 1.33 and Remark 1.36 also use recovery on quantified lines
of a proof. Finite sets of such lines can contain universally
quantified formulas. The finite-input recovery theorem supplies
concrete instances. Preservation of the quantified formulas for
codes satisfying the manuscript's validity schema remains a separate
proof obligation.

The two custom axioms are the published analytic statements
`mergelyan` and `perron_formula`. Compactness comes from Mathlib.
Preservation of the canonical round trip is a separate premise of
the relevant Proof I deductions.
