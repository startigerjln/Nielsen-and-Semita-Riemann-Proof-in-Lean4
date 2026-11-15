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
| `finite_witness_reflection` | Proved from published Σ₁-completeness of the explicitly defined Robinson Q. The target arithmetic theory proves Q's eight axioms. |
| `RH_true_in_N` and `RH_true_in_N_of_independence` | The Π₁ form, the target theory's arithmetic basis Q, and the previously established unrefutability (or independence) result. Reflection is now a proved theorem, not an input hypothesis. |
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
| `PlantedZero.finite_zeta_approximations_with_standard_failure` | Uses Mergelyan's theorem to produce a single rational code above the cutoff, satisfying all the specified compact-set approximation tolerances for ζ and failing the direct zero-location check. The common compact must avoid the pole and the planted roots and have connected complement. |

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
`perron_formula_of_valid_limits` proves that agreement from convergence
of the Dirichlet approximants and convergence of their coded error to zero.
`perronIntegral_sub_le_of_integrand_bound` bounds the finite-contour
error for a replacement function from an estimate on the weighted
integrand. The manuscript's proof translation still needs to justify
that its local validity checks are sufficient for the coefficient
identities invoked in the translation.

The three custom axioms are the published analytic statements
`mergelyan` and `perron_formula`, and the published arithmetic theorem
`Robinson.sigma1_complete`. Compactness comes from Mathlib.
Preservation of the canonical round trip is a separate premise of
the relevant Proof I deductions.

## Finite-witness reflection — Figure 1, right branch

Following Jenny Lorraine Nielsen's argument, the right branch starts with
unrefutability obtained by the preceding argument. It extracts a standard
natural-number counterexample from the hypothetical falsity of a Π₁ sentence.
The negated bounded check is Δ₀, so its existential closure is Σ₁. Published
Σ₁-completeness of Robinson Q supplies that existential sentence in every
Q-model. Hence the target theory entails the negation, contradicting
unrefutability. This proves standard arithmetic truth in the metatheory.
The reflection theorems contain no translation pair or round-trip condition.

`RH/Paper/Robinson.lean` explicitly defines the eight axioms of Q in the
existing arithmetic language, including the definition of ≤. Its only custom
axiom, `Robinson.sigma1_complete`, is the one-variable instance of Q's
Σ₁-completeness, expressed as semantic consequence via first-order soundness.
Sources: L. D. Beklemishev, *Gödel incompleteness theorems and the limits of
their applicability. I*, Russian Mathematical Surveys 65 (2010), §3.5,
Theorem 6, <https://homepage.mi-ras.ru/~bekl/Papers/goedel-en.pdf>;
for the exact eight-axiom presentation, Definition 3.1 and Theorem 3.10 of
<https://www.mff.cuni.cz/data/web/obsah/department_math/ka/MathLogic.pdf>.
The published completeness theorem remains an external axiom, as permitted
for published results; finite-witness reflection itself is proved.

The existing `Setting` is an arbitrary arithmetic theory. Its arithmetic
basis is therefore explicit: `∀ q ∈ Robinson.Q, S.Prov q`. This is not a
new RH-specific assertion. `Setting.Prov` continues to mean semantic
consequence in this formalization. These generic theorems do not themselves
instantiate a set-theoretic ZFC interpretation or a concrete RH formula.

`ReflectionAudit.lean` checks the eight encoded Q axioms in ℕ and prints the
axioms of witness extraction, reflection, and both final truth theorems.
The final theorems depend only on Lean's `propext`, `Classical.choice`,
`Quot.sound`, and `Robinson.sigma1_complete`. No original paper result is
introduced as an axiom by this change. The obstruction code is unchanged.

### Explicit blocked-counterexample step

`StandardCounterexample` names the standard finite Δ₀ witness in Figure 1.
`refutation_of_standard_counterexample` turns it into the forbidden refutation
using the published arithmetic input. `standard_counterexample_blocked` applies
the upstream unrefutability result to rule out that witness.
`truth_of_standard_counterexample_blocked` then concludes standard truth;
`truth_from_unrefutability` now follows exactly these two steps.

No axiom was added. The obstruction and translation declarations are unchanged.
These remain generic deductions with the existing explicit inputs for the
arithmetic basis and upstream unrefutability; this refactoring does not discharge
those inputs in a concrete final RH application.
