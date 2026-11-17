# Provenance of the Lean formalization

The checked files are `RH/Paper/Arith.lean` and `RH/Paper/ProofI.lean`.
The toolchain is pinned by `lean-toolchain` (Lean 4.16.0-rc1), and Mathlib
by `lake-manifest.json`.

## Definitions and supplied inputs

| Item | Status |
|---|---|
| Arithmetic language, natural-number structure, `IsDelta0`, `IsPi1` | Definitions in Lean; `IsPi1 S.RH` still needs to be supplied for a concrete RH sentence. |
| `SemanticProfile`, `LambdaObstruction`, `LambdaZero` | Model-based definitions. No truth-value case split on RH in ℕ defines the translation or obstruction. |
| `firstOrderCompactness` | Proved from Mathlib's `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`; no compactness axiom parameter remains. |
| `FiniteSatisfiabilityObligation S τ` | One explicit RH-specific proof obligation with positive and negative branches, each scoped under the corresponding provability assumption. Neither branch has been proved for concrete RH. |
| `RoundTripPreserves S τ` | Explicit requirement on the reconstruction. Must be established when the actual translation is supplied; not a theorem for arbitrary functions. |
| `WitnessReflection S` | Explicit requirement on the arithmetic theory. Motivated by Σ₁ completeness for theories extending sufficient arithmetic, but not established here for an instantiated ZFC theory. |
| `Setting.consistent` | Explicit model-existence data. It is not deduced from the syntax of ZFC. |
| Negation compositionality and kernel agreement | Explicit fields of `LambdaSound`, separate from obstruction. |

These are theorem parameters, not hidden kernel axioms. There are no project
`axiom` declarations or `sorry` terms. This does **not** mean the hypotheses
have been discharged. `#print axioms` reports kernel dependencies and must be
read together with the theorem signatures.

## Exact reductio

For a fixed background theory T and round trip R:

1. Assume T entails S (S is RH for one branch and ¬RH for the other).
2. Apply the relevant **assumed** finite-satisfiability implication to
   T ∪ {S, ¬R(S)}.
3. Mathlib compactness gives a model M of that theory.
4. The model lies in `LambdaObstruction`: S holds in M and R(S) fails.
5. `RoundTripPreserves` forces R(S) to hold in that same M, a contradiction.
6. Discharge the provability assumption.

The separate witness-reflection argument derives truth of a Π₁ sentence
from non-refutability. No arithmetic soundness assumption or truth of RH
in ℕ is used to manufacture the disagreement model.

## The uploaded separation proposal

For a fixed theory T, sentence S, and reconstruction A, completeness and
compactness identify:

- T + S does not prove A;
- T + S + ¬A has a model;
- T + S + ¬A is finitely satisfiable.

The Lean definition `UniformitySeparation` states the semantic version of
the first item. `finiteSatisfiable_of_uniformitySeparation` proves the
model-to-finite-fragments implication. `finiteSatisfiabilityObligation_of_separation`
packages both reductio directions when the separation premises are supplied.
Neither theorem proves the concrete separation premise.

The shape ∀n ∀k ψ(n,k) does not by itself establish nonprovability. If ψ is
bounded, this remains Π₁. Use of a second-order theory in a proof does not
by itself establish that its arithmetic conclusion is unprovable in a
first-order theory. See Hirschfeldt, *Slicing the Truth* (2014), Theorem 7.8,
for the relevant WKL₀ conservativity phenomenon. The subsequent ZFC-level proposal corrects the background-theory mismatch.
Its appeal to non-categoricity still does not prove failure of the specified
implication: elementary extensions preserve all first-order sentences.
The last pasted manuscript was incomplete (ending at “However,”); its
revised model-class definitions were merged without discarding the
complete manuscript’s remaining sections.

## Semantic Λ and soundness

`LambdaObstruction S τ φ` is the class of models of S.T where φ and τ.RL φ
disagree. `lambdaZero_iff_profiles` and `lambdaZero_iff_empty` prove the
connection to equality of semantic profiles and emptiness of the discrepancy
class. `LambdaSound` no longer includes a `changes` field: assuming soundness
must not also assume the desired nonzero obstruction.

`pointwise_preservation_forces_zero` checks the distinction between elementary
invariance and full pointwise truth preservation: the latter, together with
negation preservation, forces zero obstruction. `identity_lambda_zero` checks
that identity reconstruction cannot create an obstruction.

## Remaining concrete formalization

`Setting.T` is an arbitrary arithmetic theory; `Setting.RH` is an arbitrary
sentence. The name `ZFCModel` denotes satisfaction of this chosen T and is
not an implementation of set-theoretic ZFC. `Setting.Prov` denotes semantic
consequence, not a separately encoded proof calculus. The maps use a common
arithmetic syntax as the deductive abstraction; the full two-language maps,
their actual coding of analytic predicates, and their preservation proofs
are not implemented. The concrete equivalence to Mathlib's `RiemannHypothesis`
is outstanding.

Consequently, finite satisfiability is the isolated obstruction-model input,
not the only task needed to obtain an unconditional theorem of analytic RH.
Proofs II and III are not formalized. The manuscript's title and abstract
retain the authors' claim; the dependency convention states the scope of
this amendment and its checked deductive core.

## Precision reconstruction check

`RH/Paper/Precision.lean` proves `exact_iff_all_dyadic_precision` and
its indexed-family version. For an Archimedean ordered field, x = c
is equivalent to ∀k, |x - c| < (1/2)^k. Thus the exact equality and
this direct precision formulation do not differ in mathematical content.
The theorem uses no RH assumption. It does not implement the still-unspecified
arithmetic predicate ψ(n,k); that coding requires a separate correctness proof.
When the elementary argument is formalized in ZFC, its natural-number
quantifiers are internal, including nonstandard values in nonstandard models.
