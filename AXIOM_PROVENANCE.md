# Provenance of the Lean formalization

Files: `RH/Paper/Arith.lean`, `RH/Paper/ProofI.lean`.
Lean 4.16.0 and pinned Mathlib.

## Explicit inputs, not project axioms

| Input | Role | Status |
|---|---|---|
| `IsPi1 S.RH` | RH-specific arithmetic representation | Published representability result; actual formula and zeta equivalence not formalized |
| `WitnessReflection S` | True Σ₁ witnesses are provable in the intended arithmetic theory of ZFC | Standard result, not proved in this Lean module |
| `Compactness` | First-order compactness | Standard theorem, not yet connected to this custom model interface |
| `OverspillFiniteSatisfiability S τ` | Manuscript Linear Reconstruction Failure and ZFC-Level Realization | Outstanding RH-specific proof obligation |
| `RoundTripPreserves S τ` | Preservation for provable sentences | Manuscript application, explicit hypothesis |
| Compositionality and kernel agreement | Inputs to the provable-fragment LambdaSound structure | Explicit hypotheses, not a verification of the full manuscript definition |

## Overspill and compactness

The manuscript's Linear Reconstruction Failure introduces a nonstandard zero index and nonstandard precision. The input needed by the Lean compactness deduction is finite satisfiability of

    S.T ∪ {S.RH} ∪ {neg (τ.RL S.RH)}.

Here the intended S.T for the final independence argument is the arithmetic consequences of ZFC, not merely IΣ₁ or PA. In particular a finite fragment can include both RH and the negation of its round trip. Overspill gives nonstandard indices satisfying suitable definable properties, but does not by itself give a failing nonstandard precision check. The RH-specific finite satisfiability and the lift to the intended ZFC theory still need proof. No planted-zero or Mergelyan assumption is used.

The input is restricted to the setting and pair supplied by the caller; there is no assertion of finite satisfiability for all arbitrary sentences and theories.

## Conditional deductions

- `canonical_disagreement_rh`: compactness + RH-specific finite satisfiability yield a disagreement model.
- `RH_not_provable`: disagreement + provability preservation yield non-provability.
- `neg_RH_not_provable_of_model`: a model of T + RH suffices for non-refutability.
- `neg_RH_not_provable`, `RH_independent`: consequences of the preceding steps.
- `truth_from_unrefutability`: witness reflection and Π₁ form give standard truth.
- `RH_true_from_model`: minimal route, directly from a model of T + RH.
- `RH_true_in_N`: compactness route to standard truth, conditional on the explicit inputs.
- `changes_rh`, `canonical_lambda_sound_rh`, `uniform_preservation`, `round_trip_adequacy`, `no_lambda_sound_of_provable`: deductive preservation framework, with the stated hypotheses.

## Definitions and remaining formalization

`Setting.T` is an arbitrary arithmetic theory and `Setting.RH` an arbitrary sentence, not yet instantiated as ZFC's arithmetic consequences and actual arithmetic RH. `Setting.Prov` is semantic consequence; identifying it with syntactic derivability uses first-order completeness and the intended theory. The translation pair uses arithmetic syntax for both maps as a placeholder for the manuscript's distinct languages. The `LambdaSound` structure captures the provable-fragment reductio, not the full manuscript definition.

The link to Mathlib's `RiemannHypothesis` is outstanding. The module prints kernel axiom dependencies for the principal conditional theorems; this does not discharge their explicit inputs. No Proof II or III formalization is included.
