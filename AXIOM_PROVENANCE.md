# Lean dependency audit

The manuscript (`unified.tex` and `unified.pdf`) and the `LambdaSound`
definition are unchanged by this revision.

## Finite satisfiability

`FiniteSatisfiabilityAxiom S τ` is precisely finite satisfiability of
`S.T ∪ {S.RH} ∪ {neg (τ.RL S.RH)}`. It is the one finite-satisfiability
premise `hf` used throughout the principal proof. It is a local axiom
(a theorem parameter), not a global axiom asserting this for every
arbitrary theory and translation. Such a universal assertion would be
inconsistent, for example for the identity round trip.

The former `TruthGivesFS` and `NegTruthGivesFS` bridges have been removed.
Both non-provability and non-refutability use the same positive
finite-satisfiability premise. Arithmetic soundness is unnecessary and
has been removed. Compactness is proved using mathlib's
`FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`.

## Exact remaining inputs

| Conclusion | Explicit inputs beyond the setting and translation |
|---|---|
| `neg_RH_not_provable` | `FiniteSatisfiabilityAxiom S τ` |
| `RH_true_in_N` | The same finite satisfiability; `IsPi1 S.RH`; `WitnessReflection S` |
| `RH_not_provable`, `RH_independent` | The same finite satisfiability; existing `RoundTripPreserves S τ` |

The arithmetic inputs correspond to published mathematics:

- Davis, Matiyasevich and Robinson, *Hilbert's tenth problem: Diophantine
  equations: Positive aspects of a negative solution*, Proceedings of
  Symposia in Pure Mathematics 28 (1976), pp. 323–378, for an arithmetic
  presentation of RH. This does not prove `IsPi1` for an arbitrary
  sentence supplied as `S.RH`.
- Richard Kaye, *Models of Peano Arithmetic* (1991), Chapter 2,
  pp. 16–27, for Σ₁ completeness of PA⁻ and the finite-witness argument.
  https://doi.org/10.1093/oso/9780198532132.003.0003
  This applies to theories containing sufficient elementary arithmetic,
  not to every arbitrary `Setting.T`.

These are explicit interfaces to published results, not Lean proofs of
those results for a concrete ZFC/RH encoding. `RoundTripPreserves` is
retained from the existing framework; it is a separate premise for the
independence conclusion, not a consequence of finite satisfiability.
It is not used in the standard-truth conclusion.

## Scope of the check

`Setting.T` and `Setting.RH` remain parameters. `Setting.Prov` remains
semantic consequence. A concrete ZFC interpretation, selected RH syntax,
and equivalence with mathlib's analytic `RiemannHypothesis` have not been
added in this narrowly scoped revision. The existing `Setting.consistent`
field is retained, although finite satisfiability supplies a model itself.

`#print axioms` reports global kernel dependencies, not theorem parameters.
The audit must therefore inspect both theorem signatures and axiom output.
No `sorry`, project-wide global axiom, or substituted definition of Λ is
introduced. Finite satisfiability is explicitly assumed, not claimed proved.
