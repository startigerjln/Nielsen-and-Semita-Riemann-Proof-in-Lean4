# Provenance of the Lean formalization

Files: `RH/Paper/Arith.lean`, `RH/Paper/ProofI.lean`.
Lean 4.16.0 and pinned Mathlib.

## Explicit inputs

| Input | Role | Source |
|---|---|---|
| `ArithSoundness S` | Provable sentences are true in ℕ | Standard metatheoretic fact [Shoenfield 1967] |
| `Compactness` | First-order compactness | [Gödel 1930; Malcev 1936] |
| `IsPi1 S.RH` | RH is a Π₁ arithmetic sentence | [Davis–Matiyasevich–Robinson 1976] |
| `WitnessReflection S` | False Π₁ sentences are refutable (Σ₁ completeness) | [Kreisel 1951; Kaye 1991] |
| `RoundTripPreserves S τ` | Provability is preserved by the round trip | Manuscript §1.5–1.7 |
| `TruthGivesFS S τ` | ℕ ⊨ RH → positive disagreement theory is finitely satisfiable | Manuscript Lemma 1.34a [Kaye 1991, Thm 15.1] |
| `NegTruthGivesFS S τ` | ℕ ⊨ ¬RH → negative disagreement theory is finitely satisfiable | Symmetric argument |
| Compositionality and kernel agreement | Inputs to the LambdaSound structure | Explicit hypotheses |

## Reductio scoping of finite satisfiability

The finite satisfiability inputs (`TruthGivesFS`, `NegTruthGivesFS`) are
conditional on truth in ℕ.  They are consumed ONLY inside the reductio
proofs, where the truth they require is supplied by soundness from the
hypothesis being refuted:

    RH_not_provable:
      intro hprov : S.Prov S.RH          -- reductio hypothesis
      have := hs S.RH hprov              -- soundness → TrueInN S.RH
      have := htfs ‹TrueInN S.RH›        -- overspill → FS
      ...                                 -- compactness → model → ⊥

    neg_RH_not_provable:
      intro hprov : S.Prov (neg S.RH)    -- reductio hypothesis
      have := hs (neg S.RH) hprov        -- soundness → TrueInN (neg S.RH)
      have := hntfs ‹TrueInN (neg S.RH)› -- overspill → FS
      ...                                 -- compactness → model → ⊥

Lean's kernel verifies that neither `TrueInN S.RH` nor any finite
satisfiability claim appears as a hypothesis of `RH_not_provable`,
`neg_RH_not_provable`, `RH_independent`, or `RH_true_in_N`.  The
only source of truth-in-ℕ is the `ArithSoundness` bridge applied to
the reductio hypothesis, which is discharged when `False` is reached.

The former `OverspillFiniteSatisfiability` standing hypothesis has been
eliminated from all principal theorems.

## Disagreement theories

Two disagreement theories are used, one for each reductio direction:

    disagreementTheory S τ     = S.T ∪ {S.RH}       ∪ {¬(τ.RL S.RH)}
    negDisagreementTheory S τ  = S.T ∪ {¬S.RH}      ∪ {¬(τ.RL (¬S.RH))}

Each disagreement theory asserts that a sentence holds in a model of T
but its round-trip translation does not.  Compactness converts finite
satisfiability into the full disagreement model.

## Principal conditional theorems

- `RH_not_provable`: soundness + overspill bridge + compactness + round-trip preservation → ZFC ⊬ RH.
- `neg_RH_not_provable`: symmetric reductio → ZFC ⊬ ¬RH.
- `neg_RH_not_provable_of_model`: a model of T + RH suffices for non-refutability (alternative route).
- `RH_independent`: combines both directions.
- `truth_from_unrefutability`: non-refutability + Π₁ + Kreisel reflection → truth in ℕ.
- `RH_true_in_N`: non-refutability route → TrueInN S.RH.
- `RH_true_from_model`: model route → TrueInN S.RH.
- `changes_rh`, `canonical_lambda_sound_rh`, `uniform_preservation`, `round_trip_adequacy`, `no_lambda_sound_of_provable`: Λ-soundness framework with stated hypotheses.

## Definitions and remaining formalization

`Setting.T` is an arbitrary arithmetic theory and `Setting.RH` an arbitrary sentence, not yet instantiated as ZFC's arithmetic consequences and actual arithmetic RH. `Setting.Prov` is semantic consequence; identifying it with syntactic derivability uses first-order completeness and the intended theory. The translation pair uses arithmetic syntax for both maps as a placeholder for the manuscript's distinct languages. The `LambdaSound` structure captures the provable-fragment reductio, not the full manuscript definition.

The link to Mathlib's `RiemannHypothesis` is outstanding. The module prints kernel axiom dependencies for the principal conditional theorems; this does not discharge their explicit inputs. No Proof II or III formalization is included.
