# Provenance of the Lean formalization

`RH/Paper/Arith.lean` defines the arithmetic language, its standard model,
and bounded formulas. `RH/Paper/ProofI.lean` checks the deductions below.
Both files use Mathlib's first-order semantics and declare no custom
axioms.

| Deduction | Explicit premises |
|---|---|
| `RH_not_provable` | Preservation for RH_L (Lemma 1.33.1) and an eligible model where its round trip fails (the failure part of Lemma 1.35) |
| `neg_RH_not_provable` | Preservation and round-trip failure for ¬RH_L |
| `RH_independent` | Preservation and round-trip failure for both polarities |
| `changes_rh` and `changes_neg` | A model satisfying the original sentence and falsifying its round trip |
| `lambda_sound_of_disagreement` | Preservation, commutation with negation, Π₁ truth preservation in ℕ, and disagreement |
| `RH_true_in_N` | The Π₁ form, reflection for the given theory (via Σ₁-completeness for ZFC), and unrefutability |
| `uniform_preservation` and `round_trip_adequacy` | Λ-soundness and provability of the input sentence |

Jenny Lorraine Nielsen observed that unprovability uses only round-trip
failure in an eligible model. The deduction applies preservation to
whichever model witnesses the existential premise. The stronger
disagreement premise is used to refute the biconditional.

`Setting` supplies an arithmetic theory and a designated sentence.
`Setting.Prov` is semantic consequence in the bundled models.
`TranslationPair` supplies two maps on arithmetic syntax. Applying the
deductions to RH requires instantiating these parameters and proving the
relevant premises. This development leaves the specific translation
clauses, preservation and obstruction arguments, the bridge to Mathlib's
`RiemannHypothesis`, and Proofs II and III outside its scope.
