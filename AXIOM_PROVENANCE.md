# Provenance of the Lean formalization

Files: `RH/Paper/Arith.lean`, `RH/Paper/ProofI.lean`. Lean 4.16.0, Mathlib
(`Mathlib.ModelTheory.Semantics`). Paper version: May 16, 2026
(PhilArchive NIEPOT-5v52).

## Axioms

None. The files contain no `axiom` declaration and no `sorry`.

`#print axioms` on `RH.Paper.RH_true_in_N` and `RH.Paper.RH_independent`
reports only Lean's own `propext`, `Classical.choice`, `Quot.sound`.

## Definitions

| Lean | Meaning | Source |
|---|---|---|
| `L` | language of arithmetic ⟨0, S, +, ×; ≤⟩ | Kaye 1991, §1.1 |
| `natStructure` | the standard model ℕ | Kaye 1991, §1.1 |
| `IsDelta0` | formulas with bounded quantifiers only | Kaye 1991, Ch. 2 |
| `IsPi1` | `∀ n, ψ(n)` with `ψ` Δ₀ | paper §1.17 |
| `Setting.T`, `Setting.RH` | arithmetic theorems of ZFC; the sentence `RH_L` | paper §1.3, §1.18 |
| `Setting.ZFCModel` | a structure satisfying `T` | — |
| `Setting.Prov` | truth in every model of ZFC | equals derivability by Gödel's Completeness Theorem |
| `TranslationPair`, `RL`, `RC` | Definitions 1.4.1, 1.4.2 | paper |
| `LambdaSound` | Definition 1.4.3 (condition (3) for provable sentences) plus Lemma 1.7.12 | paper |

## Assumptions (fields of `Hypotheses`)

These are hypotheses of the theorems, not axioms. Every result marked
"from `Hypotheses`" below is conditional on them.

| Field | Statement | Status |
|---|---|---|
| `rh_pi1` | RH has a Π₁ form with Δ₀ kernel | published: Davis–Matiyasevich–Robinson 1976; paper Prop. 1.18.1 |
| `reflection` | a false Π₁ sentence is refutable in ZFC | published (Σ₁-completeness); paper Thm 1.17.1 |
| `induced` | a ZFC proof of RH forces a Λ-sound pair to exist | the paper's own: Thm 1.7.6. Not proved in Lean |
| `induced_neg` | the same for ¬RH | the paper's own: symmetric case of Thm 1.6.1. Not proved in Lean |

## Theorems proved in Lean

| Lean | Paper | Depends on |
|---|---|---|
| `uniform_preservation` | Lemma 1.5.6 | definitions only |
| `round_trip_adequacy` | Theorem 1.7.13 | definitions only |
| `no_lambda_sound_of_provable` | Remark 1.6.2, step 3 of the reductio | definitions only |
| `not_provable_of_induced` | Theorem 1.6.1 | definitions only |
| `induced_iff_not_provable` | — | definitions only |
| `RH_not_provable`, `neg_RH_not_provable`, `RH_independent` | Corollary 1.13.2 | from `Hypotheses` |
| `truth_from_unrefutability` | Theorem 1.18.2 | from `Hypotheses` |
| `RH_true_in_N` | Theorem 1.18.3 | from `Hypotheses` |

`induced_iff_not_provable` shows that, given the proved step 3, the
assumption `induced` for a sentence is equivalent to that sentence being
unprovable in ZFC. The independence result therefore rests entirely on
Theorem 1.7.6 and its symmetric case.

## Not formalized

Proofs II and III. The connection between the abstract sentence `RH_L`
and Mathlib's `RiemannHypothesis`.
