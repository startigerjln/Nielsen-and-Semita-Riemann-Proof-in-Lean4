# Provenance of the Lean formalization

Files: `RH/Paper/Arith.lean`, `RH/Paper/ProofI.lean`. Lean 4.16.0, Mathlib
(`Mathlib.ModelTheory.Semantics`). Paper: unified version (Lemmas 1.33–1.35).

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

## Assumptions (fields of `Hypotheses S τ`)

The canonical translation pair `τ` is a parameter, not existentially
quantified. Every result marked "from `Hypotheses`" is conditional on these.

| Field | Statement | Provenance |
|---|---|---|
| `rh_pi1` | RH has a Π₁ form with Δ₀ kernel | published: Davis–Matiyasevich–Robinson 1976; paper Prop. 1.18.1 |
| `reflection` | a false Π₁ sentence is refutable in ZFC | published (Σ₁-completeness); paper Thm 1.17.1 |
| `pres` | ZFC-provable sentences have ZFC-provable round-trips | Lemma 1.33.1: step-by-step translation of ZFC derivations through `τ₀` |
| `comp` | `τ` commutes with negation | Lemma 1.33.3: by construction of `τ₀` |
| `kernel` | Π₁ truth in ℕ preserved by round-trip | Lemma 1.33 / Definition 1.4.3(4) |
| `disagreement_rh` | ∃ model of T where RH_L holds but R_L(RH_L) fails | Lemma 1.35 (Linear Reconstruction Failure): compactness + Mergelyan witnesses (Lemma 1.34) |
| `disagreement_neg` | ∃ model of T where ¬RH_L holds but R_L(¬RH_L) fails | Curved analog (Lemma 1.12.4 equivalent): compactness + analytic obstruction |

### How the main proof uses these

`RH_not_provable` uses only `pres` and `disagreement_rh`:
1. Unpack the existential to get a model `M` with `M ⊨ T` and `M ⊭ R_L(RH_L)`.
2. If `T ⊢ RH_L`, then preservation gives `T ⊢ R_L(RH_L)`, so `M ⊨ R_L(RH_L)`.
3. Contradiction.

The proof makes no claim about ℕ and never evaluates the round-trip in
the standard model. It is purely conditional on the existence of the
disagreement model. The `M.Sat S.RH` conjunct in `disagreement_rh` is
unused for this theorem (discarded with `‐` in the `obtain`); it is
used by `changes_rh` to connect to the Λ-sound framework.

`neg_RH_not_provable` is symmetric, using `disagreement_neg`.

`RH_true_in_N` uses `reflection` and `rh_pi1` *after* independence.

## Theorems proved in Lean

| Lean | Paper | Depends on |
|---|---|---|
| `not_prov_of_roundtrip_fails` | — (general lemma) | definitions only |
| `RH_not_provable` | §1.13, Case A | `pres`, `disagreement_rh` |
| `neg_RH_not_provable` | §1.13, Case B analog | `pres`, `disagreement_neg` |
| `RH_independent` | Corollary 1.13.2 | both of the above |
| `truth_from_unrefutability` | Theorem 1.18.2 | `reflection` |
| `RH_true_in_N` | Theorem 1.18.3 | `rh_pi1`, `reflection`, `neg_RH_not_provable` |
| `changes_rh`, `changes_neg` | Lemma 1.7.12 consequence | `disagreement_rh`/`neg` (with `M.Sat` conjunct) |
| `canonical_lambda_sound_rh`/`neg` | — | all Hypotheses fields |
| `uniform_preservation` | Lemma 1.5.6 | definitions only |
| `round_trip_adequacy` | Theorem 1.7.13 | definitions only |
| `no_lambda_sound_of_provable` | Remark 1.6.2 | definitions only |

## Not formalized

Proofs II and III. The connection between the abstract sentence `RH_L`
and Mathlib's `RiemannHypothesis`.
