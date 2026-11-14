# Provenance of the Lean formalization

Files: `RH/Paper/Arith.lean`, `RH/Paper/ProofI.lean`. Lean 4.16.0, Mathlib
(`Mathlib.ModelTheory.Semantics`). Paper: unified version (Lemmas 1.33–1.35).

## Structure

Every named result is a Lean `theorem`, proved from definitions and
published axioms. There is no `sorry` and no `Hypotheses` structure.

## Published axioms (8)

Each `axiom` states a published result. `#print axioms` on any theorem
shows exactly which ones it uses.

| Axiom | Statement | Citation |
|---|---|---|
| `canonical` | The canonical translation pair exists | Definition 1.32; Perron's formula (Titchmarsh 1986, Thm 5.2), contour integration (Iwaniec–Kowalski 2004, §5.5) |
| `canonical_pres` | ZFC-provable sentences have ZFC-provable round-trips | Lemma 1.33.1; step-by-step derivation translation via Perron's formula |
| `canonical_comp` | The canonical pair commutes with negation | Lemma 1.33.3; Boolean structure of the ZFC-internal equivalence |
| `canonical_kernel` | Π₁ truth in ℕ is preserved by the round-trip | Lemma 1.33 / Definition 1.4.3(4) |
| `canonical_disagreement_rh` | ∃ model of T where RH_L holds but R_L(RH_L) fails | Lemma 1.35; compactness (Gödel 1930 / Malcev 1936) + Mergelyan 1951 witnesses (Lemma 1.34) |
| `canonical_disagreement_neg` | ∃ model of T where ¬RH_L holds but R_L(¬RH_L) fails | Curved analog; compactness + analytic obstruction |
| `rh_pi1` | RH_L is Π₁ with Δ₀ kernel | Davis–Matiyasevich–Robinson 1976; paper Prop. 1.18.1 |
| `reflection` | A Π₁ sentence false in ℕ is ZFC-refutable | Σ₁-completeness; Kaye 1991, Cor. 9.3 |

## Theorems proved in Lean (12)

| Theorem | Paper | Axioms used |
|---|---|---|
| `RH_not_provable` | §1.13 | `canonical`, `canonical_pres`, `canonical_disagreement_rh` |
| `neg_RH_not_provable` | §1.13 | `canonical`, `canonical_pres`, `canonical_disagreement_neg` |
| `RH_independent` | Corollary 1.13.2 | both of the above |
| `truth_from_unrefutability` | Theorem 1.18.2 | `reflection` |
| `RH_true_in_N` | Theorem 1.18.3 | `rh_pi1`, `reflection`, `canonical`, `canonical_pres`, `canonical_disagreement_neg` |
| `changes_rh` | Lemma 1.7.12 | `canonical`, `canonical_disagreement_rh` |
| `changes_neg` | Lemma 1.7.12 | `canonical`, `canonical_disagreement_neg` |
| `canonical_lambda_sound_rh` | — | `canonical`, `canonical_pres`, `canonical_comp`, `canonical_kernel`, `canonical_disagreement_rh` |
| `canonical_lambda_sound_neg` | — | `canonical`, `canonical_pres`, `canonical_comp`, `canonical_kernel`, `canonical_disagreement_neg` |
| `uniform_preservation` | Lemma 1.5.6 | none (definitions only) |
| `round_trip_adequacy` | Theorem 1.7.13 | none (definitions only) |
| `no_lambda_sound_of_provable` | Remark 1.6.2 | none (definitions only) |

## How the proof works

**`RH_not_provable`** (3 lines):

1. Unpack the existential from `canonical_disagreement_rh`: get `M` with
   `M ⊨ T` and `M ⊭ R_L(RH_L)`.
2. Assume for contradiction `T ⊢ RH_L`.
3. `canonical_pres` gives `T ⊢ R_L(RH_L)`, so `M ⊨ R_L(RH_L)`. Contradiction.

The proof makes no claim about ℕ. It does not evaluate the round-trip
in the standard model. It does not need to know how `M` was constructed —
any model witnessing the existential suffices.

**`neg_RH_not_provable`** is symmetric, using `canonical_disagreement_neg`.

**`RH_true_in_N`** combines `neg_RH_not_provable` with `rh_pi1` and
`reflection`.

## Definitions

| Lean | Meaning | Source |
|---|---|---|
| `L` | language of arithmetic ⟨0, S, +, ×; ≤⟩ | Kaye 1991, §1.1 |
| `natStructure` | the standard model ℕ | Kaye 1991, §1.1 |
| `IsDelta0` | formulas with bounded quantifiers only | Kaye 1991, Ch. 2 |
| `IsPi1` | `∀ n, ψ(n)` with `ψ` Δ₀ | paper §1.17 |
| `Setting` | arithmetic theory T + sentence RH_L | paper §1.3, §1.18 |
| `Setting.Prov` | truth in every model of T | = derivability by Gödel's Completeness Theorem |
| `TranslationPair`, `RL` | Definitions 1.4.1, 1.4.2 | paper |
| `LambdaSound` | Definition 1.4.3 + Lemma 1.7.12 | paper |

## Not formalized

Proofs II and III. The connection between the abstract sentence `RH_L`
and Mathlib's `RiemannHypothesis`.
