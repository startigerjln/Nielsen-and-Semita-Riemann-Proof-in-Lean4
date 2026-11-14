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
| `TranslationPair`, `RL`, `RC` | Definitions 1.4.1, 1.4.2 | paper |
| `LambdaSound` | Definition 1.4.3 + Lemma 1.7.12 | paper |

## Published facts (built into `Setting`)

`Setting` bundles the arithmetic theory `T`, the sentence `RH_L`, and
two published facts that constrain them. Any `Setting` carries these
as proved fields, not hypotheses.

| Field | Statement | Citation |
|---|---|---|
| `rh_pi1` | `RH_L` is Π₁ with Δ₀ kernel | Davis–Matiyasevich–Robinson 1976; paper Prop. 1.18.1 |
| `reflection` | a Π₁ sentence false in ℕ is ZFC-refutable | Σ₁-completeness; Kaye 1991, Cor. 9.3; paper Thm 1.17.1 |

`truth_from_unrefutability` (Theorem 1.18.2) uses only these two and
needs no `Hypotheses` at all.

## Paper's results (fields of `Hypotheses S τ`)

The canonical translation pair `τ` is a parameter. Every final theorem
(`RH_not_provable`, `RH_true_in_N`, etc.) is conditional on these five
fields, each of which is a theorem proved in the paper from published
tools.

| Field | Paper reference | Proved from |
|---|---|---|
| `pres` | Lemma 1.33.1 (Preservation) | Step-by-step translation of ZFC derivations through `τ₀`; uses Perron's formula (Titchmarsh 1986, Thm 5.2) and the ZFC-internal proof of `RH_L ↔ RH_C` (Iwaniec–Kowalski 2004, §5.5) |
| `comp` | Lemma 1.33.3 (Compositionality) | By construction of `τ₀`: the continuation code `m` is threaded uniformly through all subformulas |
| `kernel` | Lemma 1.33 / Def. 1.4.3(4) | Π₁ truth in ℕ depends only on standard witnesses; the canonical pair preserves these |
| `disagreement_rh` | Lemma 1.35 (Linear Reconstruction Failure) | Compactness theorem (Gödel–Malcev) + Mergelyan witnesses (Lemma 1.34, from Mergelyan 1951) |
| `disagreement_neg` | Curved analog of Lemma 1.35 | Compactness + analytic obstruction (Lemma 1.12.4 equivalent) |

## How the proof works

**`RH_not_provable`** uses only `pres` and `disagreement_rh` (3 lines):

1. Unpack the existential: get `M` with `M ⊨ T` and `M ⊭ R_L(RH_L)`.
2. Assume for contradiction `T ⊢ RH_L`.
3. Preservation gives `T ⊢ R_L(RH_L)`, so `M ⊨ R_L(RH_L)`. Contradiction.

The proof makes no claim about ℕ. It never evaluates the round-trip in
the standard model. It does not need to know how `M` was constructed —
any model witnessing the existential suffices.

The `M.Sat S.RH` conjunct in `disagreement_rh` is unused here (discarded
with `‐`); it is used by `changes_rh` to connect to the Λ-sound framework.

**`neg_RH_not_provable`** is symmetric, using `disagreement_neg`.

**`RH_true_in_N`** combines `neg_RH_not_provable` with the published
`Setting.rh_pi1` and `Setting.reflection`.

## Theorems proved in Lean

| Lean | Paper | Depends on |
|---|---|---|
| `Setting.prov_neg_of_false` | — | `Setting.reflection` only |
| `not_prov_of_roundtrip_fails` | — (general) | definitions only |
| `RH_not_provable` | §1.13 | `pres`, `disagreement_rh` |
| `neg_RH_not_provable` | §1.13 | `pres`, `disagreement_neg` |
| `RH_independent` | Corollary 1.13.2 | both of the above |
| `truth_from_unrefutability` | Theorem 1.18.2 | `Setting` only (no `Hypotheses`) |
| `RH_true_in_N` | Theorem 1.18.3 | `Setting` + `neg_RH_not_provable` |
| `changes_rh` / `changes_neg` | Lemma 1.7.12 | `disagreement_rh` / `neg` |
| `canonical_lambda_sound_rh` / `neg` | — | all `Hypotheses` fields |
| `uniform_preservation` | Lemma 1.5.6 | definitions only |
| `round_trip_adequacy` | Theorem 1.7.13 | definitions only |
| `no_lambda_sound_of_provable` | Remark 1.6.2 | definitions only |

## Not formalized

Proofs II and III. The connection between the abstract sentence `RH_L`
and Mathlib's `RiemannHypothesis`.
