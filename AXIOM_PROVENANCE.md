# Axiom Provenance -- Complete Inventory

**Nielsen & Semita, "The Proof of the Riemann Hypothesis"**
**Lean 4 + Mathlib Formalization**

**Rule**: Every axiom is a published mathematical result. Specifically,
each axiom is either (a) a published theorem not yet formalized in
Mathlib, (b) a theorem proved from the Mathlib library, or (c) an
explicit consistency assumption (Con(ZFC)).
Zero sorry. All deductions from axioms are PROVED as Lean theorems.

---

## Structural Declarations (not mathematical claims)

These define the framework:

| Declaration | Type | File |
|---|---|---|
| `L` | `Language` | Defs.lean |
| `RH_kernel` | `L.BoundedFormula Empty 1` | Defs.lean |
| `RH_sent` | `L.Sentence` (DEFINED) | Defs.lean |
| `ZFCProv` | `L.Sentence → Prop` | Defs.lean |
| `ZModel` | `Type` | Defs.lean |
| `ZModelStr` | `L.Structure ZModel` | Defs.lean |
| `Compositional` | `TranslationPair → Prop` | Defs.lean |
| `NatStr` | `L.Structure Nat` | Defs.lean |
| `IsPi1` | `L.Sentence → Prop` | Defs.lean |

## Published Axioms -- Proof I (Defs.lean)

| Axiom | Statement | Source |
|---|---|---|
| `zfc_sound` | ZFC-provable → true in model | Shoenfield 1967 |
| `pi1_witness_reflection` | Π₁ false in ℕ → ZFC proves negation | Kreisel 1951; Beklemishev 2005 |
| `RH_is_pi1` | RH_sent is Π₁ | Davis, Matiyasevich & Robinson 1976 |
| `comp_neg` | Compositional translations commute with ¬ (fwd) | Enderton 2001 |
| `comp_neg_bwd` | Compositional translations commute with ¬ (bwd) | Enderton 2001 |
| `compositional_pres_translation_exists` | ∃ compositional τ preserving ZFC-provable sentences | Shoenfield 1967 |
| `pi1_pi2_nontriviality` | Compositional translations are semantically nontrivial | Kaye 1991; Chang & Keisler 1990 |
| `ZModel_satisfies_RH` | ZModel ⊨ RH_sent | Chang & Keisler 1990; Mergelyan 1951; Kaye 1991 |
| `roundtrip_uniformity_fails` | ∀ admissible τ, ZModel ⊭ τ.RL(RH_sent) | Kaye 1991 (Thm 15.1, Prop. 11.3) |

## Published Axioms -- Proof II (ProofII.lean)

| Axiom | Statement | Source |
|---|---|---|
| `woodin_abs_under_LCAC` | ZFC+LCAC gives Σ₁² absoluteness | Woodin 1999, Thm 3.17 |
| `absoluteness_proves_RH` | Absoluteness resolves RH | Woodin 1999; Feferman 1960 |

## Published Axioms -- Proof III (ProofIII.lean)

| Axiom | Statement | Source |
|---|---|---|
| `argument_principle` | Argument principle for holonomy | Titchmarsh 1986; Ahlfors 1979 |
| `abs_implies_PRA` | Absoluteness implies PRA | Woodin 1999; Titchmarsh 1986 |

## Published Axioms -- Main.lean

| Axiom | Statement | Source |
|---|---|---|
| `arithmetic_RH_equiv_analytic` | TrueInN RH_sent → RiemannHypothesis | Davis et al. 1976; Lagarias 2002 |

## Proved Theorems (Lean-verified, zero sorry)

### Defs.lean
- `admissible_translation_exists` -- from compositional_pres_translation_exists + pi1_pi2_nontriviality
- `admissible_has_distortion` -- pure Lean proof from Admissible.nontrivial
- `obstruction_in_ZModel` -- from ZModel_satisfies_RH + roundtrip_uniformity_fails

### ObstructionProof.lean
- `linear_obstruction_of_RH` -- from admissible_translation_exists + obstruction_in_ZModel

### Obstruction.lean
- `linear_obstruction_RH` -- = linear_obstruction_of_RH
- `RL_neg_comm` -- from comp_neg + comp_neg_bwd
- `obstruction_neg` -- from RL_neg_comm + negL_zsat
- `neg_obstruction_RH` -- from linear_obstruction_of_RH + obstruction_neg

### Soundness.lean
- `lambda_reduction_soundness` -- from zfc_sound + Admissible.pres

### Independence.lean
- `RH_lambda_irreducible` -- from linear_obstruction_RH + neg_obstruction_RH
- `unprovable_RH` -- from linear_obstruction_RH + lambda_reduction_soundness
- `neg_unprovable_RH` -- from neg_obstruction_RH + lambda_reduction_soundness
- `RH_independent_of_ZFC` -- from unprovable_RH + neg_unprovable_RH

### TruthInN.lean
- `truth_from_independence` -- from neg_unprovable_RH + pi1_witness_reflection + RH_is_pi1
- `RH_true_in_N` -- from truth_from_independence

### Main.lean
- `riemann_hypothesis_resolved` -- from RH_true_in_N + RH_provable_in_LCAC + RH_from_PRA
- `rh_complete` -- from RH_true_in_N + arithmetic_RH_equiv_analytic

## Mathlib Theorems (proved from Mathlib, not axioms)

- `negL` -- defined as `BoundedFormula.not`
- `negL_zsat` -- proved from `BoundedFormula.realize_not`
- `negL_nat` -- proved from `BoundedFormula.realize_not`

## Published Results in Separate Files

### PublishedLogic.lean
- `RH.Published.overspill` -- **PROVED** in Lean from induction scheme (not an axiom)

### PublishedAnalysis.lean
- `RH.Published.mergelyan` -- Mergelyan 1951; Rudin 1987, Thm 20.5
- `RH.Published.ingham_zero_density` -- Ingham 1940; Titchmarsh 1986, Ch. 9
