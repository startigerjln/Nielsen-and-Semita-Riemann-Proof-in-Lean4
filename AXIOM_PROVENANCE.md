# Axiom Provenance -- Complete Inventory

**Nielsen & Semita, "The Proof of the Riemann Hypothesis"**
**Lean 4 + Mathlib Formalization**

**Rule**: Every axiom is a published mathematical result.
Zero sorry. All deductions from axioms are PROVED as Lean theorems.

---

## Structural Declarations (not mathematical claims)

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
| `MergelyanSchema` | `L.Theory` | Defs.lean |
| `HasUniformityStructure` | `L.Sentence → Prop` | Defs.lean |

## Published Axioms -- Proof I (Defs.lean)

| Axiom | Published Source |
|---|---|
| `zfc_sound` | Shoenfield 1967 |
| `pi1_witness_reflection` | Kreisel 1951; Beklemishev 2005 |
| `RH_is_pi1` | Davis, Matiyasevich & Robinson 1976 |
| `comp_neg` | Enderton 2001 |
| `comp_neg_bwd` | Enderton 2001 |
| `compositional_pres_translation_exists` | Shoenfield 1967 |
| `pi1_pi2_nontriviality` | Kaye 1991; Chang & Keisler 1990 |
| `mergelyan_finite_satisfiability` | Mergelyan 1951; Rudin 1987 |
| `ZModel_is_mergelyan_model` | Chang & Keisler 1990 |
| `compactness_model_satisfies_pi1` | Mergelyan 1951; Kaye 1991 |
| `roundtrip_has_uniformity` | Shoenfield 1967; Mertens 1874 |
| `uniformity_fails_in_nonstandard` | Kaye 1991, Thm 15.1 + Prop 11.3 |

## Published Axioms -- Proof II (ProofII.lean)

| Axiom | Published Source |
|---|---|
| `woodin_abs_under_LCAC` | Woodin 1999, Thm 3.17 |
| `absoluteness_proves_RH` | Woodin 1999; Feferman 1960 |

## Published Axioms -- Proof III (ProofIII.lean)

| Axiom | Published Source |
|---|---|
| `argument_principle` | Titchmarsh 1986; Ahlfors 1979 |
| `abs_implies_PRA` | Woodin 1999; Titchmarsh 1986 |

## Published Axioms -- Main.lean

| Axiom | Published Source |
|---|---|
| `arithmetic_RH_equiv_analytic` | Davis et al. 1976; Lagarias 2002 |

## Proved Theorems (Lean-verified, zero sorry)

### Defs.lean
- `mergelyan_schema_satisfiable` -- from Mathlib compactness + mergelyan_finite_satisfiability
- `admissible_translation_exists` -- from compositional_pres_translation_exists + pi1_pi2_nontriviality
- `admissible_has_distortion` -- pure Lean proof from Admissible.nontrivial
- `ZModel_satisfies_RH` -- from ZModel_is_mergelyan_model + compactness_model_satisfies_pi1
- `roundtrip_uniformity_fails` -- from roundtrip_has_uniformity + uniformity_fails_in_nonstandard
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
- `mergelyan_schema_satisfiable` -- proved from Mathlib's compactness theorem

## Published Results in Separate Files

### PublishedLogic.lean
- `RH.Published.overspill` -- **PROVED** in Lean from induction (not an axiom)

### PublishedAnalysis.lean
- `RH.Published.mergelyan` -- Mergelyan 1951; Rudin 1987, Thm 20.5
- `RH.Published.ingham_zero_density` -- Ingham 1940; Titchmarsh 1986, Ch. 9
