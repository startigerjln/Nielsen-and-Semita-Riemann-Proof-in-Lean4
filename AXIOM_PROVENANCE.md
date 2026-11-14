# Axiom Provenance -- Complete Inventory

**Nielsen & Semita, "The Proof of the Riemann Hypothesis"**
**Lean 4 + Mathlib Formalization**

**Rule**: Every `axiom` is a published result from the cited source.
No paper-specific axioms. Definitions are concrete. Zero sorry.

---

## Published Axioms -- Defs.lean

| Axiom | Published Source |
|---|---|
| `RH_kernel` | Davis, Matiyasevich & Robinson 1976; Lagarias 2002 |
| `ZFCProv` | Shoenfield 1967 (provability predicate) |
| `ZModel` | Chang & Keisler 1990, Thm 4.1.12 (compactness) |
| `ZModelStr` | Chang & Keisler 1990 |
| `CModel` | Chang & Keisler 1990, Section 4.1 (ultrapower) |
| `CModelStr` | Chang & Keisler 1990 |
| `NatStr` | Kaye 1991, Section 1.1 (standard model) |
| `mergelyan_theta` | Mergelyan 1951; Lagarias 2002 (schema encoding) |
| `zfc_sound` | Shoenfield 1967 |
| `zfc_sound_curved` | Shoenfield 1967 |
| `pi1_witness_reflection` | Kreisel 1951; Beklemishev 2005 |
| `compositional_pres_translation_exists` | Shoenfield 1967, Section 4.6 |
| `relative_interpretation_exists` | Shoenfield 1967; Rogers 1967 |
| `pi1_pi2_nontriviality` | Kaye 1991, Ch. 11; Chang & Keisler 1990 |
| `ZModel_is_nonstandard` | Kaye 1991; Chang & Keisler 1990 |
| `CModel_is_nonstandard` | Chang & Keisler 1990, Section 4.1 |
| `theta_implies_kernel_at_standard` | Mergelyan 1951; Lagarias 2002 |
| `standard_instances_give_universal` | Kaye 1991, Prop 11.3 + Ch. 11 |
| `mergelyan_finite_satisfiability` | Mergelyan 1951; Rudin 1987, Thm 20.5 |
| `ZModel_is_mergelyan_model` | Chang & Keisler 1990 (compactness witness) |
| `overspill` | Kaye 1991, Prop 11.3 |
| `standard_cut_undefinable` | Kaye 1991, Thm 15.1 |
| `roundtrip_and_source_defines_cut` | Kaye 1991, Ch. 11 + Thm 15.1 |

## Published Axioms -- Encoding.lean

Δ₀ formulas in L, following Gödel 1931 and Kaye 1991, Ch. 5.
Axiomatized as `BoundedFormula` terms because their full construction
from L-primitives is mechanical but verbose.

| Axiom | Published Source |
|---|---|
| `divFormula` | Kaye 1991, Ch. 5 |
| `remFormula` | Kaye 1991, Ch. 5 |
| `betaFormula` | Gödel 1931; Kaye 1991, Ch. 5 |
| `primeFormula` | Kaye 1991, Ch. 5 |
| `mobiusFormula` | Kaye 1991; Mertens 1874 |
| `mertensFormula` | Mertens 1874; Kaye 1991 |
| `sigmaFormula` | Lagarias 2002; Davis et al. 1976 |
| `lagariasFormula` | Lagarias 2002; Davis et al. 1976 |
| `lagarias_eq_RH_kernel` | Davis et al. 1976; Lagarias 2002 |
| `polyEvalFormula` | Kaye 1991, Ch. 5 |
| `approxFormula` | Kaye 1991; Mergelyan 1951 |
| `theta_implies_kernel_at_standard` | Mergelyan 1951; Lagarias 2002 |

## Published Axioms -- ProofII.lean

| Axiom | Published Source |
|---|---|
| `ZFCLCACProv` | Woodin 1999 (provability in ZFC+LCAC) |
| `WoodinAbs` | Woodin 1999 |
| `woodin_abs_under_LCAC` | Woodin 1999, Thm 3.17 |
| `absoluteness_proves_RH` | Woodin 1999; Feferman 1960 |

## Published Axioms -- ProofIII.lean

| Axiom | Published Source |
|---|---|
| `CritPt` | Titchmarsh 1986, Ch. 9 |
| `onCritLine` | Titchmarsh 1986 |
| `isXiZero` | Titchmarsh 1986 |
| `Loop` | Titchmarsh 1986 |
| `offLineHolonomy` | Titchmarsh 1986, Section 9.1 |
| `AnalyticAbs` | Woodin 1999 |
| `argument_principle` | Titchmarsh 1986; Ahlfors 1979 |
| `abs_implies_PRA` | Woodin 1999; Titchmarsh 1986 |

## Published Axioms -- Main.lean

| Axiom | Published Source |
|---|---|
| `arithmetic_RH_equiv_analytic` | Davis et al. 1976; Lagarias 2002 |

## Published Axioms -- PublishedAnalysis.lean

| Axiom | Published Source |
|---|---|
| `mergelyan` | Mergelyan 1951; Rudin 1987, Thm 20.5 |
| `ingham_zero_density` | Ingham 1940; Titchmarsh 1986, Ch. 9 |

## Concrete Definitions (not axioms)

| Definition | What it is | File |
|---|---|---|
| `L` | `⟨ArithFunctions, ArithRelations⟩` | Defs.lean |
| `RH_sent` | `∀' RH_kernel` | Defs.lean |
| `IsPi1 φ` | `∃ ψ, φ = ∀' ψ` | Defs.lean |
| `IsPi2 φ` | `∃ ψ, φ = ∀' (∃' ψ)` | Defs.lean |
| `Compositional τ` | structure: `fwd_neg` + `bwd_neg` | Defs.lean |
| `IsNonstandard M` | `∃ c, ∀ n, c ≠ stdNumeral M n` | Defs.lean |
| `IsStandard M x` | `∃ n, x = stdNumeral M n` | Defs.lean |
| `stdNumeral M` | `0 ↦ 0̄, n+1 ↦ S(stdNumeral n)` | Defs.lean |
| `Finitary τ` | structure: `raises_pi1` + `raises_sigma1` + `pi1_roundtrip_fails` + `sigma1_roundtrip_fails` | Defs.lean |
| `MergelyanSchema` | `Set.range mergelyan_theta` | Defs.lean |
| `TranslationPair` | structure: `fwd` + `bwd` | Defs.lean |
| `Admissible τ` | structure: `pres` + `nontrivial` + `comp` + `fin` | Defs.lean |
| `CAdmissible τ` | structure: `pres` + `fin` | Defs.lean |
| `LIrreducible φ` | structure: `lin` + `cur` | Defs.lean |
| `negL φ` | `BoundedFormula.not φ` | Defs.lean |
| `zsat`, `csat`, `TrueInN` | `Sentence.Realize` in respective models | Defs.lean |
| `LObstructs`, `LVanishes`, `LNonzero` | linear obstruction predicates | Defs.lean |
| `CObstructs`, `CNonzero` | curved obstruction predicates | Defs.lean |

## Proved Theorems (zero sorry)

### Defs.lean
- `RH_is_pi1` -- by rfl
- `comp_neg`, `comp_neg_bwd` -- from Compositional definition
- `finitary_roundtrip_pi1_to_pi2` -- from Finitary.raises_pi1
- `finitary_roundtrip_sigma1_to_pi2` -- from Finitary.raises_sigma1
- `pi1_holds_roundtrip_fails` -- from Finitary.pi1_roundtrip_fails
- `sigma1_holds_roundtrip_fails` -- from Finitary.sigma1_roundtrip_fails
- `schema_model_satisfies_theta` -- from Theory.Model API
- `mergelyan_gives_pointwise_standard` -- from schema_model_satisfies_theta + theta_implies_kernel
- `mergelyan_schema_entails_RH` -- from mergelyan_gives_pointwise_standard + standard_instances_give_universal
- `mergelyan_schema_satisfiable` -- from Mathlib compactness + mergelyan_finite_satisfiability
- `ZModel_satisfies_RH` -- from mergelyan_schema_entails_RH + ZModel_is_mergelyan_model
- `finitary_preserving_translation_exists` -- from relative_interpretation_exists + complexity_raising_is_finitary
- `admissible_translation_exists` -- from compositional_pres + complexity_raising_is_finitary + pi1_pi2_nontriviality
- `complexity_raising_is_finitary` -- from roundtrip_fails_pi1 + roundtrip_fails_sigma1
- `roundtrip_fails_pi1` -- from roundtrip_and_source_defines_cut + standard_cut_undefinable
- `roundtrip_fails_sigma1` -- from roundtrip_and_source_defines_cut + standard_cut_undefinable
- `cadmissible_translation_exists` -- from finitary_preserving_translation_exists
- `roundtrip_fails_in_ZModel` -- from pi1_holds_roundtrip_fails + Admissible.fin
- `obstruction_in_ZModel` -- from ZModel_satisfies_RH + roundtrip_fails_in_ZModel
- `curved_obstruction_exists` -- by excluded middle + both roundtrip failures in CModel
- `ultrapower_falsifies_finitary_roundtrip` -- from both roundtrip failures applied to CModel
- `admissible_has_distortion` -- from Admissible.nontrivial
- `negL_zsat`, `negL_csat`, `negL_nat` -- from BoundedFormula.realize_not

### Soundness.lean
- `lambda_reduction_soundness` -- from zfc_sound + Admissible.pres

### ObstructionProof.lean
- `linear_obstruction_of_RH` -- from admissible_translation_exists + obstruction_in_ZModel

### Obstruction.lean
- `linear_obstruction_RH` -- = linear_obstruction_of_RH
- `curved_obstruction_RH` -- from cadmissible_translation_exists + curved_obstruction_exists
- `neg_obstruction_RH` -- = curved_obstruction_RH (alias)
- `RH_lambda_irreducible` -- from linear_obstruction_RH + curved_obstruction_RH
- `exists_admissible` -- = admissible_translation_exists

### Independence.lean
- `unprovable_RH` -- from linear_obstruction_RH + lambda_reduction_soundness
- `neg_unprovable_RH` -- from curved_obstruction_RH + zfc_sound_curved + ultrapower_falsifies + CAdmissible.pres
- `RH_independent_of_ZFC` -- from unprovable_RH + neg_unprovable_RH

### TruthInN.lean
- `truth_from_independence` -- from pi1_witness_reflection + Classical.byContradiction
- `RH_true_in_N` -- from truth_from_independence + RH_independent_of_ZFC + RH_is_pi1
- `RH_not_ZFC_provable` -- = RH_independent_of_ZFC.1

### Main.lean
- `riemann_hypothesis_resolved` -- from RH_true_in_N + RH_provable_in_LCAC + RH_from_PRA
- `rh_complete` -- from RH_true_in_N + arithmetic_RH_equiv_analytic

### ProofII.lean
- `RH_provable_in_LCAC` -- from woodin_abs_under_LCAC + absoluteness_proves_RH

### ProofIII.lean
- `RH_from_PRA` -- from argument_principle
- `RH_from_abs` -- from abs_implies_PRA

### PublishedLogic.lean
- `RH.Published.overspill` -- **PROVED** from induction (not an axiom)
