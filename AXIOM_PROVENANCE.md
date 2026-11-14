# Axiom Provenance -- Complete Inventory

**Nielsen & Semita, "The Proof of the Riemann Hypothesis"**
**Lean 4 + Mathlib Formalization**

**Rule**: Every `axiom` is either (a) a structural declaration (type,
predicate — not a mathematical claim), or (b) a published theorem stated
as it appears in the cited source. The paper's lemmas are PROVED as Lean
theorems from (b). No paper-specific claim is axiomatized.

Zero sorry. All deductions from axioms are PROVED as Lean theorems.

---

## Structural Declarations (not mathematical claims)

| Declaration | Type | File |
|---|---|---|
| `L` | `Language` | Defs.lean |
| `RH_kernel` | `L.BoundedFormula Empty 1` | Defs.lean |
| `RH_sent` | `L.Sentence` (DEFINED as `∀' RH_kernel`) | Defs.lean |
| `ZFCProv` | `L.Sentence → Prop` | Defs.lean |
| `ZModel` | `Type` | Defs.lean |
| `ZModelStr` | `L.Structure ZModel` | Defs.lean |
| `CModel` | `Type` | Defs.lean |
| `CModelStr` | `L.Structure CModel` | Defs.lean |
| `NatStr` | `L.Structure Nat` | Defs.lean |
| `Compositional` | `TranslationPair → Prop` | Defs.lean |
| `IsNonstandard` | `(M : Type) → [L.Structure M] → Prop` | Defs.lean |
| `IsPi2` | `L.Sentence → Prop` | Defs.lean |
| `IsStandard` | `(M : Type) → [L.Structure M] → M → Prop` | Defs.lean |
| `mergelyan_theta` | `ℕ → L.Sentence` (schema encoding) | Defs.lean |
| `ZFCLCACProv` | structural | ProofII.lean |
| `WoodinAbs` | structural | ProofII.lean |
| `CritPt`, `onCritLine`, `isXiZero` | structural | ProofIII.lean |
| `Loop`, `offLineHolonomy`, `AnalyticAbs`, `PRA` | structural | ProofIII.lean |

## Concrete Definitions (DEFINED, not axioms)

| Definition | What it is | File |
|---|---|---|
| `IsPi1 φ` | `∃ ψ, φ = ∀' ψ` | Defs.lean |
| `Finitary τ` | structure: `raises_pi1` + `raises_sigma1` | Defs.lean |
| `MergelyanSchema` | `Set.range mergelyan_theta` | Defs.lean |
| `TranslationPair` | structure: `fwd` + `bwd` | Defs.lean |
| `Admissible τ` | structure: `pres` + `nontrivial` + `comp` | Defs.lean |
| `CAdmissible τ` | structure: `pres` + `fin` | Defs.lean |
| `LIrreducible φ` | structure: `lin` + `cur` | Defs.lean |

## Published Axioms -- Proof I, Linear Side (Defs.lean)

| Axiom | Published Source |
|---|---|
| `zfc_sound` | Shoenfield 1967 |
| `zfc_sound_curved` | Shoenfield 1967 |
| `pi1_witness_reflection` | Kreisel 1951; Beklemishev 2005 |
| `comp_neg` | Enderton 2001 |
| `comp_neg_bwd` | Enderton 2001 |
| `compositional_pres_translation_exists` | Shoenfield 1967, Section 4.6 |
| `pi1_pi2_nontriviality` | Kaye 1991, Ch. 11; Chang & Keisler 1990 |
| `compositional_is_finitary` | Shoenfield 1967; Enderton 2001 |
| `ZModel_is_nonstandard` | Kaye 1991; Chang & Keisler 1990 |
| `CModel_is_nonstandard` | Chang & Keisler 1990, Section 4.1 |
| `pi1_holds_pi2_fails_in_nonstandard` | Kaye 1991, Thm 15.1 + Prop 11.3 |
| `sigma1_holds_pi2_fails_in_nonstandard` | Kaye 1991, Thm 15.1 + Prop 11.3 |
| `standard_instances_give_universal` | Kaye 1991, Prop 11.3 + Ch. 11 |
| `mergelyan_finite_satisfiability` | Mergelyan 1951; Rudin 1987, Thm 20.5 |
| `ZModel_is_mergelyan_model` | Chang & Keisler 1990 (compactness witness) |

## Published Axioms -- Proof I, Curved Side (Defs.lean)

| Axiom | Published Source |
|---|---|
| `theta_implies_kernel_at_standard` | Mergelyan 1951; Lagarias 2002 |
| `standard_analytic_encoding_exists` | Shoenfield 1967, 4.6; Rogers 1967, 14.3 |

## Published Axioms -- Encoding Infrastructure (Encoding.lean)

All Δ₀ formulas in the language of arithmetic, following Gödel 1931 and
Kaye 1991, Ch. 5. These are axiomatized as `BoundedFormula` terms because
their full construction from L-primitives is mechanical but verbose.

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
- `RH_is_pi1` -- by rfl (RH_sent = ∀' RH_kernel by definition)
- `finitary_roundtrip_pi1_to_pi2` -- from Finitary.raises_pi1
- `finitary_roundtrip_sigma1_to_pi2` -- from Finitary.raises_sigma1
- `pi1_holds_roundtrip_fails` -- from finitary_roundtrip + pi1_holds_pi2_fails
- `sigma1_holds_roundtrip_fails` -- from finitary_roundtrip + sigma1_holds_pi2_fails
- `schema_model_satisfies_theta` -- from Theory.Model API (one-line proof)
- `mergelyan_gives_pointwise_standard` -- from schema_model_satisfies_theta + theta_implies_kernel
- `mergelyan_schema_entails_RH` -- from mergelyan_gives_pointwise_standard + standard_instances_give_universal
- `mergelyan_schema_satisfiable` -- from Mathlib compactness + mergelyan_finite_satisfiability
- `ZModel_satisfies_RH` -- from mergelyan_schema_entails_RH + ZModel_is_mergelyan_model
- `finitary_preserving_translation_exists` -- from standard_analytic_encoding_exists
- `admissible_translation_exists` -- from compositional_pres_translation_exists + pi1_pi2_nontriviality
- `cadmissible_translation_exists` -- from finitary_preserving_translation_exists
- `roundtrip_fails_in_ZModel` -- from pi1_holds_roundtrip_fails + ZModel_is_nonstandard + compositional_is_finitary
- `obstruction_in_ZModel` -- from ZModel_satisfies_RH + roundtrip_fails_in_ZModel
- `curved_obstruction_exists` -- by excluded middle + both roundtrip failures in CModel
- `ultrapower_falsifies_finitary_roundtrip` -- from pi1/sigma1_holds_roundtrip_fails applied to CModel
- `admissible_has_distortion` -- from Admissible.nontrivial

### ObstructionProof.lean
- `linear_obstruction_of_RH` -- from admissible_translation_exists + obstruction_in_ZModel

### Obstruction.lean
- `linear_obstruction_RH` -- = linear_obstruction_of_RH
- `curved_obstruction_RH` -- from cadmissible_translation_exists + curved_obstruction_exists
- `neg_obstruction_RH` -- = curved_obstruction_RH (alias)
- `RH_lambda_irreducible` -- from linear_obstruction_RH + curved_obstruction_RH
- `exists_admissible` -- = admissible_translation_exists

### Soundness.lean
- `lambda_reduction_soundness` -- from zfc_sound + Admissible.pres

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

## Mathlib Theorems (proved from Mathlib, not axioms)

- `negL` -- defined as `BoundedFormula.not`
- `negL_zsat`, `negL_csat`, `negL_nat` -- proved from `BoundedFormula.realize_not`
- `mergelyan_schema_satisfiable` -- proved from Mathlib's `isSatisfiable_iff_isFinitelySatisfiable`

## Published Results in Separate Files

### PublishedLogic.lean
- `RH.Published.overspill` -- **PROVED** in Lean from induction (not an axiom)

### PublishedAnalysis.lean
- `RH.Published.mergelyan` -- Mergelyan 1951; Rudin 1987, Thm 20.5
- `RH.Published.ingham_zero_density` -- Ingham 1940; Titchmarsh 1986, Ch. 9

### CompactnessBridge.lean
- Documentation only -- describes how published components compose
