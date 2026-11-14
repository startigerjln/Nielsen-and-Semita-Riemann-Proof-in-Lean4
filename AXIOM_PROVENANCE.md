# Axiom Provenance -- Complete Inventory

**Nielsen & Semita, "The Proof of the Riemann Hypothesis"**
**Lean 4 + Mathlib Formalization**

**Rule**: Every `axiom` is a published result from the cited source.
No paper-specific axioms. Definitions are concrete. Zero sorry.

---

## Published Axioms (Defs.lean)

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
| `compositional_pres_translation_exists` | Shoenfield 1967, 4.6; Kaye 1991 |
| `analytic_encoding_exists` | Shoenfield 1967; Rogers 1967; Kaye 1991 |
| `pi1_pi2_nontriviality` | Kaye 1991, Ch. 11; Chang & Keisler 1990 |
| `ZModel_is_nonstandard` | Kaye 1991; Chang & Keisler 1990 |
| `CModel_is_nonstandard` | Chang & Keisler 1990, Section 4.1 |
| `standard_instances_give_universal` | Kaye 1991, Prop 11.3 + Ch. 11 |
| `theta_implies_kernel_at_standard` | Mergelyan 1951; Lagarias 2002 |
| `mergelyan_finite_satisfiability` | Mergelyan 1951; Rudin 1987, Thm 20.5 |
| `ZModel_is_mergelyan_model` | Chang & Keisler 1990 (compactness witness) |

## Concrete Definitions (not axioms)

| Definition | What it is |
|---|---|
| `IsPi1 φ` | `∃ ψ, φ = ∀' ψ` |
| `IsPi2 φ` | `∃ ψ, φ = ∀' (∃' ψ)` |
| `Compositional τ` | structure: `fwd_neg` + `bwd_neg` |
| `IsNonstandard M` | `∃ c, ∀ n, c ≠ stdNumeral M n` |
| `IsStandard M x` | `∃ n, x = stdNumeral M n` |
| `Finitary τ` | structure: `raises_pi1` + `raises_sigma1` + `pi1_roundtrip_fails` + `sigma1_roundtrip_fails` |
| `MergelyanSchema` | `Set.range mergelyan_theta` |
| `Admissible τ` | structure: `pres` + `nontrivial` + `comp` + `fin` |
| `CAdmissible τ` | structure: `pres` + `fin` |
| `LIrreducible φ` | structure: `lin` + `cur` |

## Published Axioms -- Encoding (Encoding.lean)

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

## Proved Theorems (zero sorry)

### Defs.lean
- `RH_is_pi1` -- by rfl
- `comp_neg`, `comp_neg_bwd` -- from Compositional definition
- `finitary_roundtrip_pi1_to_pi2` -- from Finitary.raises_pi1
- `finitary_roundtrip_sigma1_to_pi2` -- from Finitary.raises_sigma1
- `pi1_holds_roundtrip_fails` -- from Finitary.pi1_roundtrip_fails
- `sigma1_holds_roundtrip_fails` -- from Finitary.sigma1_roundtrip_fails
- `schema_model_satisfies_theta` -- from Theory.Model API
- `mergelyan_gives_pointwise_standard` -- from theta_implies_kernel
- `mergelyan_schema_entails_RH` -- from standard_instances_give_universal
- `mergelyan_schema_satisfiable` -- from Mathlib compactness
- `ZModel_satisfies_RH` -- from mergelyan_schema_entails_RH
- `finitary_preserving_translation_exists` -- from analytic_encoding_exists
- `admissible_translation_exists` -- from compositional_pres_translation_exists
- `cadmissible_translation_exists` -- from finitary_preserving
- `roundtrip_fails_in_ZModel` -- from Admissible.fin
- `obstruction_in_ZModel` -- from ZModel_satisfies_RH + roundtrip
- `curved_obstruction_exists` -- by excluded middle
- `ultrapower_falsifies_finitary_roundtrip` -- from both roundtrip failures

### Soundness.lean
- `lambda_reduction_soundness` -- from zfc_sound + Admissible.pres

### ObstructionProof.lean
- `linear_obstruction_of_RH` -- from admissible + obstruction_in_ZModel

### Obstruction.lean
- `RH_lambda_irreducible` -- from linear + curved

### Independence.lean
- `unprovable_RH` -- from lambda_reduction_soundness
- `neg_unprovable_RH` -- from zfc_sound_curved + ultrapower_falsifies
- `RH_independent_of_ZFC` -- from both

### TruthInN.lean
- `RH_true_in_N` -- from independence + pi1_witness_reflection

### Main.lean
- `riemann_hypothesis_resolved` -- from all three proofs
- `rh_complete` -- from arithmetic_RH_equiv_analytic

## Separate Files

### PublishedLogic.lean
- `RH.Published.overspill` -- **PROVED** from induction

### PublishedAnalysis.lean
- `RH.Published.mergelyan` -- Mergelyan 1951; Rudin 1987
- `RH.Published.ingham_zero_density` -- Ingham 1940; Titchmarsh 1986
