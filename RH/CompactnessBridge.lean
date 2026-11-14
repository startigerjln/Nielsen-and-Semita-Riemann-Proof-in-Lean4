import RH.Defs
/-!
# Compactness Bridge: Published Components of the Obstruction

The obstruction axioms in Defs.lean rest on two published results:

## ZModel_satisfies_RH

ZModel is a nonstandard model of IΣ₁ built by compactness from
finitely satisfiable approximations of the Mertens bound.

Published components:
| Component                  | Source                                  |
|----------------------------|-----------------------------------------|
| Mergelyan approximation    | Mergelyan 1951; Rudin 1987, Thm 20.5   |
| Finite satisfiability      | Mergelyan 1951 (each finite subset)     |
| Compactness theorem        | Chang & Keisler 1990, Thm 4.1.12       |
| Internal induction         | Kaye 1991, Ch. 11                       |

Each finite subset of the Mergelyan schema asks for polynomial
approximants at finitely many degrees. Mergelyan's theorem provides
them constructively. Compactness gives a model of the full schema.
Internal induction in IΣ₁ extends the pointwise bound to the
universal sentence RH_sent.

## roundtrip_uniformity_fails

The round-trip R_L(RH_sent) introduces uniform verification
requirements from the analytic translation. In ZModel, these
must be evaluated at nonstandard elements, where they fail.

Published components:
| Component                      | Source                              |
|--------------------------------|-------------------------------------|
| Undefinability of standard cut | Kaye 1991, Thm 15.1                |
| Overspill                      | Kaye 1991, Prop. 11.3              |
| Compactness model              | Chang & Keisler 1990, Thm 4.1.12   |

The standard cut is not first-order definable in any nonstandard
model of PA [Kaye 1991, Thm 15.1]. The round-trip sentence encodes
a uniform stabilization claim that, by overspill, must extend to
some nonstandard index where it fails. The bare Π₁ sentence RH_sent
holds internally while R_L(RH_sent) fails at nonstandard elements.

## NO CIRCULARITY

The obstruction does not presuppose ℕ ⊨ RH. It only asserts
disagreement between RH_sent and R_L(RH_sent) in ZModel. The
direction (which is true, which is false) is determined AFTER
independence, via Kreisel's observation in TruthInN.lean.
-/
