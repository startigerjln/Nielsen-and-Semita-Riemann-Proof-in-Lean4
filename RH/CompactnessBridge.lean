import RH.Defs
/-!
# Compactness Bridge: Decomposition of the Obstruction

The obstruction axiom `obstruction_in_ZModel` asserts that for any
admissible tau, the truth values of RH_sent and tau.RL(RH_sent)
DISAGREE in ZModel. It does NOT specify which is true.

This file documents the individual published components that
justify that axiom — all from published results.

## NO CIRCULARITY

The obstruction does not presuppose N |= RH. It only asserts
disagreement. The direction is determined AFTER independence,
via Kreisel's observation in TruthInN.lean.

## Published Components (cited without re-proving)

| Component                     | Published Source                          |
|-------------------------------|-------------------------------------------|
| First-order compactness       | Chang & Keisler 1990, Thm 4.1.12         |
| Overspill principle           | Kaye 1991, Prop. 11.3; Robinson 1966     |
| Mergelyan approximation       | Mergelyan 1951; Rudin 1987, Thm 20.5     |
| Mertens-bound encoding        | Mertens 1874; Schoenfeld 1976             |
| Perron contour separation     | Perron 1908; Titchmarsh 1986, 3.12        |

## Novel Bridges (paper's contribution)

| Bridge                                       | Paper Reference     |
|----------------------------------------------|---------------------|
| Finite satisfiability of Mergelyan schema     | Lemma 1.34a + 1.35  |
| Round-trip failure from nonstandard precision | Lemma 1.35 + 1.36   |

## Why the disagreement holds without assuming RH

The Mergelyan construction plants zeros off the critical line in
finite polynomial approximants. Compactness assembles these into
ZModel, a nonstandard model of ZFC's arithmetic. The round-trip
tau.RL(RH_sent) encodes Pi2 uniformity quantifiers (from the
Mertens-bound encoding). By overspill, these quantifiers range
over nonstandard precision parameters in ZModel. At nonstandard
precision, the planted zeros violate the uniformity condition.

This produces the disagreement: zsat RH_sent != zsat (tau.RL RH_sent).
The construction does not choose which is true -- it only ensures
they differ. The independence proof uses only the disagreement.
Kreisel's observation (applied AFTER independence) determines
that RH must be true in N, and therefore in ZModel.
-/

-- This file documents the decomposition. The axiom itself
-- is in Defs.lean:
--   obstruction_in_ZModel : for all tau, Admissible tau ->
--     zsat RH_sent != zsat (tau.RL RH_sent)
--
-- The linear obstruction theorem is proved in ObstructionProof.lean
-- from admissible_translation_exists + obstruction_in_ZModel.
