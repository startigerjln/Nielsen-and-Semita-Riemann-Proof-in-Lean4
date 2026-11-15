# The Proof of the Riemann Hypothesis

J. L. Nielsen and L. Semita, Center for Topological Physics (2025)

Lean 4 + Mathlib formalization of the deductive structure of Proof I.

## Lean formalization

- `RH/Paper/Arith.lean`: arithmetic syntax, standard natural numbers, bounded formulas.
- `RH/Paper/ProofI.lean`: compactness-to-disagreement, non-refutability, independence and truth-from-non-refutability, as conditional theorems with explicit inputs.

The formalization now follows the manuscript's overspill/compactness route, rather than a rational-approximation argument. The central RH-specific finite-satisfiability statement is an explicit, unproved input. The actual ZFC arithmetic theory, concrete arithmetic RH sentence, two-language canonical translation, and connection to Mathlib's `RiemannHypothesis` remain to be formalized. See [AXIOM_PROVENANCE.md](AXIOM_PROVENANCE.md).

No project axiom declarations or sorry placeholders are used in these modules; this does not make the conditional conclusions unconditional RH proofs. The Lean build workflow checks the code on push. Proofs II and III are not formalized.

Manuscript source: [unified.tex](unified.tex). The checked-in [unified.pdf](unified.pdf) may still be the earlier version pending regeneration.
