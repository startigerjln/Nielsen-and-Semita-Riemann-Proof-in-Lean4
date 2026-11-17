# The Proof of the Riemann Hypothesis

J. L. Nielsen and L. Semita, Center for Topological Physics

Lean 4 + Mathlib formalization of the deductive structure of Proof I.

- `RH/Paper/Arith.lean`: arithmetic syntax, standard natural numbers, bounded formulas.
- `RH/Paper/ProofI.lean`: semantic profiles and Λ, Mathlib compactness, disagreement models, both reductios, and truth from non-refutability.
- `RH/Paper/Precision.lean`: exact equality is equivalent to verification at every dyadic precision in an Archimedean ordered field.
- `unified.tex` and `unified.pdf`: amended manuscript and matching PDF.

Λ is the set of models where a specified sentence and reconstruction disagree.
The finite-satisfiability requirement is one explicit obligation with two
reductio branches. Compactness is proved from Mathlib. The proposed separation
route is represented with its actual premises visible; unbounded quantifier
shape alone does not discharge them.

The main Lean theorems are conditional. The concrete ZFC arithmetic theory,
RH sentence, canonical maps, their preservation proofs, and the link to
Mathlib's `RiemannHypothesis` remain to be supplied. There are no project
axiom declarations or sorry placeholders; that fact does not discharge the
explicit hypotheses. See [AXIOM_PROVENANCE.md](AXIOM_PROVENANCE.md).

Run `lake build` with the pinned toolchain. The GitHub workflow checks the
same build on pushes and pull requests. Proofs II and III are not formalized.
