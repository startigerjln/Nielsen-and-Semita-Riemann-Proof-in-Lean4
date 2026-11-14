# The Proof of the Riemann Hypothesis

J. L. Nielsen and L. Semita, Center for Topological Physics (2025)

Lean 4 + Mathlib formalization of the deductive structure of Proof I.

## Lean formalization

`RH/Paper/ProofI.lean` checks the implications from round-trip
preservation and failure to unprovability. It also checks the
independence and standard-model truth deductions under their explicit
premises. The arithmetic theory, RH sentence, and translation pair are
parameters. See [provenance](AXIOM_PROVENANCE.md) for the exact premises.

Proofs II and III are not formalized.

The reference for this formalization is Nielsen and Semita's 32-page
manuscript with the May 16, 2026 update (`OLDGOODRIEMANN.pdf`). The repository also
contains a separate manuscript revision, `unified.pdf`.
