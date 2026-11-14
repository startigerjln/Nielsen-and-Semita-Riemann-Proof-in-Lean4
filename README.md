# The Proof of the Riemann Hypothesis

J. L. Nielsen and L. Semita, Center for Topological Physics (2025)

Lean 4 + Mathlib formalization of the deductive structure of Proof I.

## Lean formalization

`RH/Paper/ProofI.lean` formalizes Section 1 of the paper (version of May 16, 2026). It compiles with Lean 4.16.0, with no `axiom` and no `sorry`.

Proved in Lean: Uniform Preservation (Lemma 1.5.6), Round-Trip Adequacy (Theorem 1.7.13), the reductio step of Theorem 1.6.1, and, from the assumptions below, ZFC-undecidability of RH (Corollary 1.13.2) and truth of RH in the standard model (Theorem 1.18.3).

Assumed, as explicit hypotheses of those theorems: two published results (the Π₁ form of RH; Π₁ witness reflection) and two results of the paper not yet formalized (Theorem 1.7.6 for RH and its symmetric case for ¬RH). See `AXIOM_PROVENANCE.md`.

Proofs II and III are not formalized.

The full paper with appendix is unified.pdf (62 pages). LaTeX source: unified.tex + appendix_body.tex.
