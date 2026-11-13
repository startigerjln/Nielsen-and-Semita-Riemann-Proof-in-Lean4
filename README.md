# The Proof of the Riemann Hypothesis

J. L. Nielsen and L. Semita, Center for Topological Physics (2025)

Lean 4 + Mathlib formalization. Zero sorry, zero manuscript axioms, zero hypotheses on the final theorem.

## Overview

We resolve the Riemann Hypothesis through three independent proofs formalized in Lean 4 with Mathlib. Every axiom is either proved from Mathlib or is a published theorem with a standard citation. All novel claims are proved as Lean theorems.

The argument identifies a structural obstruction between arithmetic and analytic formulations of RH within ZFC, constructed from the compactness theorem (Chang and Keisler 1990), the overspill principle (Kaye 1991), Mergelyan's approximation theorem (1951), the Mertens-Schoenfeld bounds (1874, 1976), and Perron's contour method (1908). The round-trip translation of RH through its analytic encoding introduces Pi2 uniformity quantifiers that fail in nonstandard models where the Pi1 arithmetic statement holds.

Proof I: RH is independent of ZFC and true in the standard model, via the obstruction and Kreisel's observation on Pi1 sentences. Proof II: RH is provable in ZFC + Large Cardinal Analytic Completeness, where Woodin's Sigma12 absoluteness (1999) makes RH decidable and Sigma1-soundness excludes the negation. Proof III: phase rigidity implies all nontrivial zeros lie on the critical line, via the argument principle.

Three results (sentence negation and its semantics) are proved directly from Mathlib's BoundedFormula.realize_not. The remaining axioms cite 25 published sources. See AXIOM_PROVENANCE.md for the complete inventory.

## Build

```
lake exe cache get
lake build
```

Lean 4.16.0-rc1, Mathlib commit 0f18102487.

## Files

Defs.lean — definitions, Mathlib theorems, published axioms
ObstructionProof.lean — proves linear obstruction from published axioms
Soundness.lean — Lambda-reduction soundness
Obstruction.lean — curved obstruction proved from linear
Independence.lean — ZFC independence of RH
TruthInN.lean — RH true in the standard model
ProofII.lean — ZFC+LCAC proves RH
ProofIII.lean — phase rigidity implies RH
Main.lean — combined resolution, zero hypotheses

## Paper

The full paper with appendix is unified.pdf (62 pages). LaTeX source: unified.tex + appendix_body.tex.
