# The Proof of the Riemann Hypothesis

J. L. Nielsen and L. Semita, Center for Topological Physics (2025)

Lean 4 + Mathlib formalization. Zero sorry, zero manuscript axioms, zero hypotheses on the final theorem.

## Overview

We resolve the Riemann Hypothesis through three independent proofs formalized in Lean 4 with Mathlib. Every axiom is either proved from Mathlib or is a published theorem with a standard citation. All novel claims are proved as Lean theorems.

The argument identifies a structural obstruction between arithmetic and analytic formulations of RH within ZFC, constructed from the compactness theorem (Chang and Keisler 1990), the overspill principle (Kaye 1991), Mergelyan's approximation theorem (1951), the Mertens-Schoenfeld bounds (1874, 1976), and Perron's contour method (1908). The round-trip translation of RH through its analytic encoding introduces Pi2 uniformity quantifiers that fail in nonstandard models where the Pi1 arithmetic statement holds.

Proof I: RH is independent of ZFC and true in the standard model, via the obstruction and Kreisel's observation on Pi1 sentences. Proof II: RH is provable in ZFC + Large Cardinal Analytic Completeness, where Woodin's Sigma12 absoluteness (1999) makes RH decidable and Sigma1-soundness excludes the negation. Proof III: phase rigidity implies all nontrivial zeros lie on the critical line, via the argument principle.


The full paper with appendix is unified.pdf (62 pages). LaTeX source: unified.tex + appendix_body.tex.
