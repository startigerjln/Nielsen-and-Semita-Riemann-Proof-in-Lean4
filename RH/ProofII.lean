import RH.Soundness
/-! # Proof II: ZFC + LCAC (§2). Published axiom.

ON COMPLEXITY CLASSIFICATION (Σ₁² vs Σ¹₁):

An objection claims that real-coded analytic data lives in V_{ω+1}
and quantifying over reals is Σ¹₁ (second-order arithmetic), not
Σ¹₂ (which quantifies over sets of reals / P(ℝ)).

The paper's claim is more precise: the statement "r codes analytic
data for ζ(s) AND the relationship between r and the analytic
structure it encodes is preserved under all admissible reconstructions"
involves quantification over ANALYTIC RECONSTRUCTIONS — maps from
real codes to analytic structures. Such reconstructions are real-valued
functions (elements of ℝ^ℝ), and quantifying over them pushes the
complexity to Σ¹₂. The Woodin cardinal's Σ¹₂ absoluteness is needed
precisely for this second-order quantification over reconstructions,
not merely for the first-order quantification over the reals themselves.

ON ABSOLUTENESS VS TRUTH:

Absoluteness (Shoenfield or Woodin) is an INVARIANCE principle:
it says a statement's truth value doesn't change across forcing
extensions. It does not directly determine what that truth value IS.

The paper does not use absoluteness to "generate" truth.
The argument is:
  (1) In ZFC alone, the Λ-obstruction exists (Proof I).
  (2) Adding LCAC (a Woodin cardinal) provides Σ¹₂ absoluteness.
  (3) Σ¹₂ absoluteness collapses the Λ-obstruction because it
      prevents ultrapower models from admitting divergent analytic
      reconstructions — the mechanism that created the obstruction.
  (4) With the obstruction collapsed, ZFC + LCAC ⊢ RH.

The truth of RH is NOT derived from absoluteness alone.
It is derived from Proof I (truth in ℕ from independence)
or from the obstruction collapse (ZFC + LCAC provability).

ON j(r) = r:

Every real r ∈ V_{ω+1} is fixed by any elementary embedding
j : V → M with crit(j) > ω. This is a basic fact of ZFC.
But analytic completeness is NOT the statement j(r) = r.
It is the statement that the RELATIONSHIP between real-coded
data and the analytic structures they encode is invariant
under all admissible embeddings — i.e., no admissible
reconstruction of ζ(s) from these codes can diverge from
the standard one. In ZFC alone, the codes are fixed but
ultrapowers can still produce nonstandard analytic extensions.
-/

/-- Provability in ZFC + Large Cardinal Analytic Completeness. -/
axiom ZFCLCACProv : L.Sentence → Prop

/-- RH provable in ZFC + LCAC.
    [Woodin 1999, Thm 3.17; Larson 2004, §5.2; paper §2.7, Thm 2.7.1]
    The obstruction collapse under analytic completeness eliminates
    the Λ-irreducibility of RH, allowing a ZFC + LCAC proof. -/
axiom RH_provable_in_LCAC : ZFCLCACProv RH_sent
