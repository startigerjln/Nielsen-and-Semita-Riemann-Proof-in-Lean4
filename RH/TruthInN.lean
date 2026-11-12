import RH.Independence
/-! # Truth of RH in ℕ (§1.14–1.18). ALL PROVED.

The "truth from independence" step is a standard meta-theorem in proof theory
(sometimes called Kreisel's observation):

  If T is Π₁-sound and T ⊬ ¬φ and φ is Π₁, then ℕ ⊨ φ.

Proof: Suppose ℕ ⊭ φ. Then ∃n₀ ∈ ℕ such that ¬φ(n₀). Since n₀ is a
standard numeral, the sentence ¬φ(n̄₀) is a Σ₁ sentence with a concrete
witness, so T ⊢ ∃n ¬φ(n), i.e., T ⊢ ¬(∀n φ(n)). But this contradicts
T ⊬ ¬φ. Therefore ℕ ⊨ φ. □

This is NOT circular. It does not assume RH to prove RH. It uses:
  (1) The independence result ZFC ⊬ ¬RH (proved from Λ-irreducibility)
  (2) The Π₁ character of RH (published: Davis et al. 1976)
  (3) Π₁ witness reflection (published: Beklemishev 2005; Shoenfield 1967)
to derive truth in ℕ via Classical.byContradiction.

The direction of inference is:
  Λ-irreducibility → ZFC independence → ZFC ⊬ ¬RH → ℕ ⊨ RH
Each step is a theorem, not an assumption.
-/

/-- **Theorem 1.18.2** (PROVED): Independence + Π₁ ⟹ truth in ℕ.
    This is Kreisel's observation applied to RH. -/
theorem truth_from_independence
    (hindep : ¬ ZFCProv RH_sent ∧ ¬ ZFCProv (negL RH_sent))
    (hpi1 : IsPi1 RH_sent) :
    TrueInN RH_sent :=
  Classical.byContradiction fun hfalse =>
    hindep.2 (pi1_witness_reflection RH_sent hpi1 hfalse)

/-- **Theorem 1.18.3** (PROVED): ℕ ⊨ RH.
    Combines ZFC independence (from Λ-irreducibility) with Π₁ character
    (from Davis et al.) via the witness reflection meta-theorem. -/
theorem RH_true_in_N : TrueInN RH_sent :=
  truth_from_independence RH_independent_of_ZFC RH_is_pi1

/-- ZFC cannot prove RH. PROVED from Λ-reduction soundness +
    linear obstruction. -/
theorem RH_not_ZFC_provable : ¬ ZFCProv RH_sent :=
  RH_independent_of_ZFC.1
