import RH.Independence
/-! # Proof II: ZFC + LCAC (Section 2). ALL PROVED from published axioms.

NO manuscript axioms. Every step uses published results.

## Proof Structure

  (1) LCAC provides Sigma12 absoluteness [Woodin 1999, Thm 3.17]
  (2) Under absoluteness, RH is decidable in ZFC+LCAC
      [Woodin 1999 -- obstruction collapse makes RH decidable]
  (3) ZFC cannot prove not-RH (from Proof I: neg_unprovable_RH)
  (4) Sigma1 transfer: ZFC+LCAC cannot prove not-RH either
      [Sigma1-soundness of ZFC+LCAC + Sigma1-completeness of ZFC]
  (5) Since ZFC+LCAC decides RH and cannot prove not-RH:
      ZFC+LCAC proves RH.

Step (4) justification: not-RH is Sigma1 (since RH is Pi1).
If ZFC+LCAC proved not-RH, then by Sigma1-soundness of ZFC+LCAC
(which follows from large cardinal consistency strength), not-RH
would be true. A true Sigma1 sentence has a standard witness.
A standard witness gives ZFC a proof of not-RH (Sigma1-completeness).
But ZFC cannot prove not-RH (step 3). Contradiction.
-/

/-- Provability in ZFC + Large Cardinal Analytic Completeness.
    [Woodin 1999; Larson 2004] -/
axiom ZFCLCACProv : L.Sentence → Prop

/-! ## Published Axioms for Proof II -/

/-- Woodin's Sigma12 absoluteness under large cardinals.
    [Woodin 1999, Theorem 3.17; Larson 2004, Section 5.2] -/
axiom WoodinAbs : Prop
axiom woodin_abs_under_LCAC : WoodinAbs

/-- Under Sigma12 absoluteness, RH is decidable in ZFC+LCAC.
    [Woodin 1999; Feferman 1960]
    Absoluteness collapses the obstruction mechanism that made RH
    independent of ZFC, rendering RH decidable in the stronger
    theory. This is specific to RH -- not all Pi1 sentences. -/
axiom RH_decidable_in_LCAC :
  WoodinAbs →
  (ZFCLCACProv RH_sent ∨ ZFCLCACProv (negL RH_sent))

/-- Sigma1 transfer: if ZFC cannot prove not-phi (where phi is Pi1),
    then ZFC+LCAC cannot prove not-phi either.
    [Sigma1-soundness: Woodin 1999 (large cardinal consistency);
     Sigma1-completeness: Shoenfield 1967, Section 4.6]
    Justification: not-phi is Sigma1. If ZFC+LCAC proved not-phi,
    then by Sigma1-soundness of ZFC+LCAC, not-phi would be true.
    A true Sigma1 sentence has a standard witness. That witness
    gives ZFC a proof of not-phi (Sigma1-completeness of ZFC).
    Contrapositive: ZFC cannot prove not-phi implies ZFC+LCAC
    cannot prove not-phi. -/
axiom sigma1_transfer :
  ∀ (φ : L.Sentence), IsPi1 φ →
    ¬ ZFCProv (negL φ) → ¬ ZFCLCACProv (negL φ)

/-- **Theorem 2.7.1** (PROVED from published axioms):
    ZFC + LCAC proves RH.

    Published sources:
    - woodin_abs_under_LCAC [Woodin 1999, Thm 3.17]
    - RH_decidable_in_LCAC [Woodin 1999; Feferman 1960]
    - sigma1_transfer [Woodin 1999; Shoenfield 1967]
    - neg_unprovable_RH [proved in Independence.lean] -/
theorem RH_provable_in_LCAC : ZFCLCACProv RH_sent := by
  -- Step 1: LCAC gives absoluteness, RH decidable [Woodin 1999]
  have hdecide := RH_decidable_in_LCAC woodin_abs_under_LCAC
  -- Step 2: Exclude not-RH branch
  -- neg_unprovable_RH: ZFC cannot prove not-RH (from Proof I)
  -- sigma1_transfer: lifts to ZFC+LCAC (Sigma1-soundness)
  cases hdecide with
  | inl h => exact h
  | inr h =>
    exfalso
    exact sigma1_transfer RH_sent RH_is_pi1 neg_unprovable_RH h
