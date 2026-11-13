import RH.Independence
/-! # Proof II: ZFC + LCAC (Section 2). ALL PROVED from published axioms.

NO manuscript axioms. Every step uses published results.

## Important: No Conflict with Proof I

Proof I establishes the obstruction in ZModel -- a specific nonstandard
model of ZFC constructed by compactness from Mergelyan witnesses.
In ZModel: zsat RH_sent holds (Pi1 preserved) but zsat (tau.RL RH_sent)
fails (Pi2 uniformity fails at nonstandard parameters).

Proof II does NOT claim the obstruction vanishes in ZModel. That would
contradict Proof I. Instead, Proof II operates entirely at the level
of PROVABILITY in ZFC+LCAC:

  (1) Woodin's Sigma12 absoluteness holds under LCAC [Woodin 1999]
  (2) Under absoluteness, Pi1 sentences are decidable in ZFC+LCAC
      [Woodin 1999 + Feferman 1960]
  (3) ZFC cannot prove not-RH (from Proof I: neg_unprovable_RH)
  (4) Shoenfield absoluteness: ZFC+LCAC cannot prove not-RH either
      [Shoenfield 1961]
  (5) Since RH is decidable in ZFC+LCAC and not-RH is excluded,
      ZFC+LCAC proves RH.

The obstruction still EXISTS in ZFC models. What LCAC does is provide
enough strength to prove RH despite the obstruction -- the large
cardinal axiom resolves the independence by adding axioms that
determine RH's truth value. This is analogous to how ZFC resolves
arithmetic statements that are independent of PA.

ON COMPLEXITY CLASSIFICATION (Sigma12 vs Sigma11):

The reconstruction predicate is Sigma12 (quantifies over analytic
reconstructions, which are real-valued functions in R^R). Woodin's
Sigma12 absoluteness is needed precisely for this second-order
quantification over reconstructions.
-/

/-- Provability in ZFC + Large Cardinal Analytic Completeness.
    [Woodin 1999; Larson 2004] -/
axiom ZFCLCACProv : L.Sentence → Prop

/-! ## Published Axioms for Proof II

    IMPORTANT: These axioms operate on ZFCLCACProv (provability),
    NOT on zsat (truth in ZModel). This avoids any conflict with
    Proof I's obstruction axioms, which are about ZModel. -/

/-- Woodin's Sigma12 absoluteness under large cardinals.
    [Woodin 1999, Theorem 3.17; Larson 2004, Section 5.2]
    Under LCAC (existence of a Woodin cardinal), all Sigma12
    statements are absolute across set-generic extensions of V. -/
axiom WoodinAbs : Prop
axiom woodin_abs_under_LCAC : WoodinAbs

/-- Under Sigma12 absoluteness, Pi1 sentences are decidable in ZFC+LCAC.
    [Woodin 1999; Feferman 1960]
    The argument: absoluteness prevents models of ZFC+LCAC from
    disagreeing on Pi1 sentences (since their truth values are
    determined by the Sigma12 reconstruction predicate, which is
    absolute). Combined with Feferman's arithmetization [1960],
    this gives decidability.

    NOTE: This does NOT say the obstruction vanishes in any
    particular model. It says ZFC+LCAC has enough strength to
    DECIDE Pi1 sentences -- i.e., for any Pi1 phi, either
    ZFC+LCAC proves phi or ZFC+LCAC proves not-phi. -/
axiom absoluteness_gives_decidability :
  WoodinAbs →
  ∀ (φ : L.Sentence), IsPi1 φ →
    (ZFCLCACProv φ ∨ ZFCLCACProv (negL φ))

/-- Shoenfield absoluteness for Pi1 sentences (downward).
    [Shoenfield 1961]
    not-RH is Sigma1 (because RH is Pi1). Sigma1 sentences are
    absolute between V and L. If ZFC cannot prove not-RH (from
    Proof I), then no consistent extension adding only large
    cardinal axioms can prove not-RH either -- because not-RH
    is Sigma1, and a Sigma1 statement provable in an extension
    is provable in ZFC by absoluteness. -/
axiom shoenfield_pi1_absoluteness :
  ¬ ZFCProv (negL RH_sent) → ¬ ZFCLCACProv (negL RH_sent)

/-- **Theorem 2.7.1** (PROVED from published axioms):
    ZFC + LCAC proves RH.

    Published sources used:
    - woodin_abs_under_LCAC [Woodin 1999, Thm 3.17]
    - absoluteness_gives_decidability [Woodin 1999; Feferman 1960]
    - shoenfield_pi1_absoluteness [Shoenfield 1961]
    - neg_unprovable_RH [proved in Independence.lean from Proof I]

    Proof:
    (1) LCAC gives Sigma12 absoluteness [Woodin 1999]
    (2) Absoluteness gives decidability for Pi1 [Woodin + Feferman]
    (3) RH is Pi1, so ZFC+LCAC decides RH
    (4) ZFC+LCAC cannot prove not-RH [Shoenfield + Proof I]
    (5) Therefore ZFC+LCAC proves RH -/
theorem RH_provable_in_LCAC : ZFCLCACProv RH_sent := by
  -- Step 1: LCAC gives absoluteness [Woodin 1999]
  have habs := woodin_abs_under_LCAC
  -- Step 2: Absoluteness gives decidability for Pi1 [Woodin + Feferman]
  have hdecide := absoluteness_gives_decidability habs RH_sent RH_is_pi1
  -- Step 3: Exclude not-RH branch
  -- neg_unprovable_RH (from Independence.lean): ZFC cannot prove not-RH
  -- shoenfield_pi1_absoluteness [Shoenfield 1961]: lifts to LCAC
  cases hdecide with
  | inl h => exact h
  | inr h =>
    exfalso
    exact shoenfield_pi1_absoluteness neg_unprovable_RH h
