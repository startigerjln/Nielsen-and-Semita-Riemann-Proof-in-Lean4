# Formalization instructions

- Credit the mathematical work to Jenny Lorraine Nielsen and Lucis Semita.
  Do not add assistant coauthorship.
- Follow Proof I's reductio direction: hypothetical provability implies
  round-trip preservation; a proved disagreement witness contradicts it.
  Failure is the desired conclusion of the witness construction. Do not
  change the goal into unconditional round-trip preservation.
- Express the model target positively: there exists a model of the target
  theory satisfying the specified original statement and falsifying its
  reconstruction. Keep the target-theory condition explicit.
- After obtaining unrefutability, the reflection branch excludes a standard
  finite counterexample and concludes standard arithmetic truth.
- Custom axioms may state only accurately sourced published results.
  Prove original paper claims; do not move them into axioms, structure fields,
  or theorem hypotheses and then report a complete formalization.
- Mathematical side conditions of published tools must be checked in each
  application. Distinguish a theorem with remaining input premises from a
  final application that supplies proofs of those premises.
- Preserve proved upstream results when working downstream. Report any exact
  missing connection or discrepancy without claiming it has been discharged.
- Run Lean and inspect both theorem signatures and `#print axioms` before
  reporting completion. An empty custom-axiom list alone does not discharge
  theorem parameters.
