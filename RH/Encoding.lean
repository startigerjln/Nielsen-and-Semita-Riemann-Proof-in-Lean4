import RH.Defs
/-!
# Encoding Theorems

Connection between the names in Defs.lean and the constructions in LArith.
The step "θ_k implies RH_kernel at standard elements" is open; see
`theta_implies_kernel_at_standard` in Defs.lean.
-/

open FirstOrder

namespace RH.Encoding

theorem lagarias_eq_RH_kernel : RH.LArith.lagariasFormula = RH_kernel := rfl

theorem mergelyan_theta_eq :
    ∀ k, RH.LArith.mergelyan_theta_concrete k = mergelyan_theta k := by
  intro k; rfl

end RH.Encoding
