import RH.Paper.Mergelyan
import RH.Paper.PlantedZero
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

namespace RH.Paper.PlantedZero

/-- Interpret a pair of rational coordinates as a complex number. -/
def Point.toComplex (q : Point) : ℂ :=
  ⟨(q.1 : ℝ), (q.2 : ℝ)⟩

private theorem gaussianRationals_dense : DenseRange Point.toComplex := by
  let cast : ℚ → ℝ := fun q => q
  have dense : DenseRange cast := Rat.denseRange_cast
  exact (Complex.equivRealProdCLM.symm.surjective.denseRange.comp
    (dense.prodMap dense) Complex.equivRealProdCLM.symm.continuous)

/-- Horner form of a polynomial from its coefficient list. -/
noncomputable def polynomialOfCoefficients (coefficients : List ℂ) : Polynomial ℂ :=
  coefficients.foldr (fun a p => Polynomial.C a + Polynomial.X * p) 0

private def addCoefficients : List ℂ → List ℂ → List ℂ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addCoefficients as bs

private theorem polynomialOfCoefficients_add (as bs : List ℂ) :
    polynomialOfCoefficients (addCoefficients as bs) =
      polynomialOfCoefficients as + polynomialOfCoefficients bs := by
  induction as generalizing bs with
  | nil => simp [addCoefficients, polynomialOfCoefficients]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoefficients, polynomialOfCoefficients]
    | cons b bs =>
      simp only [addCoefficients, polynomialOfCoefficients, List.foldr_cons, map_add]
      rw [show List.foldr (fun a p => Polynomial.C a + Polynomial.X * p) 0
        (addCoefficients as bs) = polynomialOfCoefficients as + polynomialOfCoefficients bs
        from ih bs, mul_add]
      unfold polynomialOfCoefficients
      abel

private theorem polynomialOfCoefficients_monomial (n : ℕ) (a : ℂ) :
    polynomialOfCoefficients (List.replicate n 0 ++ [a]) = Polynomial.C a * Polynomial.X ^ n := by
  induction n with
  | zero => simp [polynomialOfCoefficients]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    change Polynomial.C 0 + Polynomial.X *
      polynomialOfCoefficients (List.replicate n 0 ++ [a]) = _
    rw [ih, map_zero, zero_add, pow_succ, mul_left_comm, mul_comm Polynomial.X]

private theorem exists_coefficient_list (p : Polynomial ℂ) :
    ∃ coefficients : List ℂ, polynomialOfCoefficients coefficients = p := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    obtain ⟨as, rfl⟩ := hp
    obtain ⟨bs, rfl⟩ := hq
    exact ⟨addCoefficients as bs, polynomialOfCoefficients_add as bs⟩
  | h_monomial n a =>
    exact ⟨List.replicate n 0 ++ [a], by
      rw [polynomialOfCoefficients_monomial, Polynomial.C_mul_X_pow_eq_monomial]⟩

private theorem approximate_coefficient_list
    (K : Set ℂ) (bound : ℝ) (one_le : 1 ≤ bound) (bounded : ∀ z ∈ K, ‖z‖ ≤ bound)
    (coefficients : List ℂ) (ε : ℝ) (positive : 0 < ε) :
    ∃ rs : List Point, ∀ z ∈ K,
      ‖(polynomialOfCoefficients (rs.map Point.toComplex)).eval z -
        (polynomialOfCoefficients coefficients).eval z‖ < ε := by
  induction coefficients generalizing ε with
  | nil =>
    exact ⟨[], fun z _ => by simpa [polynomialOfCoefficients] using positive⟩
  | cons a rest ih =>
    have bound_pos : 0 < bound := zero_lt_one.trans_le one_le
    obtain ⟨r, hr⟩ := gaussianRationals_dense.exists_dist_lt a (half_pos positive)
    obtain ⟨rs, hrs⟩ := ih (ε / 2 / bound) (div_pos (half_pos positive) bound_pos)
    refine ⟨r :: rs, fun z hz => ?_⟩
    let rTail := (polynomialOfCoefficients (rs.map Point.toComplex)).eval z
    let aTail := (polynomialOfCoefficients rest).eval z
    have tail : ‖rTail - aTail‖ < ε / 2 / bound := hrs z hz
    have head := hr
    rw [dist_comm, dist_eq_norm] at head
    change ‖(polynomialOfCoefficients ((r :: rs).map Point.toComplex)).eval z -
      (polynomialOfCoefficients (a :: rest)).eval z‖ < ε
    simp only [List.map_cons, polynomialOfCoefficients, List.foldr_cons,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    change ‖r.toComplex + z * rTail - (a + z * aTail)‖ < ε
    rw [show r.toComplex + z * rTail - (a + z * aTail) =
      (r.toComplex - a) + z * (rTail - aTail) by ring]
    have scaled : ‖z * (rTail - aTail)‖ < ε / 2 := by
      rw [norm_mul]
      calc
        ‖z‖ * ‖rTail - aTail‖ ≤ bound * ‖rTail - aTail‖ :=
          mul_le_mul_of_nonneg_right (bounded z hz) (norm_nonneg _)
        _ < bound * (ε / 2 / bound) := mul_lt_mul_of_pos_left tail bound_pos
        _ = ε / 2 := mul_div_cancel₀ _ (ne_of_gt bound_pos)
    exact (norm_add_le _ _).trans_lt (by linarith)

/-- Every complex polynomial admits uniform approximation on a compact
    set by polynomials given by Gaussian-rational coefficient lists. -/
theorem approximate_polynomial_by_rational_coefficients (K : Set ℂ)
    (compact : IsCompact K) (p : Polynomial ℂ) (ε : ℝ) (positive : 0 < ε) :
    ∃ coefficients : List Point, ∀ z ∈ K,
      ‖(polynomialOfCoefficients (coefficients.map Point.toComplex)).eval z - p.eval z‖ < ε := by
  obtain ⟨b, hb⟩ := compact.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨coefficients, rfl⟩ := exists_coefficient_list p
  exact approximate_coefficient_list K (max b 1) (le_max_right _ _)
    (fun z hz => (hb z hz).trans (le_max_left _ _)) coefficients ε positive

private noncomputable def rootFactor (roots : List Point) : Polynomial ℂ :=
  (roots.map (fun w => Polynomial.X - Polynomial.C w.toComplex)).prod

/-- Complex value of a rational-function code, with its numerator in
    factored form. -/
noncomputable def evalComplex (f : RationalFunction) (z : ℂ) : ℂ :=
  (rootFactor f.1).eval z *
    (polynomialOfCoefficients (f.2.1.map Point.toComplex)).eval z /
    (polynomialOfCoefficients (f.2.2.map Point.toComplex)).eval z

private theorem rootFactor_ne_zero_at (roots : List Point) (z : ℂ)
    (outside : ∀ w ∈ roots, w.toComplex ≠ z) : (rootFactor roots).eval z ≠ 0 := by
  induction roots with
  | nil => simp [rootFactor]
  | cons w rest ih =>
    simp only [rootFactor, List.map_cons, List.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm (outside w (List.mem_cons_self ..))))
      (ih (fun r hr => outside r (List.mem_cons_of_mem _ hr)))

/-- The same Gaussian-rational code both approximates on the compact set
    and yields a standard counterexample to the direct zero-location check. -/
theorem compact_approximation_with_standard_failure
    (K : Set ℂ) (target : ℂ → ℂ) (N : ℕ)
    (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (continuous : ContinuousOn target K) (holomorphic : DifferentiableOn ℂ target (interior K))
    (outside : ∀ w ∈ plantedRoots N, w.toComplex ∉ K) (ε : ℝ) (positive : 0 < ε) :
    ∃ f : RationalFunction, N < Encodable.encode f ∧
      (∀ z ∈ K, ‖evalComplex f z - target z‖ < ε) ∧
      ¬ passes (Encodable.encode f) (Encodable.encode (plantedPoint N)) 3 := by
  let factor := rootFactor (plantedRoots N)
  have nonzero (z : ℂ) (hz : z ∈ K) : factor.eval z ≠ 0 :=
    rootFactor_ne_zero_at _ z (fun w hw heq => outside w hw (heq.symm ▸ hz))
  obtain ⟨p, hp⟩ := approximate_with_polynomial_factor K target factor compact connected
    continuous holomorphic nonzero (ε / 2) (half_pos positive)
  obtain ⟨b, hb⟩ := compact.exists_bound_of_continuousOn factor.continuousOn
  have bPos : 0 < max b 1 := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨cs, hcs⟩ := approximate_polynomial_by_rational_coefficients K compact p
    (ε / 2 / max b 1) (div_pos (half_pos positive) bPos)
  let base : RationalFunction := ([], cs, (1, 0) :: List.replicate N (0, 0))
  have large : N < Encodable.encode (plant N base) := by
    apply lt_of_lt_of_le _ (denominator_length_le_code (plant N base))
    simp [plant, base]
  have defined : evalPolynomial (plantedPoint N) base.2.2 ≠ (0, 0) := by
    change evalPolynomial (plantedPoint N) ((1, 0) :: List.replicate N (0, 0)) ≠ (0, 0)
    rw [evalPolynomial_one_padded]
    decide
  refine ⟨plant N base, large, ?_, planted_code_fails N base defined⟩
  · intro z hz
    have value : evalComplex (plant N base) z =
        factor.eval z * (polynomialOfCoefficients (cs.map Point.toComplex)).eval z := by
      have one : Point.toComplex (1, 0) = 1 := by
        apply Complex.ext <;> simp [Point.toComplex]
      have zero : Point.toComplex (0, 0) = 0 := by
        apply Complex.ext <;> simp [Point.toComplex]
      have zeroCoefficients : ∀ n : ℕ,
          polynomialOfCoefficients (List.replicate n (0 : ℂ)) = 0 := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [List.replicate_succ]
          change Polynomial.C 0 +
            Polynomial.X * polynomialOfCoefficients (List.replicate n (0 : ℂ)) = 0
          simp [ih]
      have denominator : polynomialOfCoefficients (base.2.2.map Point.toComplex) = 1 := by
        change polynomialOfCoefficients (List.map Point.toComplex
          ((1, 0) :: List.replicate N (0, 0))) = 1
        rw [List.map_cons, List.map_replicate, one, zero]
        change Polynomial.C 1 + Polynomial.X * polynomialOfCoefficients (List.replicate N 0) = 1
        simp [zeroCoefficients]
      change factor.eval z * (polynomialOfCoefficients (cs.map Point.toComplex)).eval z /
        (polynomialOfCoefficients (base.2.2.map Point.toComplex)).eval z = _
      simp [denominator]
    have close := hp z hz
    rw [Polynomial.eval_mul] at close
    have scaled :
        ‖factor.eval z * ((polynomialOfCoefficients (cs.map Point.toComplex)).eval z - p.eval z)‖
          < ε / 2 := by
      rw [norm_mul]
      calc
        _ ≤ max b 1 * ‖(polynomialOfCoefficients (cs.map Point.toComplex)).eval z - p.eval z‖ :=
          mul_le_mul_of_nonneg_right ((hb z hz).trans (le_max_left _ _)) (norm_nonneg _)
        _ < max b 1 * (ε / 2 / max b 1) := mul_lt_mul_of_pos_left (hcs z hz) bPos
        _ = ε / 2 := mul_div_cancel₀ _ (ne_of_gt bPos)
    rw [value, show factor.eval z * (polynomialOfCoefficients (cs.map Point.toComplex)).eval z -
      target z =
        factor.eval z * ((polynomialOfCoefficients (cs.map Point.toComplex)).eval z - p.eval z) +
          (factor.eval z * p.eval z - target z) by ring]
    exact (norm_add_le _ _).trans_lt (by linarith)

/-- A standard code realizes any finite list of local uniform
    approximation requirements contained in a common compact set. -/
theorem finite_local_approximations_with_standard_failure
    (K : Set ℂ) (target : ℂ → ℂ) (N : ℕ)
    (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (continuous : ContinuousOn target K) (holomorphic : DifferentiableOn ℂ target (interior K))
    (outside : ∀ w ∈ plantedRoots N, w.toComplex ∉ K)
    (checks : Finset ℕ) (region : ℕ → Set ℂ) (tolerance : ℕ → ℝ)
    (contained : ∀ k ∈ checks, region k ⊆ K) (positive : ∀ k ∈ checks, 0 < tolerance k) :
    ∃ f : RationalFunction, N < Encodable.encode f ∧
      (∀ k ∈ checks, ∀ z ∈ region k, ‖evalComplex f z - target z‖ < tolerance k) ∧
      ¬ passes (Encodable.encode f) (Encodable.encode (plantedPoint N)) 3 := by
  classical
  have boundedBelow (indices : Finset ℕ) (positivity : ∀ k ∈ indices, 0 < tolerance k) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ indices, ε ≤ tolerance k := by
    induction indices using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert k rest fresh ih =>
      obtain ⟨ε, εPos, small⟩ := ih
        (fun j hj => positivity j (Finset.mem_insert_of_mem hj))
      refine ⟨min (tolerance k) ε, lt_min (positivity k (Finset.mem_insert_self _ _)) εPos,
        fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (small j hj)
  obtain ⟨ε, εPos, small⟩ := boundedBelow checks positive
  obtain ⟨f, large, approximation, failure⟩ :=
    compact_approximation_with_standard_failure K target N compact connected continuous
      holomorphic outside ε εPos
  exact ⟨f, large, fun k hk z hz =>
    (approximation z (contained k hk hz)).trans_le (small k hk), failure⟩

/-- A single code meets finitely many local zeta-approximation
    requirements and fails the direct check of its planted zero. -/
theorem finite_zeta_approximations_with_standard_failure
    (K : Set ℂ) (N : ℕ) (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (poleOutside : (1 : ℂ) ∉ K) (zerosOutside : ∀ w ∈ plantedRoots N, w.toComplex ∉ K)
    (checks : Finset ℕ) (region : ℕ → Set ℂ) (tolerance : ℕ → ℝ)
    (contained : ∀ k ∈ checks, region k ⊆ K) (positive : ∀ k ∈ checks, 0 < tolerance k) :
    ∃ f : RationalFunction, N < Encodable.encode f ∧
      (∀ k ∈ checks, ∀ z ∈ region k, ‖evalComplex f z - riemannZeta z‖ < tolerance k) ∧
      ¬ passes (Encodable.encode f) (Encodable.encode (plantedPoint N)) 3 := by
  have differentiable (z : ℂ) (hz : z ∈ K) : DifferentiableAt ℂ riemannZeta z :=
    differentiableAt_riemannZeta (fun eq => poleOutside (eq ▸ hz))
  exact finite_local_approximations_with_standard_failure K riemannZeta N compact connected
    (fun z hz => (differentiable z hz).continuousAt.continuousWithinAt)
    (fun z hz => (differentiable z (interior_subset hz)).differentiableWithinAt)
    zerosOutside checks region tolerance contained positive

end RH.Paper.PlantedZero
