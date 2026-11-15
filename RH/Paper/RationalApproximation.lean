import RH.Paper.Mergelyan
import RH.Paper.PlantedZero
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open Filter
open scoped BigOperators

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

private theorem compact_polynomial_approximation_with_standard_failure
    (K : Set ℂ) (target : ℂ → ℂ) (N : ℕ)
    (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (continuous : ContinuousOn target K) (holomorphic : DifferentiableOn ℂ target (interior K))
    (outside : ∀ w ∈ plantedRoots N, w.toComplex ∉ K) (ε : ℝ) (positive : 0 < ε) :
    ∃ (f : RationalFunction) (p : Polynomial ℂ), N < Encodable.encode f ∧
      (∀ z, evalComplex f z = p.eval z) ∧
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
  have value (z : ℂ) : evalComplex (plant N base) z =
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
  refine ⟨plant N base, factor * polynomialOfCoefficients (cs.map Point.toComplex), large,
    fun z => by rw [value z, Polynomial.eval_mul], ?_, planted_code_fails N base defined⟩
  · intro z hz
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
    rw [value z, show factor.eval z * (polynomialOfCoefficients (cs.map Point.toComplex)).eval z -
      target z =
        factor.eval z * ((polynomialOfCoefficients (cs.map Point.toComplex)).eval z - p.eval z) +
          (factor.eval z * p.eval z - target z) by ring]
    exact (norm_add_le _ _).trans_lt (by linarith)

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
  obtain ⟨f, _, large, _, close, failure⟩ :=
    compact_polynomial_approximation_with_standard_failure K target N compact connected
      continuous holomorphic outside ε positive
  exact ⟨f, large, close, failure⟩

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

/-- A standard rational code can meet any positive uniform error bound on
    the compact checked region and still disagree with zeta at a point of
    the Perron line outside that region. -/
theorem zeta_approximation_can_disagree_on_perron_line
    (K : Set ℂ) (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (poleOutside : (1 : ℂ) ∉ K) (c t : ℝ) (hc : 1 < c)
    (outside : (c : ℂ) + (t : ℂ) * Complex.I ∉ K)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ f : RationalFunction, (∀ z ∈ K, ‖evalComplex f z - riemannZeta z‖ < ε) ∧
      evalComplex f ((c : ℂ) + (t : ℂ) * Complex.I) ≠
        riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  let w : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
  have nonzero : riemannZeta w ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa [w, Complex.mul_re] using hc)
  have analyticAt (z : ℂ) (hz : z ∈ K) : DifferentiableAt ℂ riemannZeta z :=
    differentiableAt_riemannZeta (fun eq => poleOutside (eq ▸ hz))
  obtain ⟨p, zero, close⟩ := approximate_with_prescribed_zeros K riemannZeta {w}
    compact connected (fun z hz => (analyticAt z hz).continuousAt.continuousWithinAt)
    (fun z hz => (analyticAt z (interior_subset hz)).differentiableWithinAt)
    (by simpa only [Finset.mem_singleton, forall_eq] using outside) (ε / 2) (half_pos positive)
  let δ := min (ε / 2) (‖riemannZeta w‖ / 2)
  have δPos : 0 < δ := lt_min (half_pos positive) (half_pos (norm_pos_iff.mpr nonzero))
  obtain ⟨coefficients, approx⟩ := approximate_polynomial_by_rational_coefficients
    (insert w K) (compact.insert w) p δ δPos
  let f : RationalFunction := ([], coefficients, [(1, 0)])
  have value (z : ℂ) : evalComplex f z =
      (polynomialOfCoefficients (coefficients.map Point.toComplex)).eval z := by
    have one : Point.toComplex (1, 0) = 1 := by
      apply Complex.ext <;> simp [Point.toComplex]
    simp [f, evalComplex, rootFactor, polynomialOfCoefficients, one]
  refine ⟨f, ?_, ?_⟩
  · intro z hz
    rw [value, ← sub_add_sub_cancel _ (p.eval z)]
    refine (norm_add_le _ _).trans_lt ?_
    have h := (approx z (Set.mem_insert_of_mem _ hz)).trans_le (min_le_left _ _)
    linarith only [h, close z hz]
  · change evalComplex f w ≠ riemannZeta w
    intro eq
    have h := (approx w (Set.mem_insert _ _)).trans_le (min_le_right _ _)
    rw [← value, eq, zero w (Finset.mem_singleton_self w), sub_zero] at h
    linarith only [h, norm_nonneg (riemannZeta w)]

private theorem zeta_uniform_dirichlet_partials (σ : ℝ) (hσ : 1 < σ) :
    TendstoUniformlyOn (fun J z => ∑ j ∈ Finset.range J, LSeries.term 1 z j)
      riemannZeta atTop {z : ℂ | σ ≤ z.re} := by
  have summable : Summable (fun j => LSeries.term 1 (σ : ℂ) j) :=
    LSeriesSummable_one_iff.mpr (by simpa using hσ)
  have uniform := tendstoUniformlyOn_tsum_nat summable.norm
    (s := {z : ℂ | σ ≤ z.re}) (f := fun j z => LSeries.term 1 z j)
    (fun j z hz => LSeries.norm_term_le_of_re_le_re 1 (by simpa using hz) j)
  refine uniform.congr_right (fun z hz => ?_)
  exact (LSeriesHasSum_one (hσ.trans_le hz)).tsum_eq

/-- Lemma 1.34's finite witness on a compact checked region. One
    Gaussian-rational polynomial code has exact Taylor overlaps, agrees
    with one sufficiently long Dirichlet partial sum at all requested
    precisions on the checked subregion, and fails at its planted zero. -/
theorem finite_taylor_dirichlet_checks_with_standard_failure
    (K : Set ℂ) (N : ℕ) (compact : IsCompact K) (connected : IsConnected Kᶜ)
    (poleOutside : (1 : ℂ) ∉ K) (zerosOutside : ∀ w ∈ plantedRoots N, w.toComplex ∉ K)
    (D : Set ℂ) (dirichletCompact : IsCompact D) (contained : D ⊆ K)
    (convergenceRegion : ∀ z ∈ D, 1 < z.re) :
    ∃ (f : RationalFunction) (p : Polynomial ℂ) (J : ℕ),
      N < Encodable.encode f ∧
      (∀ z ∈ K, ‖evalComplex f z - riemannZeta z‖ < (1 / 2 : ℝ) ^ N) ∧
      (∀ center z : ℂ,
        (p.comp (Polynomial.X + Polynomial.C center)).eval (z - center) = evalComplex f z) ∧
      (∀ k ≤ N, ∀ z ∈ D,
        ‖evalComplex f z - (∑ j ∈ Finset.range J, LSeries.term 1 z j)‖ <
          (1 / 2 : ℝ) ^ k) ∧
      ¬ passes (Encodable.encode f) (Encodable.encode (plantedPoint N)) 3 := by
  let precision := (1 / 2 : ℝ) ^ N
  have positive : 0 < precision := by dsimp [precision]; positivity
  obtain ⟨σ, hσ, margin⟩ : ∃ σ : ℝ, 1 < σ ∧ ∀ z ∈ D, σ ≤ z.re := by
    by_cases nonempty : D.Nonempty
    · obtain ⟨z, hz, minimum⟩ :=
        dirichletCompact.exists_isMinOn nonempty Complex.continuous_re.continuousOn
      exact ⟨z.re, convergenceRegion z hz, fun _ hw => minimum hw⟩
    · exact ⟨2, by norm_num, fun z hz => (nonempty ⟨z, hz⟩).elim⟩
  have differentiable (z : ℂ) (hz : z ∈ K) : DifferentiableAt ℂ riemannZeta z :=
    differentiableAt_riemannZeta (fun eq => poleOutside (eq ▸ hz))
  obtain ⟨f, p, large, value, close, failure⟩ :=
    compact_polynomial_approximation_with_standard_failure K riemannZeta N compact connected
      (fun z hz => (differentiable z hz).continuousAt.continuousWithinAt)
      (fun z hz => (differentiable z (interior_subset hz)).differentiableWithinAt)
      zerosOutside (precision / 2) (half_pos positive)
  obtain ⟨J, dirichlet⟩ := (Metric.tendstoUniformlyOn_iff.mp (zeta_uniform_dirichlet_partials σ hσ)
    (precision / 2) (half_pos positive)).exists
  refine ⟨f, p, J, large, fun z hz => (close z hz).trans (half_lt_self positive),
    ?_, ?_, failure⟩
  · intro center z
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      sub_add_cancel, value z]
  · intro k hk z hz
    have tailError : ‖riemannZeta z - ∑ j ∈ Finset.range J, LSeries.term 1 z j‖ <
        precision / 2 := by
      simpa only [dist_eq_norm] using dirichlet z (margin z hz)
    have bound : precision ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    rw [← sub_add_sub_cancel _ (riemannZeta z)]
    exact ((norm_add_le _ _).trans_lt
      (by linarith only [close z (contained hz), tailError])).trans_le bound

end RH.Paper.PlantedZero
