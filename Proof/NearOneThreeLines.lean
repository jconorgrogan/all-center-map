import NearOneDerivative
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.PSeries

/-!
# Unequal-boundary interpolation for Dirichlet L-functions near one

This staging module keeps the conductor-free absolutely-convergent boundary
separate from the `q^2` left boundary.  Hadamard's three-lines theorem then
retains the varying conductor exponent which the symmetric fixed-strip API
deliberately coarsens away.
-/

namespace MAPZeroFreeSiegelSpine

open Complex Set Metric LSeries
open Complex.HadamardThreeLines

noncomputable section

private def nearOneNormalizedL {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ z / (z + 3) ^ 2

/-- A finite conductor-free majorant for the right boundary `Re s = 1+r`.
The use of a `tsum` avoids inserting an unproved explicit integral-test
constant into the interpolation argument. -/
def rightEdgePSeries (r : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun _n : ℕ => (1 : ℂ)) ((1 + r : ℝ) : ℂ) n‖

private theorem summable_rightEdgePSeries {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ =>
      ‖LSeries.term (fun _n : ℕ => (1 : ℂ)) ((1 + r : ℝ) : ℂ) n‖) := by
  exact (LSeriesSummable_of_bounded_of_one_lt_re
    (f := fun _n : ℕ => (1 : ℂ)) (m := 1)
    (fun _n _hn => by simp) (by simp; linarith)).norm

theorem one_le_rightEdgePSeries {r : ℝ} (hr : 0 < r) :
    1 ≤ rightEdgePSeries r := by
  have hs := summable_rightEdgePSeries hr
  have hone := hs.le_tsum 1 (fun j hj => norm_nonneg _)
  simpa [rightEdgePSeries, LSeries.norm_term_eq] using hone

/-- Absolute convergence bounds every primitive or imprimitive character on
`Re s = 1+r` by a constant depending on `r` alone. -/
theorem norm_LFunction_rightEdge_le_pSeries
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z.re = 1 + r) :
    ‖DirichletCharacter.LFunction χ z‖ ≤ rightEdgePSeries r := by
  have hzone : 1 < z.re := by linarith
  have hχsum : Summable (LSeries.term (fun n : ℕ => χ n) z) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _hn => χ.norm_le_one n) hzone
  have honesum := summable_rightEdgePSeries hr
  rw [DirichletCharacter.LFunction_eq_LSeries χ hzone]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hχsum.norm).trans ?_
  apply Summable.tsum_le_tsum _ hχsum.norm honesum
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · rw [hz]
    exact div_le_div_of_nonneg_right (by simpa using χ.norm_le_one n) (by positivity)

private theorem nearOneNormalizedL_diffContOnCl
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {r : ℝ} (hr : 0 < r) :
    DiffContOnCl ℂ (nearOneNormalizedL χ) (verticalStrip (-1) (1 + r)) := by
  let d : ℂ → ℂ := fun z => (z + 3) ^ 2
  have hd : Differentiable ℂ d :=
    (differentiable_id.add_const 3).pow 2
  have hdne : ∀ z ∈ closure (verticalStrip (-1) (1 + r)), d z ≠ 0 := by
    intro z hz
    have hzmem : z.re ∈ Set.Icc (-1 : ℝ) (1 + r) := by
      rw [verticalStrip, Complex.closure_preimage_re,
        closure_Ioo (by linarith : (-1 : ℝ) ≠ 1 + r)] at hz
      exact hz
    have hzadd : z + 3 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith [hzmem.1]
    exact pow_ne_zero _ hzadd
  have hinv : DiffContOnCl ℂ d⁻¹ (verticalStrip (-1) (1 + r)) :=
    hd.diffContOnCl.inv hdne
  have hL : DiffContOnCl ℂ (DirichletCharacter.LFunction χ)
      (verticalStrip (-1) (1 + r)) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hmul := hinv.smul hL
  simpa [nearOneNormalizedL, d, div_eq_inv_mul, mul_comm] using hmul

private theorem norm_nearOneNormalizedL_le_q_sq
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {z : ℂ} (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 2) :
    ‖nearOneNormalizedL χ z‖ ≤ 200 * (q : ℝ) ^ 2 := by
  have hzadd : z + 3 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have hden : 0 < ‖z + 3‖ ^ 2 := by positivity
  rw [nearOneNormalizedL, norm_div, norm_pow]
  apply (div_le_iff₀ hden).2
  exact PLInteriorGrowth.norm_LFunction_fixedStrip_le χ hχ hzlo hzhi

private theorem nearOneNormalizedL_bddAbove
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    BddAbove ((norm ∘ nearOneNormalizedL χ) '' verticalClosedStrip (-1) (1 + r)) := by
  refine ⟨200 * (q : ℝ) ^ 2, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact norm_nearOneNormalizedL_le_q_sq χ hχ hz.1 (by linarith [hz.2])

private theorem norm_nearOneNormalizedL_rightEdge
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z.re = 1 + r) :
    ‖nearOneNormalizedL χ z‖ ≤ rightEdgePSeries r := by
  have hden : 1 ≤ ‖(z + 3) ^ 2‖ := by
    rw [norm_pow]
    have hre : 4 ≤ |(z + 3).re| := by
      rw [abs_of_nonneg (by simp; linarith)]
      simp [hz]
      linarith
    have hnorm : 4 ≤ ‖z + 3‖ := hre.trans (Complex.abs_re_le_norm _)
    nlinarith
  rw [nearOneNormalizedL, norm_div]
  exact (div_le_self (norm_nonneg _) hden).trans
    (norm_LFunction_rightEdge_le_pSeries χ hr hz)

/-- The unequal-boundary Hadamard estimate which preserves the small
conductor exponent near `Re s = 1`. -/
theorem norm_nearOneNormalizedL_le_interp
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {z : ℂ}
    (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 1 + r) :
    ‖nearOneNormalizedL χ z‖ ≤
      Real.rpow (200 * (q : ℝ) ^ 2)
          (1 - (z.re - (-1)) / ((1 + r) - (-1))) *
        Real.rpow (rightEdgePSeries r)
          ((z.re - (-1)) / ((1 + r) - (-1))) := by
  apply Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (l := (-1 : ℝ)) (u := 1 + r) (a := 200 * (q : ℝ) ^ 2)
    (b := rightEdgePSeries r) (by linarith)
  · exact ⟨hzlo, hzhi⟩
  · exact nearOneNormalizedL_diffContOnCl χ hχ hr
  · exact nearOneNormalizedL_bddAbove χ hχ hr hr1
  · intro w hw
    have hw' : w.re = -1 := by simpa using hw
    exact norm_nearOneNormalizedL_le_q_sq χ hχ (by linarith) (by linarith)
  · intro w hw
    exact norm_nearOneNormalizedL_rightEdge χ hr (by simpa using hw)

/-- On a width-`r` neighborhood of one, the unequal-boundary estimate has
conductor exponent at most `2*r`. -/
theorem norm_nearOneNormalizedL_le_q_rpow
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {δ r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hrδ : 2 * r ≤ δ)
    {z : ℂ} (hzlo : 1 - r ≤ z.re) (hzhi : z.re ≤ 1 + r) :
    ‖nearOneNormalizedL χ z‖ ≤
      200 * rightEdgePSeries r * Real.rpow (q : ℝ) δ := by
  let α : ℝ := 1 - (z.re - (-1)) / ((1 + r) - (-1))
  let θ : ℝ := (z.re - (-1)) / ((1 + r) - (-1))
  have hden : 0 < (1 + r) - (-1 : ℝ) := by linarith
  have hα0 : 0 ≤ α := by
    dsimp [α]
    rw [sub_nonneg]
    apply (div_le_one hden).2
    linarith
  have hαr : α ≤ r := by
    dsimp [α]
    rw [show 1 - (z.re - (-1)) / ((1 + r) - (-1)) =
      ((1 + r) - z.re) / (2 + r) by field_simp; ring]
    have hden2 : 0 < 2 + r := by linarith
    apply (div_le_iff₀ hden2).2
    nlinarith
  have hα1 : α ≤ 1 := by linarith
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one hden).2 (by linarith)
  have hinterp := norm_nearOneNormalizedL_le_interp χ hχ hr hr1
    (z := z) (by linarith) hzhi
  change ‖nearOneNormalizedL χ z‖ ≤
      Real.rpow (200 * (q : ℝ) ^ 2) α *
        Real.rpow (rightEdgePSeries r) θ at hinterp
  have h200 : Real.rpow (200 : ℝ) α ≤ 200 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 200) hα1
    simpa using h
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqeq : Real.rpow ((q : ℝ) ^ 2) α =
      Real.rpow (q : ℝ) (2 * α) := by
    calc
      Real.rpow ((q : ℝ) ^ 2) α =
          Real.rpow (Real.rpow (q : ℝ) (2 : ℝ)) α := by
            exact congrArg (fun u : ℝ => Real.rpow u α)
              (Real.rpow_natCast (q : ℝ) 2).symm
      _ = Real.rpow (q : ℝ) (2 * α) :=
        (Real.rpow_mul (Nat.cast_nonneg q) 2 α).symm
  have hqpow : Real.rpow ((q : ℝ) ^ 2) α ≤ Real.rpow (q : ℝ) δ := by
    rw [hqeq]
    exact Real.rpow_le_rpow_of_exponent_le hqone (by nlinarith)
  have hBpow : Real.rpow (rightEdgePSeries r) θ ≤ rightEdgePSeries r := by
    have h := Real.rpow_le_rpow_of_exponent_le (one_le_rightEdgePSeries hr) hθ1
    simpa using h
  have hsplit : Real.rpow (200 * (q : ℝ) ^ 2) α =
      Real.rpow 200 α * Real.rpow ((q : ℝ) ^ 2) α :=
    Real.mul_rpow (by norm_num) (sq_nonneg (q : ℝ))
  have hfirst : Real.rpow 200 α * Real.rpow ((q : ℝ) ^ 2) α ≤
      200 * Real.rpow (q : ℝ) δ :=
    mul_le_mul h200 hqpow
      (Real.rpow_nonneg (sq_nonneg (q : ℝ)) α) (by norm_num)
  calc
    ‖nearOneNormalizedL χ z‖ ≤
        Real.rpow (200 * (q : ℝ) ^ 2) α *
          Real.rpow (rightEdgePSeries r) θ := hinterp
    _ = (Real.rpow 200 α * Real.rpow ((q : ℝ) ^ 2) α) *
          Real.rpow (rightEdgePSeries r) θ := by
      rw [hsplit]
    _ ≤ (200 * Real.rpow (q : ℝ) δ) * rightEdgePSeries r := by
      exact mul_le_mul
        hfirst hBpow
        (Real.rpow_nonneg (zero_le_one.trans (one_le_rightEdgePSeries hr)) θ)
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg (Nat.cast_nonneg q) δ))
    _ = 200 * rightEdgePSeries r * Real.rpow (q : ℝ) δ := by ring

/-- Cauchy's inequality turns the interpolated near-one bound into a direct
subpower derivative estimate. -/
theorem norm_deriv_LFunction_near_one_le_q_rpow
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {δ r x : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hrδ : 2 * r ≤ δ)
    (hxlo : 1 - r / 2 ≤ x) (hxhi : x ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
      (10000 * rightEdgePSeries r / r) * Real.rpow (q : ℝ) δ := by
  have hdiff : DiffContOnCl ℂ (DirichletCharacter.LFunction χ)
      (ball (x : ℂ) (r / 2)) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hcircle : ∀ z ∈ sphere (x : ℂ) (r / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤
        5000 * rightEdgePSeries r * Real.rpow (q : ℝ) δ := by
    intro z hz
    have hdist : ‖z - (x : ℂ)‖ = r / 2 := by
      simpa [dist_eq_norm] using (mem_sphere.mp hz)
    have hreDiff : |z.re - x| ≤ r / 2 := by
      calc
        |z.re - x| = |(z - (x : ℂ)).re| := by simp
        _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r / 2 := hdist
    have hzlo : 1 - r ≤ z.re := by
      rw [abs_le] at hreDiff
      linarith
    have hzhi : z.re ≤ 1 + r := by
      rw [abs_le] at hreDiff
      linarith
    have hnorm := norm_nearOneNormalizedL_le_q_rpow χ hχ hr hr1 hrδ hzlo hzhi
    have hshift : ‖z + 3‖ ≤ 5 := by
      calc
        ‖z + 3‖ = ‖(z - (x : ℂ)) + ((x : ℂ) + 3)‖ := by
          congr 1
          ring
        _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) + 3‖ := norm_add_le _ _
        _ = r / 2 + |x + 3| := by
          rw [hdist, show ((x : ℂ) + 3) = ((x + 3 : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 5 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
    have hzadd : z + 3 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
    have hrecover : DirichletCharacter.LFunction χ z =
        nearOneNormalizedL χ z * (z + 3) ^ 2 := by
      simp [nearOneNormalizedL, hzadd]
    have hmain0 : 0 ≤ 200 * rightEdgePSeries r * Real.rpow (q : ℝ) δ :=
      mul_nonneg
        (mul_nonneg (by norm_num)
          (zero_le_one.trans (one_le_rightEdgePSeries hr)))
        (Real.rpow_nonneg (Nat.cast_nonneg q) δ)
    rw [hrecover, norm_mul, norm_pow]
    calc
      ‖nearOneNormalizedL χ z‖ * ‖z + 3‖ ^ 2 ≤
          (200 * rightEdgePSeries r * Real.rpow (q : ℝ) δ) * 5 ^ 2 := by
        exact mul_le_mul hnorm (by gcongr) (sq_nonneg _) hmain0
      _ = 5000 * rightEdgePSeries r * Real.rpow (q : ℝ) δ := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := DirichletCharacter.LFunction χ) (c := (x : ℂ))
    (R := r / 2)
    (C := 5000 * rightEdgePSeries r * Real.rpow (q : ℝ) δ)
    (by positivity) hdiff hcircle
  calc
    ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
        (5000 * rightEdgePSeries r * Real.rpow (q : ℝ) δ) / (r / 2) := hcauchy
    _ = (10000 * rightEdgePSeries r / r) * Real.rpow (q : ℝ) δ := by
      field_simp
      <;> ring

/-- The requested near-one subpower derivative theorem.  Primitivity,
real-valuedness, and the zero hypotheses are retained in the public interface
needed by the exceptional-zero route, although the analytic estimate itself
only uses nonprincipality. -/
theorem exists_nearOne_derivative_subpower_bound
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M η : ℝ, 0 < M ∧ 0 < η ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        ∀ β : ℝ, 1 - η ≤ β → β ≤ 1 →
          DirichletCharacter.LFunction χ β = 0 →
          ∀ x ∈ Set.Ico β 1,
            ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
              M * Real.rpow (q : ℝ) δ := by
  let r : ℝ := min 1 (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min zero_lt_one (by positivity)
  have hr1 : r ≤ 1 := by
    exact min_le_left _ _
  have hrδ : 2 * r ≤ δ := by
    have := min_le_right (1 : ℝ) (δ / 2)
    dsimp [r]
    linarith
  refine ⟨10000 * rightEdgePSeries r / r, r / 2, ?_, by positivity, ?_⟩
  · exact div_pos (mul_pos (by norm_num)
      (lt_of_lt_of_le zero_lt_one (one_le_rightEdgePSeries hr))) hr
  · intro q _ χ _hprim hχ _hreal β hβlo _hβhi _hzero x hx
    apply norm_deriv_LFunction_near_one_le_q_rpow χ hχ hr hr1 hrδ
    · linarith [hβlo, hx.1]
    · exact hx.2.le

end
end MAPZeroFreeSiegelSpine

#print axioms MAPZeroFreeSiegelSpine.one_le_rightEdgePSeries
#print axioms MAPZeroFreeSiegelSpine.norm_LFunction_rightEdge_le_pSeries
#print axioms MAPZeroFreeSiegelSpine.norm_nearOneNormalizedL_le_interp
#print axioms MAPZeroFreeSiegelSpine.norm_nearOneNormalizedL_le_q_rpow
#print axioms MAPZeroFreeSiegelSpine.norm_deriv_LFunction_near_one_le_q_rpow
#print axioms MAPZeroFreeSiegelSpine.exists_nearOne_derivative_subpower_bound
