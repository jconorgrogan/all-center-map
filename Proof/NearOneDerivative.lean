import ExceptionalZeroWeight
import PrimitiveLFixedStripGrowthCertified
import Mathlib.Analysis.Complex.Liouville

/-!
# Near-one derivative bounds from the promoted fixed-strip estimate

The unconditional theorem below records exactly what the current promoted
fixed-strip estimate yields by Cauchy's inequality.  Its conductor exponent is
`2`; the module does not disguise this as the desired subpower estimate.
-/

namespace MAPZeroFreeSiegelSpine

open Complex Set Metric

noncomputable section

/-- Cauchy's estimate on a fixed radius-`1/4` disk, using the promoted
`q^2` fixed-strip bound. -/
theorem norm_deriv_LFunction_near_one_le_q_sq
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x : ℝ} (hxlo : 3 / 4 ≤ x) (hxhi : x ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
      20000 * (q : ℝ) ^ 2 := by
  have hdiff : DiffContOnCl ℂ (DirichletCharacter.LFunction χ)
      (ball (x : ℂ) (1 / 4 : ℝ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hcircle : ∀ z ∈ sphere (x : ℂ) (1 / 4 : ℝ),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 5000 * (q : ℝ) ^ 2 := by
    intro z hz
    have hdist : ‖z - (x : ℂ)‖ = 1 / 4 := by
      simpa [dist_eq_norm] using (mem_sphere.mp hz)
    have hreDiff : |z.re - x| ≤ 1 / 4 := by
      calc
        |z.re - x| = |(z - (x : ℂ)).re| := by simp
        _ ≤ ‖z - (x : ℂ)‖ := Complex.abs_re_le_norm _
        _ = 1 / 4 := hdist
    have hzlo : -1 ≤ z.re := by
      rw [abs_le] at hreDiff
      linarith
    have hzhi : z.re ≤ 2 := by
      rw [abs_le] at hreDiff
      linarith
    have hshift : ‖z + 3‖ ≤ 5 := by
      calc
        ‖z + 3‖ = ‖(z - (x : ℂ)) + ((x : ℂ) + 3)‖ := by
          congr 1
          ring
        _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) + 3‖ := norm_add_le _ _
        _ = 1 / 4 + |x + 3| := by
          rw [hdist, show ((x : ℂ) + 3) = ((x + 3 : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 5 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
    have hbase := PLInteriorGrowth.norm_LFunction_fixedStrip_le χ hχ hzlo hzhi
    calc
      ‖DirichletCharacter.LFunction χ z‖ ≤
          200 * (q : ℝ) ^ 2 * ‖z + 3‖ ^ 2 := hbase
      _ ≤ 200 * (q : ℝ) ^ 2 * 5 ^ 2 := by gcongr
      _ = 5000 * (q : ℝ) ^ 2 := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := DirichletCharacter.LFunction χ) (c := (x : ℂ))
    (R := (1 / 4 : ℝ)) (C := 5000 * (q : ℝ) ^ 2)
    (by norm_num) hdiff hcircle
  calc
    ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
        (5000 * (q : ℝ) ^ 2) / (1 / 4) := hcauchy
    _ = 20000 * (q : ℝ) ^ 2 := by ring

/-- The exact requested quantifier pattern in the range actually supported by
current APIs: every conductor exponent `delta >= 2` works uniformly on the
fixed near-one interval `[3/4,1]`. -/
theorem exists_nearOne_derivative_rpow_bound_of_two_le
    {δ : ℝ} (hδ : 2 ≤ δ) :
    ∃ M η : ℝ, 0 < M ∧ 0 < η ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        ∀ β : ℝ, 1 - η ≤ β → β ≤ 1 →
          DirichletCharacter.LFunction χ β = 0 →
          ∀ x ∈ Set.Ico β 1,
            ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
              M * Real.rpow (q : ℝ) δ := by
  refine ⟨20000, 1 / 4, by norm_num, by norm_num, ?_⟩
  intro q _ χ _hprim hχ _hreal β hβlo hβhi _hzero x hx
  have hxlo : 3 / 4 ≤ x := by
    have := hx.1
    norm_num at hβlo ⊢
    linarith
  have hxhi : x ≤ 1 := hx.2.le
  have hbase := norm_deriv_LFunction_near_one_le_q_sq χ hχ hxlo hxhi
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hpow : (q : ℝ) ^ (2 : ℕ) ≤ Real.rpow (q : ℝ) δ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hqone hδ
  exact hbase.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

end
end MAPZeroFreeSiegelSpine

#print axioms MAPZeroFreeSiegelSpine.norm_deriv_LFunction_near_one_le_q_sq
#print axioms MAPZeroFreeSiegelSpine.exists_nearOne_derivative_rpow_bound_of_two_le
