import KoukExercise12TwoEndpointScalars

/-! Power-saving geometry for the selected pointwise contour. -/

namespace MAPKoukExercise12TwoPowerGeometry

open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

theorem halfIntegerPoint_rpow_half_le_threeQuarter
    {X t : ℝ} (hX : 9 ≤ X) (ht : t ∈ Set.Icc X (2 * X)) :
    Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) ≤
      Real.rpow X (3 / 4 : ℝ) := by
  obtain ⟨hN, _hxLower, hxUpper, -⟩ :=
    MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range
      (by linarith) ht
  let x := halfIntegerPoint ⌊t⌋₊
  have hXpos : 0 < X := by linarith
  have hxpos : 0 < x := by dsimp [x]; exact halfIntegerPoint_pos _
  have hsqrt0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsqrt3 : 3 ≤ Real.sqrt X := by
    nlinarith [Real.sq_sqrt hXpos.le]
  have hthree : 3 * X ≤ Real.rpow X (3 / 2 : ℝ) := by
    calc
      3 * X ≤ Real.sqrt X * X :=
        mul_le_mul_of_nonneg_right hsqrt3 hXpos.le
      _ = X * Real.sqrt X := by ring
      _ = Real.rpow X 1 * Real.rpow X (1 / 2 : ℝ) := by
        rw [show Real.rpow X 1 = X from Real.rpow_one X,
          show Real.rpow X (1 / 2 : ℝ) = Real.sqrt X from
            (Real.sqrt_eq_rpow X).symm]
      _ = Real.rpow X (1 + 1 / 2 : ℝ) :=
        (Real.rpow_add hXpos 1 (1 / 2 : ℝ)).symm
      _ = Real.rpow X (3 / 2 : ℝ) := by norm_num
  have hxUpper' : x ≤ 3 * X := by simpa only [x] using hxUpper
  have hxbase : x ≤ Real.rpow X (3 / 2 : ℝ) := hxUpper'.trans hthree
  calc
    Real.rpow x (1 / 2 : ℝ) ≤
        Real.rpow (Real.rpow X (3 / 2 : ℝ)) (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hxpos.le hxbase (by norm_num)
    _ = Real.rpow X ((3 / 2 : ℝ) * (1 / 2 : ℝ)) :=
      (Real.rpow_mul hXpos.le (3 / 2 : ℝ) (1 / 2 : ℝ)).symm
    _ = Real.rpow X (3 / 4 : ℝ) := by norm_num

theorem halfIntegerPoint_rpow_sigma_le_threeQuarter
    {X t sigma : ℝ} (hX : 9 ≤ X) (ht : t ∈ Set.Icc X (2 * X))
    (hsigma : sigma ≤ 1 / 2) :
    Real.rpow (halfIntegerPoint ⌊t⌋₊) sigma ≤
      Real.rpow X (3 / 4 : ℝ) := by
  have hxone : 1 ≤ halfIntegerPoint ⌊t⌋₊ := by
    obtain ⟨hN, -, -, -⟩ :=
      MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range
        (by linarith) ht
    have hNR : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  exact (Real.rpow_le_rpow_of_exponent_le hxone hsigma).trans
    (halfIntegerPoint_rpow_half_le_threeQuarter hX ht)

end
end MAPKoukExercise12TwoPowerGeometry

#print axioms MAPKoukExercise12TwoPowerGeometry.halfIntegerPoint_rpow_half_le_threeQuarter
#print axioms MAPKoukExercise12TwoPowerGeometry.halfIntegerPoint_rpow_sigma_le_threeQuarter
