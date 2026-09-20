import KoukInverseWideZeroClearance
import QuantitativeFiniteAperture

/-!
# Per-character good height in Koukoulopoulos Theorem 11.3

The source proof first moves from a requested cutoff `H` to a character-
dependent height `T ∈ (H,H+1)`.  Only the six unit zero slices which can meet
the top or bottom edge enter the pigeonhole argument.  Consequently the
inverse clearance costs one local zero count, not the whole divisor and not
a union over the AP family.
-/

namespace KoukTheorem113PerCharacterGoodHeight

open Set Complex DirichletZeros QuantitativeFiniteAperture
open WideDiskBlaschkeAssembly WideDiskLocalMass WideDiskLFunctionGrowth
open MAPKoukExercise12TwoLocalHorizontalAperture
open KoukInverseWideZeroClearance

noncomputable section

/-- Literal per-character ordinate selection used in the proof of Theorem
11.3. -/
theorem exists_goodHeight_with_localCoordinateClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    ∃ T ∈ Set.Ioo H (H + 1),
      ∀ a ∈ exerciseLocalImagCoordinates chi H,
        exerciseHorizontalClearance chi H ≤ |T - a| := by
  obtain ⟨T, hT, hclear⟩ :=
    exists_mem_Ioo_with_finset_clearance
      (exerciseLocalImagCoordinates chi H)
      (a := H) (b := H + 1) (by linarith)
  refine ⟨T, hT, ?_⟩
  intro a ha
  simpa [exerciseHorizontalClearance] using hclear a ha

private theorem clearance_le_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    exerciseHorizontalClearance chi H ≤ 1 := by
  unfold exerciseHorizontalClearance
  have hcard : (0 : ℝ) ≤ ((exerciseLocalImagCoordinates chi H).card : ℝ) := by
    positivity
  have hden : (1 : ℝ) ≤
      4 * (((exerciseLocalImagCoordinates chi H).card : ℝ) + 1) := by
    nlinarith
  exact (one_div_le_one_div_of_le (by norm_num) hden).trans_eq (by norm_num)

/-- The selected ordinate clears the direct primitive wide disks at both
horizontal sides, for every real coordinate. -/
theorem directWideClearance_of_goodHeight
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {H T : ℝ} (hH : 4 ≤ H)
    (hT : T ∈ Set.Ioo H (H + 1))
    (hclear : ∀ a ∈ exerciseLocalImagCoordinates chi H,
      exerciseHorizontalClearance chi H ≤ |T - a|) :
    (∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi (-T),
      exerciseHorizontalClearance chi H ≤
        ‖((r : ℂ) + Complex.I * (-T) - rho)‖) ∧
    (∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi T,
      exerciseHorizontalClearance chi H ≤
        ‖((r : ℂ) + Complex.I * T - rho)‖) := by
  have hd1 := clearance_le_one chi H
  constructor
  · intro r rho hrho
    have hfull : rho ∈ zeroSupport chi 0 (H + 4) :=
      mem_zeroSupport_of_mem_wide_at_negative_height chi hprim hH hT hrho
    by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hcoord : -rho.im ∈ exerciseLocalImagCoordinates chi H :=
        mem_exerciseLocalImagCoordinates_of_mem_global_bottom chi hfull hrange
      have hordinate := hclear (-rho.im) hcoord
      have him := Complex.abs_im_le_norm
        (((r : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖((r : ℂ) + Complex.I * (-T) - rho)‖ := by simpa using him
      rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
      exact hordinate.trans hraw
    · have hfar : 1 ≤ |T - (-rho.im)| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hT.1])]
          linarith [hT.1]
        · rw [abs_of_nonpos (by linarith [hT.2])]
          linarith [hT.2]
      have him := Complex.abs_im_le_norm
        (((r : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖((r : ℂ) + Complex.I * (-T) - rho)‖ := by simpa using him
      rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
      exact hd1.trans (hfar.trans hraw)
  · intro r rho hrho
    have hfull : rho ∈ zeroSupport chi 0 (H + 4) :=
      mem_zeroSupport_of_mem_wide_at_positive_height chi hprim hH hT hrho
    by_cases hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hcoord : rho.im ∈ exerciseLocalImagCoordinates chi H :=
        mem_exerciseLocalImagCoordinates_of_mem_global_top chi hfull hrange
      exact (hclear rho.im hcoord).trans (by
        simpa using Complex.abs_im_le_norm
          (((r : ℂ) + Complex.I * T) - rho))
    · have hfar : 1 ≤ |T - rho.im| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hT.1])]
          linarith [hT.1]
        · rw [abs_of_nonpos (by linarith [hT.2])]
          linarith [hT.2]
      exact hd1.trans (hfar.trans (by
        simpa using Complex.abs_im_le_norm
          (((r : ℂ) + Complex.I * T) - rho)))

/-- Reflection turns every inverse-character wide zero needed on the negative
horizontal half into a direct zero coordinate already avoided by the same
per-character good height. -/
theorem inverseWideClearance_of_goodHeight
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H T : ℝ} (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    (hclear : ∀ a ∈ exerciseLocalImagCoordinates chi H,
      exerciseHorizontalClearance chi H ≤ |T - a|) :
    ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0,
      ∀ rho ∈ wideZeroSupport chi⁻¹ (-T),
        exerciseHorizontalClearance chi H ≤
          ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
  intro r _hr rho hrho
  have hreflect : 1 - rho ∈ zeroSupport chi 0 (H + 4) :=
    one_sub_mem_zeroSupport_of_mem_inverse_wide
      chi hprim hchi hH hT hrho
  by_cases hrange : (1 - rho).im ∈ Set.Icc (H - 1) (H + 2)
  · have hcoord : (1 - rho).im ∈ exerciseLocalImagCoordinates chi H :=
      mem_exerciseLocalImagCoordinates_of_mem_global_top chi hreflect hrange
    have hordinate := hclear (1 - rho).im hcoord
    have him := Complex.abs_im_le_norm
      ((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)
    have hraw : |-T - rho.im| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
      simpa using him
    have himEq : (1 - rho).im = -rho.im := by simp
    rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
    rw [himEq] at hordinate
    exact hordinate.trans (by simpa [sub_eq_add_neg] using hraw)
  · have hfar : 1 ≤ |T - (1 - rho).im| := by
      rw [Set.mem_Icc, not_and_or] at hrange
      rcases hrange with hlo | hhi
      · rw [abs_of_nonneg (by linarith [hT.1])]
        linarith [hT.1]
      · rw [abs_of_nonpos (by linarith [hT.2])]
        linarith [hT.2]
    have him := Complex.abs_im_le_norm
      ((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)
    have hraw : |-T - rho.im| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
      simpa using him
    have himEq : (1 - rho).im = -rho.im := by simp
    rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
    rw [himEq] at hfar
    exact (clearance_le_one chi H).trans
      (hfar.trans (by simpa [sub_eq_add_neg] using hraw))

/-- Positive-height companion of the reflected inverse-wide support lemma. -/
theorem one_sub_mem_zeroSupport_of_mem_inverse_wide_positive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H T : ℝ} (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    {rho : ℂ} (hrho : rho ∈ wideZeroSupport chi⁻¹ T) :
    1 - rho ∈ zeroSupport chi 0 (H + 4) := by
  have hInvPrim : chi⁻¹.IsPrimitive := MAPFunctionalZeroTransport.isPrimitive_inv hprim
  have hInvNe : chi⁻¹ ≠ 1 := MAPFunctionalZeroTransport.inverse_ne_one hchi
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport chi⁻¹ hrho
  have hzeroInv : regularizedLFunction chi⁻¹ rho = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport
      chi⁻¹ (-1) (|T| + 3) hbase
  have hball := mem_ball_of_mem_wideZeroSupport chi⁻¹ hrho
  have hnorm : ‖rho - wideCenter T‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have himDiff : |rho.im - T| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (rho - wideCenter T)).trans_lt hnorm
  have himPos : 0 < rho.im := by
    have hlower : -3 < rho.im - T := neg_lt_of_abs_lt himDiff
    linarith [hH, hT.1]
  have hzero : regularizedLFunction chi (1 - rho) = 0 :=
    KoukFullCriticalZeroTransport.regularizedLFunction_one_sub_eq_zero_of_nonreal
      hprim hchi himPos.ne' hzeroInv
  have hre0 : 0 ≤ rho.re :=
    re_nonneg_of_mem_wideZeroSupport_of_primitive_of_im_ne_zero
      chi⁻¹ hInvPrim himPos.ne' hrho
  have hbaseRect : rho ∈ zeroRectangle (-1) (|T| + 3) :=
    (zeroDivisor chi⁻¹ (-1) (|T| + 3)).supportWithinDomain
      ((zeroSupport_mem_iff chi⁻¹ (-1) (|T| + 3) rho).mp hbase)
  have hre1 : rho.re ≤ 1 := hbaseRect.1.2
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have himabs : |rho.im| ≤ |T| + 3 := abs_le.mpr hbaseRect.2
  have himheight : |rho.im| ≤ H + 4 := by
    rw [abs_of_pos hTpos] at himabs
    linarith [hT.2]
  have hreflectRect : 1 - rho ∈ zeroRectangle 0 (H + 4) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    constructor
    · simp only [Complex.sub_re, Complex.one_re]
      exact ⟨by linarith, by linarith⟩
    · have habs : |(1 - rho).im| = |rho.im| := by simp
      exact abs_le.mp (by simpa [habs] using himheight)
  exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    chi 0 (H + 4) hreflectRect).2 hzero

/-- Reflected inverse-wide clearance needed on the bottom horizontal side. -/
theorem inverseWidePositiveClearance_of_goodHeight
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H T : ℝ} (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    (hclear : ∀ a ∈ exerciseLocalImagCoordinates chi H,
      exerciseHorizontalClearance chi H ≤ |T - a|) :
    ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0,
      ∀ rho ∈ wideZeroSupport chi⁻¹ T,
        exerciseHorizontalClearance chi H ≤
          ‖((((1 - r : ℝ) : ℂ) + Complex.I * T) - rho)‖ := by
  intro r _hr rho hrho
  have hreflect : 1 - rho ∈ zeroSupport chi 0 (H + 4) :=
    one_sub_mem_zeroSupport_of_mem_inverse_wide_positive
      chi hprim hchi hH hT hrho
  by_cases hrange : -(1 - rho).im ∈ Set.Icc (H - 1) (H + 2)
  · have hcoord : -(1 - rho).im ∈ exerciseLocalImagCoordinates chi H :=
      mem_exerciseLocalImagCoordinates_of_mem_global_bottom chi hreflect hrange
    have hordinate := hclear (-(1 - rho).im) hcoord
    have him := Complex.abs_im_le_norm
      ((((1 - r : ℝ) : ℂ) + Complex.I * T) - rho)
    have hraw : |T - rho.im| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * T) - rho)‖ := by
      simpa using him
    have himEq : -(1 - rho).im = rho.im := by simp
    rw [himEq] at hordinate
    exact hordinate.trans hraw
  · have hfar : 1 ≤ |T - (-(1 - rho).im)| := by
      rw [Set.mem_Icc, not_and_or] at hrange
      rcases hrange with hlo | hhi
      · rw [abs_of_nonneg (by linarith [hT.1])]
        linarith [hT.1]
      · rw [abs_of_nonpos (by linarith [hT.2])]
        linarith [hT.2]
    have him := Complex.abs_im_le_norm
      ((((1 - r : ℝ) : ℂ) + Complex.I * T) - rho)
    have hraw : |T - rho.im| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * T) - rho)‖ := by
      simpa using him
    have himEq : -(1 - rho).im = rho.im := by simp
    rw [himEq] at hfar
    exact (clearance_le_one chi H).trans (hfar.trans hraw)

end

end KoukTheorem113PerCharacterGoodHeight

#print axioms KoukTheorem113PerCharacterGoodHeight.exists_goodHeight_with_localCoordinateClearance
#print axioms KoukTheorem113PerCharacterGoodHeight.directWideClearance_of_goodHeight
#print axioms KoukTheorem113PerCharacterGoodHeight.inverseWideClearance_of_goodHeight
