import KoukFullCriticalZeroTransport
import KoukNegativeHorizontalLogDerivativeBound
import KoukFullStripGoodHeightAperture
import WideDiskLocalMass

/-!
# Reflected inverse-family clearance at a common good height

The negative half of the Koukoulopoulos horizontal contour is estimated after
functional-equation reflection.  Its local Blaschke field belongs to the
inverse primitive character at height `-T`.  Every such nonreal zero reflects
to an ordinary zero of the original primitive character at height `T`; the
family-good-height construction therefore supplies the same literal ordinate
clearance.  This module records that bridge without changing the common-height
quantifiers.
-/

namespace KoukInverseWideZeroClearance

open Set Complex DirichletZeros
open WideDiskBlaschkeAssembly WideDiskLocalMass
open WideDiskLFunctionGrowth
open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPAPSignedAlignedFamilyContourAperture
open KoukFullCriticalZeroTransport MAPFunctionalZeroTransport

noncomputable section

/-- A nonreal wide-disk zero of a primitive character cannot lie to the
left of the critical strip.  Unlike the older local-mass API, this statement
also covers the conductor-one principal character. -/
theorem re_nonneg_of_mem_wideZeroSupport_of_primitive_of_im_ne_zero
    {q : ℕ} [NeZero q] (psi : DirichletCharacter ℂ q)
    (hprim : psi.IsPrimitive) {t : ℝ} {rho : ℂ}
    (him : rho.im ≠ 0) (hrho : rho ∈ wideZeroSupport psi t) :
    0 ≤ rho.re := by
  by_contra hnot
  have hreNeg : rho.re < 0 := lt_of_not_ge hnot
  have hball := mem_ball_of_mem_wideZeroSupport psi hrho
  have hnorm : ‖rho - wideCenter t‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have hreDiff : |rho.re - 2| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_re_le_norm (rho - wideCenter t)).trans_lt hnorm
  have hreLo : -1 < rho.re := by
    have := neg_lt_of_abs_lt hreDiff
    linarith
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    psi (-1) (|t| + 3)
      (mem_baseZeroSupport_of_mem_wideZeroSupport psi hrho)
  have hgamma :=
    KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
      psi him
  exact
    (KoukNegativeHalfPlaneNonvanishing.regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
      psi hprim hreNeg hgamma) hzero

/-- A nonreal primitive wide-disk zero at `-T` belongs to the complete
critical-strip divisor at the selected family height. -/
theorem mem_zeroSupport_of_mem_wide_at_negative_height
    {q : ℕ} [NeZero q] (psi : DirichletCharacter ℂ q)
    (hprim : psi.IsPrimitive) {H T : ℝ} (hH : 4 ≤ H)
    (hT : T ∈ Set.Ioo H (H + 1)) {rho : ℂ}
    (hrho : rho ∈ wideZeroSupport psi (-T)) :
    rho ∈ zeroSupport psi 0 (H + 4) := by
  have hball := mem_ball_of_mem_wideZeroSupport psi hrho
  have hnorm : ‖rho - wideCenter (-T)‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have himDiff : |rho.im + T| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (rho - wideCenter (-T))).trans_lt hnorm
  have himNeg : rho.im < 0 := by
    have hupper : rho.im + T < 3 := lt_of_abs_lt himDiff
    linarith [hT.1]
  have him : rho.im ≠ 0 := ne_of_lt himNeg
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport psi hrho
  have hbaseRect : rho ∈ zeroRectangle (-1) (|-T| + 3) :=
    (zeroDivisor psi (-1) (|-T| + 3)).supportWithinDomain
      ((zeroSupport_mem_iff psi (-1) (|-T| + 3) rho).mp hbase)
  have hre0 : 0 ≤ rho.re :=
    re_nonneg_of_mem_wideZeroSupport_of_primitive_of_im_ne_zero
      psi hprim him hrho
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have himabs : |rho.im| ≤ |-T| + 3 := abs_le.mpr hbaseRect.2
  have himheight : |rho.im| ≤ H + 4 := by
    rw [abs_neg, abs_of_pos hTpos] at himabs
    linarith [hT.2]
  have hrect : rho ∈ zeroRectangle 0 (H + 4) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hre0, hbaseRect.1.2⟩, abs_le.mp himheight⟩
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    psi (-1) (|-T| + 3) hbase
  exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    psi 0 (H + 4) hrect).2 hzero

/-- Positive-height companion of
`mem_zeroSupport_of_mem_wide_at_negative_height`. -/
theorem mem_zeroSupport_of_mem_wide_at_positive_height
    {q : ℕ} [NeZero q] (psi : DirichletCharacter ℂ q)
    (hprim : psi.IsPrimitive) {H T : ℝ} (hH : 4 ≤ H)
    (hT : T ∈ Set.Ioo H (H + 1)) {rho : ℂ}
    (hrho : rho ∈ wideZeroSupport psi T) :
    rho ∈ zeroSupport psi 0 (H + 4) := by
  have hball := mem_ball_of_mem_wideZeroSupport psi hrho
  have hnorm : ‖rho - wideCenter T‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have himDiff : |rho.im - T| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (rho - wideCenter T)).trans_lt hnorm
  have himPos : 0 < rho.im := by
    have hlower : -3 < rho.im - T := neg_lt_of_abs_lt himDiff
    linarith [hT.1]
  have him : rho.im ≠ 0 := ne_of_gt himPos
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport psi hrho
  have hbaseRect : rho ∈ zeroRectangle (-1) (|T| + 3) :=
    (zeroDivisor psi (-1) (|T| + 3)).supportWithinDomain
      ((zeroSupport_mem_iff psi (-1) (|T| + 3) rho).mp hbase)
  have hre0 : 0 ≤ rho.re :=
    re_nonneg_of_mem_wideZeroSupport_of_primitive_of_im_ne_zero
      psi hprim him hrho
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have himabs : |rho.im| ≤ |T| + 3 := abs_le.mpr hbaseRect.2
  have himheight : |rho.im| ≤ H + 4 := by
    rw [abs_of_pos hTpos] at himabs
    linarith [hT.2]
  have hrect : rho ∈ zeroRectangle 0 (H + 4) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hre0, hbaseRect.1.2⟩, abs_le.mp himheight⟩
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    psi (-1) (|T| + 3) hbase
  exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    psi 0 (H + 4) hrect).2 hzero

/-- A zero in the inverse-character wide disk at `-T` reflects into the full
`[0,1]` divisor of the original primitive character at height `H+4`.
The harmless hypothesis `4 ≤ H` ensures that the radius-three wide disk is
strictly nonreal, so the value-level functional equation applies. -/
theorem one_sub_mem_zeroSupport_of_mem_inverse_wide
    {q : ℕ} [NeZero q] (psi : DirichletCharacter ℂ q)
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    {H T : ℝ} (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    {rho : ℂ} (hrho : rho ∈ wideZeroSupport psi⁻¹ (-T)) :
    1 - rho ∈ zeroSupport psi 0 (H + 4) := by
  have hInvPrim : psi⁻¹.IsPrimitive := isPrimitive_inv hprim
  have hInvNe : psi⁻¹ ≠ 1 := inverse_ne_one hpsi
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport psi⁻¹ hrho
  have hzeroInv : regularizedLFunction psi⁻¹ rho = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport
      psi⁻¹ (-1) (|-T| + 3) hbase
  have hball := mem_ball_of_mem_wideZeroSupport psi⁻¹ hrho
  have hnorm : ‖rho - wideCenter (-T)‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have himDiff : |rho.im + T| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (rho - wideCenter (-T))).trans_lt hnorm
  have himNeg : rho.im < 0 := by
    have hupper : rho.im + T < 3 := lt_of_abs_lt himDiff
    linarith [hT.1]
  have him : rho.im ≠ 0 := ne_of_lt himNeg
  have hzero : regularizedLFunction psi (1 - rho) = 0 :=
    regularizedLFunction_one_sub_eq_zero_of_nonreal
      hprim hpsi him hzeroInv
  have hre0 : 0 ≤ rho.re :=
    re_nonneg_of_mem_wideZeroSupport psi⁻¹ hInvPrim hInvNe hrho
  have hbaseRect : rho ∈ zeroRectangle (-1) (|-T| + 3) :=
    (zeroDivisor psi⁻¹ (-1) (|-T| + 3)).supportWithinDomain
      ((zeroSupport_mem_iff psi⁻¹ (-1) (|-T| + 3) rho).mp hbase)
  have hre1 : rho.re ≤ 1 := hbaseRect.1.2
  have hTpos : 0 < T := lt_of_lt_of_le (by linarith : 0 < H) hT.1.le
  have himabs : |rho.im| ≤ |-T| + 3 := abs_le.mpr hbaseRect.2
  have himheight : |rho.im| ≤ H + 4 := by
    rw [abs_neg, abs_of_pos hTpos] at himabs
    linarith [hT.2]
  have hreflectRect : 1 - rho ∈ zeroRectangle 0 (H + 4) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    constructor
    · simp only [Complex.sub_re, Complex.one_re]
      exact ⟨by linarith, by linarith⟩
    · have habs : |(1 - rho).im| = |rho.im| := by simp
      exact abs_le.mp (by simpa [habs] using himheight)
  exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    psi 0 (H + 4) hreflectRect).2 hzero

/-- The selected family-good height clears the inverse-character wide disk
needed after reflection on the entire negative half-strip.  This is an
ordinate argument, so no loss depends on the real coordinate `r`. -/
theorem inverseWideZeroClearance_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 4 ≤ H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      chi.primitiveCharacter ≠ 1 →
      ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0,
        ∀ rho ∈ wideZeroSupport chi.primitiveCharacter⁻¹ (-T),
          familyExerciseHorizontalClearance Q H ≤
            ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  intro hpsi r _hr rho hrho
  let psi := chi.primitiveCharacter
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hreflect : 1 - rho ∈ zeroSupport psi 0 (H + 4) :=
    one_sub_mem_zeroSupport_of_mem_inverse_wide
      psi chi.primitiveCharacter_isPrimitive hpsi hH hTIoo hrho
  have hTpos : 0 < T := by linarith [hH, hTIoo.1]
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport psi⁻¹ hrho
  have hbaseRect : rho ∈ zeroRectangle (-1) (|-T| + 3) :=
    (zeroDivisor psi⁻¹ (-1) (|-T| + 3)).supportWithinDomain
      ((zeroSupport_mem_iff psi⁻¹ (-1) (|-T| + 3) rho).mp hbase)
  have himabs : |rho.im| ≤ |-T| + 3 := abs_le.mpr hbaseRect.2
  have himrange : (1 - rho).im ∈ Set.Icc (H - 1) (H + 2) ∨
      (1 - rho).im ∉ Set.Icc (H - 1) (H + 2) :=
    em _
  rcases himrange with hrange | hrange
  · have hcoordLocal : (1 - rho).im ∈
        exerciseLocalImagCoordinates psi H :=
      mem_exerciseLocalImagCoordinates_of_mem_global_top
        psi hreflect hrange
    have hcoordFamily : (1 - rho).im ∈
        familyExerciseLocalImagCoordinates Q H := by
      apply mem_familyImagCoordinates Q H q hq chi
      exact hcoordLocal
    have hclear := familyExerciseHorizontalClearance_le_abs_sub
      Q H hTG hcoordFamily
    have himEq : (1 - rho).im = -rho.im := by simp
    have hnormIm : |T - (1 - rho).im| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
      have himNorm := Complex.abs_im_le_norm
        ((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
        simpa using himNorm
      rw [show -T - rho.im = -(T + rho.im) by ring, abs_neg] at hraw
      simpa [himEq] using hraw
    exact hclear.trans hnormIm
  · have hdLeOne : familyExerciseHorizontalClearance Q H ≤ 1 := by
      have hcard : (0 : ℝ) ≤
          ((familyExerciseLocalImagCoordinates Q H).card : ℝ) := by
        positivity
      have hden : (4 : ℝ) ≤ 4 *
          (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1) := by
        nlinarith
      unfold familyExerciseHorizontalClearance
      have hfrac :
          1 / (4 * (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1))
            ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hden
      exact hfrac.trans (by norm_num)
    have hfar : 1 ≤ |T - (1 - rho).im| := by
      rw [Set.mem_Icc, not_and_or] at hrange
      rcases hrange with hlo | hhi
      · rw [abs_of_nonneg (by linarith [hTIoo.1])]
        linarith [hTIoo.1]
      · rw [abs_of_nonpos (by linarith [hTIoo.2])]
        linarith [hTIoo.2]
    have himEq : (1 - rho).im = -rho.im := by simp
    have hnormIm : |T - (1 - rho).im| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
      have himNorm := Complex.abs_im_le_norm
        ((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
        simpa using himNorm
      rw [show -T - rho.im = -(T + rho.im) by ring, abs_neg] at hraw
      simpa [himEq] using hraw
    exact hdLeOne.trans (hfar.trans hnormIm)

/-- Direct top/bottom wide-disk clearance for every primitive inducer in the
ambient AP family.  The real coordinate is unrestricted because the selected
height construction is an ordinate aperture. -/
theorem directWideZeroClearance_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 4 ≤ H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      ( ∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi.primitiveCharacter (-T),
          familyExerciseHorizontalClearance Q H ≤
            ‖(((r : ℂ) + Complex.I * (-T)) - rho)‖ ) ∧
      ( ∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi.primitiveCharacter T,
          familyExerciseHorizontalClearance Q H ≤
            ‖(((r : ℂ) + Complex.I * T) - rho)‖ ) := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hdLeOne : familyExerciseHorizontalClearance Q H ≤ 1 := by
    have hcard : (0 : ℝ) ≤
        ((familyExerciseLocalImagCoordinates Q H).card : ℝ) := by
      positivity
    have hden : (4 : ℝ) ≤ 4 *
        (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1) := by
      nlinarith
    unfold familyExerciseHorizontalClearance
    have hfrac :
        1 / (4 * (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1))
          ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hden
    exact hfrac.trans (by norm_num)
  constructor
  · intro r rho hrho
    have hfull : rho ∈ zeroSupport psi 0 (H + 4) :=
      mem_zeroSupport_of_mem_wide_at_negative_height
        psi chi.primitiveCharacter_isPrimitive hH hTIoo hrho
    by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hcoordLocal : -rho.im ∈ exerciseLocalImagCoordinates psi H :=
        mem_exerciseLocalImagCoordinates_of_mem_global_bottom
          psi hfull hrange
      have hcoordFamily : -rho.im ∈
          familyExerciseLocalImagCoordinates Q H := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact hcoordLocal
      have hclear := familyExerciseHorizontalClearance_le_abs_sub
        Q H hTG hcoordFamily
      have himNorm := Complex.abs_im_le_norm
        (((r : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖(((r : ℂ) + Complex.I * (-T)) - rho)‖ := by
        simpa using himNorm
      rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
      exact hclear.trans hraw
    · have hfar : 1 ≤ |T - (-rho.im)| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hTIoo.1])]
          linarith [hTIoo.1]
        · rw [abs_of_nonpos (by linarith [hTIoo.2])]
          linarith [hTIoo.2]
      have himNorm := Complex.abs_im_le_norm
        (((r : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖(((r : ℂ) + Complex.I * (-T)) - rho)‖ := by
        simpa using himNorm
      rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
      exact hdLeOne.trans (hfar.trans hraw)
  · intro r rho hrho
    have hfull : rho ∈ zeroSupport psi 0 (H + 4) :=
      mem_zeroSupport_of_mem_wide_at_positive_height
        psi chi.primitiveCharacter_isPrimitive hH hTIoo hrho
    by_cases hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hcoordLocal : rho.im ∈ exerciseLocalImagCoordinates psi H :=
        mem_exerciseLocalImagCoordinates_of_mem_global_top
          psi hfull hrange
      have hcoordFamily : rho.im ∈
          familyExerciseLocalImagCoordinates Q H := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact hcoordLocal
      have hclear := familyExerciseHorizontalClearance_le_abs_sub
        Q H hTG hcoordFamily
      exact hclear.trans (by
        simpa using Complex.abs_im_le_norm
          (((r : ℂ) + Complex.I * T) - rho))
    · have hfar : 1 ≤ |T - rho.im| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hTIoo.1])]
          linarith [hTIoo.1]
        · rw [abs_of_nonpos (by linarith [hTIoo.2])]
          linarith [hTIoo.2]
      exact hdLeOne.trans (hfar.trans (by
        simpa using Complex.abs_im_le_norm
          (((r : ℂ) + Complex.I * T) - rho)))

/-- Principal primitive-inducer version.  Here inversion fixes the character,
so the bottom family ordinate set itself supplies the clearance. -/
theorem principalInverseWideZeroClearance_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 4 ≤ H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      chi.primitiveCharacter = 1 →
      ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0,
        ∀ rho ∈ wideZeroSupport chi.primitiveCharacter⁻¹ (-T),
          familyExerciseHorizontalClearance Q H ≤
            ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  intro hpsi r _hr rho hrho
  let psi := chi.primitiveCharacter
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hrhoPsi : rho ∈ wideZeroSupport psi (-T) := by
    simpa [psi, hpsi] using hrho
  have hfull : rho ∈ zeroSupport psi 0 (H + 4) :=
    mem_zeroSupport_of_mem_wide_at_negative_height
      psi chi.primitiveCharacter_isPrimitive hH hTIoo hrhoPsi
  by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
  · have hcoordLocal : -rho.im ∈ exerciseLocalImagCoordinates psi H :=
      mem_exerciseLocalImagCoordinates_of_mem_global_bottom
        psi hfull hrange
    have hcoordFamily : -rho.im ∈
        familyExerciseLocalImagCoordinates Q H := by
      apply mem_familyImagCoordinates Q H q hq chi
      exact hcoordLocal
    have hclear := familyExerciseHorizontalClearance_le_abs_sub
      Q H hTG hcoordFamily
    have hnormIm : |T - (-rho.im)| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
      have himNorm := Complex.abs_im_le_norm
        ((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
        simpa using himNorm
      rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
      exact hraw
    exact hclear.trans hnormIm
  · have hTIoo' := familyExerciseGoodHeights_subset_Ioo Q H hTG
    have hdLeOne : familyExerciseHorizontalClearance Q H ≤ 1 := by
      have hcard : (0 : ℝ) ≤
          ((familyExerciseLocalImagCoordinates Q H).card : ℝ) := by
        positivity
      have hden : (4 : ℝ) ≤ 4 *
          (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1) := by
        nlinarith
      unfold familyExerciseHorizontalClearance
      have hfrac :
          1 / (4 * (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1))
            ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hden
      exact hfrac.trans (by norm_num)
    have hfar : 1 ≤ |T - (-rho.im)| := by
      rw [Set.mem_Icc, not_and_or] at hrange
      rcases hrange with hlo | hhi
      · rw [abs_of_nonneg (by linarith [hTIoo'.1])]
        linarith [hTIoo'.1]
      · rw [abs_of_nonpos (by linarith [hTIoo'.2])]
        linarith [hTIoo'.2]
    have hnormIm : |T - (-rho.im)| ≤
        ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
      have himNorm := Complex.abs_im_le_norm
        ((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)
      have hraw : |-T - rho.im| ≤
          ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
        simpa using himNorm
      rw [show -T - rho.im = -(T - (-rho.im)) by ring, abs_neg] at hraw
      exact hraw
    exact hdLeOne.trans (hfar.trans hnormIm)

/-- Uniform wrapper over the principal and nonprincipal primitive-inducer
cases.  This is the exact distance premise consumed by the negative
horizontal logarithmic-derivative bounds. -/
theorem allInverseWideZeroClearance_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 4 ≤ H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0,
        ∀ rho ∈ wideZeroSupport chi.primitiveCharacter⁻¹ (-T),
          familyExerciseHorizontalClearance Q H ≤
            ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-T)) - rho)‖ := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  by_cases hpsi : chi.primitiveCharacter = 1
  · exact principalInverseWideZeroClearance_of_mem_familyExerciseGoodHeights
      Q hH hTG q hq chi hpsi
  · exact inverseWideZeroClearance_of_mem_familyExerciseGoodHeights
      Q hH hTG q hq chi hpsi

end

end KoukInverseWideZeroClearance

#print axioms KoukInverseWideZeroClearance.one_sub_mem_zeroSupport_of_mem_inverse_wide
#print axioms KoukInverseWideZeroClearance.inverseWideZeroClearance_of_mem_familyExerciseGoodHeights
#print axioms KoukInverseWideZeroClearance.principalInverseWideZeroClearance_of_mem_familyExerciseGoodHeights
#print axioms KoukInverseWideZeroClearance.allInverseWideZeroClearance_of_mem_familyExerciseGoodHeights
