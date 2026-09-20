import APSignedAlignedFamilyContourAperture
import KoukNegativeHalfPlaneNonvanishing

/-!
# Quantitative full-strip clearance at every family-good height

The common family height set was defined from imaginary zero coordinates.
Consequently its horizontal clearance is independent of the real coordinate;
it holds on the literal full strip `0 ≤ re s ≤ 1`, not only on the
positive paper edge exposed by the older consumer.  We record that exact
source-facing fact for the full-support Koukoulopoulos contour.
-/

namespace KoukFullStripGoodHeightAperture

open Set Complex DirichletZeros QuantitativeFiniteAperture
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPAPSignedAlignedFamilyContourAperture
open KoukNegativeHalfPlaneNonvanishing

noncomputable section

/-- Every height in the family-good set has uniform horizontal clearance from
the complete primitive-inducer divisor on the full critical strip. -/
theorem fullStripHorizontalClearance_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 0 < H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      (∀ r ∈ Set.Icc (0 : ℝ) 1,
        ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
          familyExerciseHorizontalClearance Q H ≤
            ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) 1,
        ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
          familyExerciseHorizontalClearance Q H ≤
            ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hdPos : 0 < familyExerciseHorizontalClearance Q H := by
    unfold familyExerciseHorizontalClearance
    positivity
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
  · intro r _hr rho hrho
    by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hrhoFamily : -rho.im ∈
          familyExerciseLocalImagCoordinates Q H := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact mem_exerciseLocalImagCoordinates_of_mem_global_bottom
          chi.primitiveCharacter hrho hrange
      have hcoord := familyExerciseHorizontalClearance_le_abs_sub
        Q H hTG hrhoFamily
      have hdist : familyExerciseHorizontalClearance Q H ≤
          |(-T) - rho.im| := by
        calc
          familyExerciseHorizontalClearance Q H ≤ |T - (-rho.im)| := hcoord
          _ = |(-T) - rho.im| := by
            rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]
      exact hdist.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
    · have hfar : 1 ≤ |T - (-rho.im)| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hTIoo.1])]
          linarith [hTIoo.1]
        · rw [abs_of_nonpos (by linarith [hTIoo.2])]
          linarith [hTIoo.2]
      have hdist : familyExerciseHorizontalClearance Q H ≤
          |(-T) - rho.im| :=
        hdLeOne.trans (hfar.trans_eq (by
          rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]))
      exact hdist.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
  · intro r _hr rho hrho
    by_cases hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hrhoFamily : rho.im ∈
          familyExerciseLocalImagCoordinates Q H := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact mem_exerciseLocalImagCoordinates_of_mem_global_top
          chi.primitiveCharacter hrho hrange
      have hcoord := familyExerciseHorizontalClearance_le_abs_sub
        Q H hTG hrhoFamily
      exact hcoord.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + (T : ℂ) * Complex.I) - rho))
    · have hfar : 1 ≤ |T - rho.im| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hTIoo.1])]
          linarith [hTIoo.1]
        · rw [abs_of_nonpos (by linarith [hTIoo.2])]
          linarith [hTIoo.2]
      exact hdLeOne.trans (hfar.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + (T : ℂ) * Complex.I) - rho)))

/-- Quantitative clearance implies literal nonvanishing on the full strip. -/
theorem fullStripHorizontalNonzero_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 0 < H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      (∀ r ∈ Set.Icc (0 : ℝ) 1,
        regularizedLFunction chi.primitiveCharacter
          ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) 1,
        regularizedLFunction chi.primitiveCharacter
          ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hclear := fullStripHorizontalClearance_of_mem_familyExerciseGoodHeights
    Q hH hTG q hq chi
  have hdPos : 0 < familyExerciseHorizontalClearance Q H := by
    unfold familyExerciseHorizontalClearance
    positivity
  constructor
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · simpa [z] using hr
      · constructor
        · have : -(H + 4) ≤ -T := by linarith [hTIoo.2]
          simpa [z] using this
        · have : -T ≤ H + 4 := by linarith [hH, hTIoo.1]
          simpa [z] using this
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hd := hclear.1 r hr z hzS
    simp [z] at hd
    linarith
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · simpa [z] using hr
      · constructor
        · have : -(H + 4) ≤ T := by linarith [hH, hTIoo.1]
          simpa [z] using this
        · have : T ≤ H + 4 := hTIoo.2.le.trans (by linarith)
          simpa [z] using this
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hd := hclear.2 r hr z hzS
    simp [z] at hd
    linarith

/-- The same quantitative good height is legal on every canonical far-left
Kouk rectangle. -/
theorem negativeRectangleHorizontalNonzero_of_mem_familyExerciseGoodHeights
    (Q : ℕ) {H T : ℝ} (hH : 0 < H)
    (hTG : T ∈ familyExerciseGoodHeights Q H) :
    ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q) (M : ℕ) (c : ℝ),
      1 ≤ c →
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      (∀ r ∈ Set.Icc (negativeHalfIntegerEdge M) c,
        regularizedLFunction chi.primitiveCharacter
          ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
      (∀ r ∈ Set.Icc (negativeHalfIntegerEdge M) c,
        regularizedLFunction chi.primitiveCharacter
          ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) := by
  intro q hq chi M c hc
  letI : NeZero q :=
    ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hfull := fullStripHorizontalNonzero_of_mem_familyExerciseGoodHeights
    Q hH hTG q hq chi
  exact negativeHalfInteger_horizontal_nonzero_of_fullStrip
    chi.primitiveCharacter chi.primitiveCharacter_isPrimitive M
    (hH.trans hTIoo.1) hc hfull.1 hfull.2

end
end KoukFullStripGoodHeightAperture

#print axioms KoukFullStripGoodHeightAperture.fullStripHorizontalClearance_of_mem_familyExerciseGoodHeights
#print axioms KoukFullStripGoodHeightAperture.negativeRectangleHorizontalNonzero_of_mem_familyExerciseGoodHeights
