import RamachandraLongContourContinuity

/-!
# Extracting the literal long-contour family moment from the product `L²` bound

This file contains no source-scale absorption.  It turns the certified
infinite-shell Minkowski estimate into the exact primitive-family second
moment and accounts for the normalized `1/(2π)` contour factor.
-/

namespace RamachandraLongContourMomentExtraction

open scoped BigOperators Interval ENNReal
open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraLongFamilyLpAssembly
open RamachandraLongContourContinuity
open RamachandraLongDyadicCutoff
open RamachandraLongDyadicScalarSummability

noncomputable section

set_option maxHeartbeats 1200000

local instance characterMeasurableSpace (n : ℕ) :
    MeasurableSpace (DirichletCharacter ℂ n) := ⊤

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The exact scale-sharp real majorant for the raw long-contour `L²`
seminorm. -/
def longSourceCutoffMajorant
    (d : ℕ) (X T sigma : ℝ) : ℝ :=
  ((∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
      (-(sigma + 1 / 4)) v) *
    Real.sqrt
      (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
        (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
        (1 + T) ^ 3)) *
  (Real.sqrt (8 + 8 * Real.pi) *
    ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
    (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X *
    longDyadicTailMass)

theorem longSourceCutoffMajorant_nonneg
    (d : ℕ) (X T sigma : ℝ) :
    0 ≤ longSourceCutoffMajorant d X T sigma := by
  unfold longSourceCutoffMajorant
  exact mul_nonneg
    (mul_nonneg
      (integral_nonneg (fun v =>
        RamachandraGammaWeightIntegrability.gammaPolynomialWeight_nonneg _ _))
      (Real.sqrt_nonneg _))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
        (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _))
      longDyadicTailMass_nonneg)

theorem integrable_norm_sq_primitiveLongRawField
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    Integrable (fun p => ‖primitiveLongRawField d X sigma p‖ ^ 2)
      (primitiveLongFamilyMeasure d T) := by
  have hsm := stronglyMeasurable_primitiveLongRawField d
    (show 1 ≤ X by linarith) hcLo hcHi
  have hbound := eLpNorm_primitiveLongRawField_le_sourceCutoffMajorant d
    hscale hX hT hcLo hcHi
  have hmem : MemLp (primitiveLongRawField d X sigma) 2
      (primitiveLongFamilyMeasure d T) := by
    refine ⟨hsm.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (by simpa [longSourceCutoffMajorant] using hbound)
      ENNReal.ofReal_lt_top
  exact (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).1 hmem

/-- Exact `L²` seminorm formula for the raw family field. -/
theorem eLpNorm_primitiveLongRawField_eq_ofReal_sqrt_integral
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    eLpNorm (primitiveLongRawField d X sigma) 2
        (primitiveLongFamilyMeasure d T) =
      ENNReal.ofReal (Real.sqrt
        (∫ p, ‖primitiveLongRawField d X sigma p‖ ^ 2
          ∂primitiveLongFamilyMeasure d T)) := by
  have hsm := stronglyMeasurable_primitiveLongRawField d
    (show 1 ≤ X by linarith) hcLo hcHi
  have hint := integrable_norm_sq_primitiveLongRawField d
    hscale hX hT hcLo hcHi
  have hmem : MemLp (primitiveLongRawField d X sigma) 2
      (primitiveLongFamilyMeasure d T) :=
    (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).2 hint
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [← Real.sqrt_eq_rpow]

/-- The raw product-space second moment is bounded by the square of the exact
source cutoff majorant. -/
theorem integral_norm_sq_primitiveLongRawField_le
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    (∫ p, ‖primitiveLongRawField d X sigma p‖ ^ 2
        ∂primitiveLongFamilyMeasure d T) ≤
      longSourceCutoffMajorant d X T sigma ^ 2 := by
  let I : ℝ := ∫ p, ‖primitiveLongRawField d X sigma p‖ ^ 2
    ∂primitiveLongFamilyMeasure d T
  let R : ℝ := longSourceCutoffMajorant d X T sigma
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hR : 0 ≤ R := by exact longSourceCutoffMajorant_nonneg d X T sigma
  have hnorm := eLpNorm_primitiveLongRawField_le_sourceCutoffMajorant d
    hscale hX hT hcLo hcHi
  have heq := eLpNorm_primitiveLongRawField_eq_ofReal_sqrt_integral d
    hscale hX hT hcLo hcHi
  have hsqrt : Real.sqrt I ≤ R := by
    apply (ENNReal.ofReal_le_ofReal_iff hR).1
    rw [← heq]
    simpa only [I, R, longSourceCutoffMajorant] using hnorm
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg I) hsqrt 2
  rw [Real.sq_sqrt hI] at hsq
  simpa only [I, R] using hsq

/-- Product-space integral expanded in the source's character-first order. -/
theorem integral_norm_sq_primitiveLongRawField_eq
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    (∫ p, ‖primitiveLongRawField d X sigma p‖ ^ 2
        ∂primitiveLongFamilyMeasure d T) =
      ∑ psi : DirichletCharacter ℂ d,
        if psi.IsPrimitive then
          ∫ t in (-T)..T,
            ‖∫ v : ℝ, ramachandraShiftedContourIntegrand psi X sigma
              (-(sigma + 1 / 4)) t v true‖ ^ 2
        else 0 := by
  classical
  have hint := integrable_norm_sq_primitiveLongRawField d
    hscale hX hT hcLo hcHi
  unfold primitiveLongFamilyMeasure at hint ⊢
  rw [MeasureTheory.integral_prod _ hint, MeasureTheory.integral_count]
  unfold primitiveLongRawField
  apply Finset.sum_congr rfl
  intro psi hpsi
  by_cases hp : psi.IsPrimitive
  · simp only [hp, if_true]
    rw [Set.uIoc_of_le (by linarith)]
    rw [intervalIntegral.integral_of_le (by linarith)]
  · simp [hp]

/-- The normalized source long-contour moment is no larger than the raw
product-space moment. -/
theorem primitiveFamilyLongContourSecondMoment_le_rawIntegral
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 1 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    primitiveFamilyLongContourSecondMoment d T sigma ≤
      ∫ p, ‖primitiveLongRawField d X sigma p‖ ^ 2
        ∂primitiveLongFamilyMeasure d T := by
  classical
  rw [integral_norm_sq_primitiveLongRawField_eq d hscale hX
    (by linarith) hcLo hcHi]
  unfold primitiveFamilyLongContourSecondMoment
  apply Finset.sum_le_sum
  intro psi hpsi
  by_cases hp : psi.IsPrimitive
  · simp only [hp, if_true]
    have hrawCont := continuous_integral_longContourIntegrand_character psi
      (show 1 ≤ X by linarith) hcLo hcHi
    have hsourceCont := continuous_primitiveShiftedLongContour_sq psi
      hT hcLo hcHi
    apply intervalIntegral.integral_mono (by linarith)
      (hsourceCont.intervalIntegrable (-T) T)
      ((hrawCont.norm.pow 2).intervalIntegrable (-T) T)
    intro t
    unfold primitiveShiftedLongContour ramachandraShiftedContourPiece
    dsimp only
    rw [show primitiveShiftedScale d T = X by
      unfold primitiveShiftedScale
      exact hscale.symm]
    rw [norm_mul]
    have hc : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      exact div_le_one (by positivity) |>.2 hpi
    have hz : 0 ≤ ‖∫ v : ℝ, ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v true‖ := norm_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hc hz
    simpa using pow_le_pow_left₀
      (mul_nonneg (norm_nonneg _) hz) hmul 2
  · simp [hp]

/-- Exact analytic long-contour moment bound before elementary source-scale
absorption. -/
theorem primitiveFamilyLongContourSecondMoment_le_cutoffMajorant_sq
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 1 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    primitiveFamilyLongContourSecondMoment d T sigma ≤
      longSourceCutoffMajorant d X T sigma ^ 2 :=
  (primitiveFamilyLongContourSecondMoment_le_rawIntegral d
    hscale hX hT hcLo hcHi).trans
      (integral_norm_sq_primitiveLongRawField_le d
        hscale hX (by linarith) hcLo hcHi)

end
end RamachandraLongContourMomentExtraction

#print axioms RamachandraLongContourMomentExtraction.primitiveFamilyLongContourSecondMoment_le_cutoffMajorant_sq
