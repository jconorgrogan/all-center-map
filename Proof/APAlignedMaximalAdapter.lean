import APHalfIntegerAlignedTail
import APSelectedTruncatedZeroFieldEnergy28
import APFloorMaximalBridge
import OneSidedMaximalL2

/-!
# Maximal adapter for half-integer-aligned Perron endpoints

The aligned endpoint formula averages the sigma-truncated Perron field on
`[x-1/2,x+Y+1/2]`.  This file converts that real integral exactly into the
indicator-valued one-sided average at scale `Y+1` and shifted base `x-1/2`.
The conversion is deterministic and introduces no measurable continuum
supremum.
-/

namespace MAPAPAlignedMaximalAdapter

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation APMaximalExplicitFormulaBridge OneSidedMaximalL2
open MAPFixedScaleAPZeroRoute MAPAPHalfIntegerAlignedTail
open MAPAPSelectedTruncatedZeroFieldEnergy28

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Exact ENNReal conversion of the enlarged aligned zero average. -/
theorem ofReal_alignedZeroAverage_eq_rightAverage
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma X T x Y : ℝ}
    (hXtwo : 2 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    ENNReal.ofReal
        ((Y + 1)⁻¹ *
          ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
            ‖perronZeroField chi sigma T t‖) =
      rightAverage (truncatedZeroNormField chi sigma X T)
        (Y + 1) (x - 1 / 2) := by
  let f : ℝ → ℝ := fun t => ‖perronZeroField chi sigma T t‖
  have hY1 : 0 < Y + 1 := by linarith
  have hleft : 0 < x - 1 / 2 := by linarith [hx.1]
  have hcont : ContinuousOn f
      (Set.Icc (x - 1 / 2) ((x - 1 / 2) + (Y + 1))) := by
    have h := continuousOn_norm_perronZeroField chi sigma T
      (a := x - 1 / 2) (b := x + Y + 1 / 2) hleft (by linarith)
    simpa only [show x - 1 / 2 + (Y + 1) = x + Y + 1 / 2 by ring] using h
  have hintIcc : IntegrableOn f
      (Set.Icc (x - 1 / 2) ((x - 1 / 2) + (Y + 1))) :=
    hcont.integrableOn_Icc
  have hintIoc : IntegrableOn f
      (Set.Ioc (x - 1 / 2) ((x - 1 / 2) + (Y + 1))) :=
    hintIcc.mono_set Set.Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (Set.Ioc (x - 1 / 2) ((x - 1 / 2) + (Y + 1)))] f :=
    Filter.Eventually.of_forall (fun t => norm_nonneg _)
  have hint :
      ENNReal.ofReal
          (∫ t : ℝ in x - 1 / 2..(x - 1 / 2) + (Y + 1), f t) =
        ∫⁻ t : ℝ in Set.Ioc (x - 1 / 2)
            ((x - 1 / 2) + (Y + 1)), ENNReal.ofReal (f t) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact ofReal_integral_eq_lintegral_ofReal hintIoc hnonneg
  have hsupport : ∀ t ∈ Set.Ioc (x - 1 / 2)
      ((x - 1 / 2) + (Y + 1)),
      t ∈ Set.Icc (X / 4) (6 * X) := by
    intro t ht
    constructor
    · have hleftSupport : X / 4 ≤ x - 1 / 2 := by linarith [hx.1]
      exact hleftSupport.trans ht.1.le
    · have hrightSupport : (x - 1 / 2) + (Y + 1) ≤ 6 * X := by
        linarith [hx.2, hYX]
      exact ht.2.trans hrightSupport
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hY1.le),
    ENNReal.ofReal_inv_of_pos hY1]
  have hinterval :
      (∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2, f t) =
        ∫ t : ℝ in x - 1 / 2..(x - 1 / 2) + (Y + 1), f t := by
    congr 1 <;> ring
  rw [hinterval, hint, rightAverage_eq_interval]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp [truncatedZeroNormField, hsupport t ht, f]

/-- The enlarged aligned average lies in the legal shifted maximal family. -/
theorem ofReal_alignedZeroAverage_sq_le_rightMax
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma X T x Y H : ℝ}
    (hXtwo : 2 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hY : 1 ≤ Y) (hYX : Y ≤ X)
    (hHY : H ≤ Y) :
    ENNReal.ofReal
        ((Y + 1)⁻¹ *
          ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
            ‖perronZeroField chi sigma T t‖) ^ 2 ≤
      rightMaxSqBetween (truncatedZeroNormField chi sigma X T)
        (H + 1) (X + 1) (x - 1 / 2) := by
  rw [ofReal_alignedZeroAverage_eq_rightAverage chi hXtwo hx hY hYX]
  exact le_iSup_of_le (Y + 1) <| le_iSup_of_le (by linarith) <|
    le_iSup_of_le (by linarith) le_rfl

end
end MAPAPAlignedMaximalAdapter

#print axioms MAPAPAlignedMaximalAdapter.ofReal_alignedZeroAverage_eq_rightAverage
#print axioms MAPAPAlignedMaximalAdapter.ofReal_alignedZeroAverage_sq_le_rightMax
