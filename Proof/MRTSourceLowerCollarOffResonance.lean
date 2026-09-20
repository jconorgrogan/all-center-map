import MRTSourceLowerCollarVdC
import MRTNonstationaryPhaseTwoIBPEndpointBound
import MRTSourcePacketAmplitudeC2

/-! # Two-IBP amplitude budgets off the lower-collar resonance cell -/

namespace MAPMRTSourceLowerCollarOffResonance

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTVanDerCorput
open MAPMRTSourcePacketAmplitudeC2
open MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarAmplitudeGain
open MAPMRTNonstationaryPhaseTwoIBPEndpointBound

noncomputable section

/-- The exact second derivative of the lower-collar packet difference. -/
def sourceLowerCollarAmplitudeDifferenceSecond
    (X H x : ℝ)
    (cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ) (w : ℝ) : ℂ :=
  sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
      (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ 0) w -
    sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
      outer outer' outer'' w

theorem hasDerivAt_sourceLowerCollarAmplitudeDifferenceDeriv
    {X H x w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hcutoff : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff' : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (houter : ∀ z, HasDerivAt outer (outer' z) z)
    (houter' : ∀ z, HasDerivAt outer' (outer'' z) z) :
    HasDerivAt
      (sourceLowerCollarAmplitudeDifferenceDeriv
        X H x cutoff cutoff' outer outer')
      (sourceLowerCollarAmplitudeDifferenceSecond
        X H x cutoff cutoff' cutoff'' outer outer' outer'' w) w := by
  exact (hasDerivAt_sourcePacketAmplitudeDeriv hcutoff hcutoff'
    (fun z ↦ hasDerivAt_const z 1) (fun z ↦ hasDerivAt_const z 0)).sub
      (hasDerivAt_sourcePacketAmplitudeDeriv hcutoff hcutoff' houter houter')

/-- At the endpoint `H=X/2`, the inner cutoff gains the actual exponential
scale, uniformly for every `x≥X/2`. -/
theorem abs_cutoff_on_lowerTail_le_two_mul_derivBound_mul_exp
    {X x w B : ℝ} {cutoff cutoff' : ℝ → ℝ}
    (hX : 0 < X) (hxLower : X / 2 ≤ x) (hB : 0 ≤ B)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B) :
    |cutoff ((X * Real.exp w - x) / (X / 2))| ≤
      2 * B * Real.exp w := by
  let y : ℝ := (X * Real.exp w - x) / (X / 2)
  by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
  · have hgain := abs_cutoff_le_derivBound_mul_distance_from_neg_one
      hcutoffSupport hcutoffDeriv hcutoff'Bound hy
    have hcoord : y + 1 ≤ 2 * Real.exp w := by
      unfold y
      field_simp [ne_of_gt hX]
      nlinarith
    calc
      |cutoff ((X * Real.exp w - x) / (X / 2))| = |cutoff y| := rfl
      _ ≤ B * (y + 1) := hgain
      _ ≤ B * (2 * Real.exp w) := mul_le_mul_of_nonneg_left hcoord hB
      _ = 2 * B * Real.exp w := by ring
  · have habs : 1 ≤ |y| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_nonpos (by linarith : y ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ y)]
        exact hy.le
    rw [show (X * Real.exp w - x) / (X / 2) = y by rfl,
      hcutoffSupport y habs, abs_zero]
    positivity

private theorem norm_add_six_le (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  calc
    _ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
    _ ≤ (‖a + b + c + d‖ + ‖e‖) + ‖f‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖a + b + c‖ + ‖d‖) + ‖e‖) + ‖f‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ ((((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖ := by
      gcongr; exact norm_add_le _ _
    _ = _ := by ring

/-- Six-term pointwise norm expansion of the literal second amplitude
 derivative. -/
theorem norm_sourcePacketAmplitudeSecond_le_terms
    (X H x w : ℝ)
    (cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ) :
    ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'' w‖ ≤
      Real.exp (w / 2) / 4 * |cutoff ((X * Real.exp w - x) / H)| *
          |outer (w / 100)| +
      2 * Real.exp (w / 2) * |cutoff' ((X * Real.exp w - x) / H)| *
          |X * Real.exp w / H| * |outer (w / 100)| +
      Real.exp (w / 2) * |cutoff'' ((X * Real.exp w - x) / H)| *
          |X * Real.exp w / H| ^ 2 * |outer (w / 100)| +
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          (|outer' (w / 100)| / 100) +
      2 * Real.exp (w / 2) * |cutoff' ((X * Real.exp w - x) / H)| *
          |X * Real.exp w / H| * (|outer' (w / 100)| / 100) +
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          (|outer'' (w / 100)| / 10000) := by
  unfold sourcePacketAmplitudeSecond
  refine (norm_add_six_le _ _ _ _ _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_div, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 100),
    abs_of_pos (by norm_num : (0 : ℝ) < 10000)]
  norm_num
  ring_nf
  exact le_rfl

/-- Pointwise C2 budget retaining the exponential boundary gain. -/
theorem norm_sourceLowerCollarAmplitudeDifferenceSecond_le
    {X x w U B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hxLower : X / 2 ≤ x)
    (hU : 0 ≤ U) (hwUpper : Real.exp w ≤ U)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bo1)
    (houter''Bound : ∀ z, |outer'' z| ≤ Bo2) :
    ‖sourceLowerCollarAmplitudeDifferenceSecond X (X / 2) x
        cutoff cutoff' cutoff'' outer outer' outer'' w‖ ≤
      Real.exp (w / 2) *
        (B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
          2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000) := by
  have hc := abs_cutoff_on_lowerTail_le_two_mul_derivBound_mul_exp (w := w)
    hX hxLower hB1 hcutoffSupport hcutoffDeriv hcutoff'Bound
  have hc' := abs_cutoff_on_lowerTail_le_two_mul_derivBound_mul_exp (w := w)
    hX hxLower hB2 hcutoff'Support hcutoffSecond hcutoff''Bound
  have hcU : |cutoff ((X * Real.exp w - x) / (X / 2))| ≤ 2 * B1 * U :=
    hc.trans (mul_le_mul_of_nonneg_left hwUpper (by positivity))
  have hc'U : |cutoff' ((X * Real.exp w - x) / (X / 2))| ≤ 2 * B2 * U :=
    hc'.trans (mul_le_mul_of_nonneg_left hwUpper (by positivity))
  have hrU : |X * Real.exp w / (X / 2)| ≤ 2 * U := by
    rw [abs_of_nonneg (by positivity : 0 ≤ X * Real.exp w / (X / 2))]
    have hden : 0 < X / 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hzero := norm_sourcePacketAmplitudeSecond_le_terms X (X / 2) x w
    cutoff cutoff' cutoff'' (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ 0)
  have hone := norm_sourcePacketAmplitudeSecond_le_terms X (X / 2) x w
    cutoff cutoff' cutoff'' outer outer' outer''
  norm_num at hzero
  have hzero' :
      ‖sourcePacketAmplitudeSecond X (X / 2) x cutoff cutoff' cutoff''
        (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ 0) w‖ ≤
      Real.exp (w / 2) * (B1 * U / 2 + 12 * B2 * U ^ 2) := by
    calc
      _ ≤ Real.exp (w / 2) / 4 *
            |cutoff ((X * Real.exp w - x) / (X / 2))| +
          2 * Real.exp (w / 2) *
            |cutoff' ((X * Real.exp w - x) / (X / 2))| *
              |X * Real.exp w / (X / 2)| +
          Real.exp (w / 2) *
            |cutoff'' ((X * Real.exp w - x) / (X / 2))| *
              |X * Real.exp w / (X / 2)| ^ 2 := by
        simpa [sq_abs] using hzero
      _ ≤ Real.exp (w / 2) / 4 * (2 * B1 * U) +
          2 * Real.exp (w / 2) * (2 * B2 * U) * (2 * U) +
          Real.exp (w / 2) * B2 * (2 * U) ^ 2 := by
        gcongr
        exact hcutoff''Bound _
      _ = _ := by ring
  have hone' :
      ‖sourcePacketAmplitudeSecond X (X / 2) x cutoff cutoff' cutoff''
        outer outer' outer'' w‖ ≤
      Real.exp (w / 2) * (B1 * U / 2 + 12 * B2 * U ^ 2 +
        B1 * Bo1 * U / 50 + 2 * B2 * Bo1 * U ^ 2 / 25 +
        B1 * Bo2 * U / 5000) := by
    calc
      _ ≤ Real.exp (w / 2) / 4 * (2 * B1 * U) * 1 +
          2 * Real.exp (w / 2) * (2 * B2 * U) * (2 * U) * 1 +
          Real.exp (w / 2) * B2 * (2 * U) ^ 2 * 1 +
          Real.exp (w / 2) * (2 * B1 * U) * (Bo1 / 100) +
          2 * Real.exp (w / 2) * (2 * B2 * U) * (2 * U) * (Bo1 / 100) +
          Real.exp (w / 2) * (2 * B1 * U) * (Bo2 / 10000) := by
        exact hone.trans (by
          gcongr
          all_goals first
            | exact hcutoff''Bound _
            | exact houterBound _
            | exact houter'Bound _
            | exact houter''Bound _)
      _ = _ := by ring
  unfold sourceLowerCollarAmplitudeDifferenceSecond
  calc
    _ ≤ ‖sourcePacketAmplitudeSecond X (X / 2) x cutoff cutoff' cutoff''
          (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ 0) w‖ +
        ‖sourcePacketAmplitudeSecond X (X / 2) x cutoff cutoff' cutoff''
          outer outer' outer'' w‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hzero' hone'
    _ = _ := by ring

end
end MAPMRTSourceLowerCollarOffResonance

#print axioms MAPMRTSourceLowerCollarOffResonance.hasDerivAt_sourceLowerCollarAmplitudeDifferenceDeriv
#print axioms MAPMRTSourceLowerCollarOffResonance.abs_cutoff_on_lowerTail_le_two_mul_derivBound_mul_exp
#print axioms MAPMRTSourceLowerCollarOffResonance.norm_sourcePacketAmplitudeSecond_le_terms
#print axioms MAPMRTSourceLowerCollarOffResonance.norm_sourceLowerCollarAmplitudeDifferenceSecond_le
