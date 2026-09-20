import MRTSourceLowerCollarResonance

/-!
# Boundary gain of the resonant lower-collar amplitude

The stationary point exposed in `MRTSourceLowerCollarResonance` is tied to the
left endpoint of the inner cutoff.  A first-order boundary zero supplies an
explicit factor equal to the distance from that endpoint.  This is the gain
needed by any stationary treatment of the collar packet difference.
-/

namespace MAPMRTSourceLowerCollarAmplitudeGain

open Set
open MAPMRTProposition51HardBranch

noncomputable section

/-- A differentiable cutoff supported on `[-1,1]` gains its distance from the
left endpoint. -/
theorem abs_cutoff_le_derivBound_mul_distance_from_neg_one
    {cutoff cutoff' : ℝ → ℝ} {B y : ℝ}
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |cutoff y| ≤ B * (y + 1) := by
  have hneg : cutoff (-1) = 0 :=
    hcutoffSupport (-1) (by norm_num)
  have hmv := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := cutoff) (f' := cutoff') (C := B)
    (fun z _ ↦ (hcutoffDeriv z).hasDerivWithinAt)
    (fun z _ ↦ by simpa [Real.norm_eq_abs] using hcutoff'Bound z)
    (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1) 1) hy
  rw [hneg, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have hyadd : 0 ≤ y + 1 := by linarith [hy.1]
  have hyabs : |y - -1| = y + 1 := by
    rw [abs_of_nonneg]
    · ring
    · linarith
  rw [hyabs] at hmv
  exact hmv

/-- At `H=X/2`, a resonant ratio `q<exp(-10)` can meet the cutoff only on
`x∈[X/2,X/2+Xq)`, and the inner cutoff there gains the factor `2q`. -/
theorem abs_cutoff_resonanceCoordinate_le_two_mul_derivBound_mul_ratio
    {X x q B : ℝ} {cutoff cutoff' : ℝ → ℝ}
    (hX : 0 < X) (hqTail : q < Real.exp (-10))
    (hx : x ∈ Set.Ico (X / 2) (X / 2 + X * q))
    (hB : 0 ≤ B)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B) :
    |cutoff ((X * q - x) / (X / 2))| ≤ 2 * B * q := by
  have hqOne : q < 1 :=
    hqTail.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 0 < X / 2 := by positivity
  have hy : (X * q - x) / (X / 2) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hden]
      linarith [hx.2]
    · rw [div_le_iff₀ hden]
      nlinarith [hx.1]
  have hgain := abs_cutoff_le_derivBound_mul_distance_from_neg_one
    hcutoffSupport hcutoffDeriv hcutoff'Bound hy
  have hcoord : (X * q - x) / (X / 2) + 1 ≤ 2 * q := by
    field_simp [ne_of_gt hX]
    nlinarith [hx.1]
  calc
    |cutoff ((X * q - x) / (X / 2))| ≤
        B * ((X * q - x) / (X / 2) + 1) := hgain
    _ ≤ B * (2 * q) := mul_le_mul_of_nonneg_left hcoord hB
    _ = 2 * B * q := by ring

/-- Uniform form on the full resonant cell `exp(w)≤2q`.  Outside the inner
cutoff support the claim is zero; inside it the boundary-distance argument
gives `4q`. -/
theorem abs_cutoff_on_resonanceCell_le_four_mul_derivBound_mul_ratio
    {X x q w B : ℝ} {cutoff cutoff' : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q)
    (hxLower : X / 2 ≤ x) (hwUpper : Real.exp w ≤ 2 * q)
    (hB : 0 ≤ B)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B) :
    |cutoff ((X * Real.exp w - x) / (X / 2))| ≤ 4 * B * q := by
  let y : ℝ := (X * Real.exp w - x) / (X / 2)
  by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
  · have hgain := abs_cutoff_le_derivBound_mul_distance_from_neg_one
      hcutoffSupport hcutoffDeriv hcutoff'Bound hy
    have hden : 0 < X / 2 := by positivity
    have hcoord : y + 1 ≤ 4 * q := by
      unfold y
      field_simp [ne_of_gt hX]
      nlinarith
    calc
      |cutoff ((X * Real.exp w - x) / (X / 2))| = |cutoff y| := rfl
      _ ≤ B * (y + 1) := hgain
      _ ≤ B * (4 * q) := mul_le_mul_of_nonneg_left hcoord hB
      _ = 4 * B * q := by ring
  · have habs : 1 ≤ |y| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_nonpos (by linarith : y ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ y)]
        exact hy.le
    have hz : cutoff y = 0 := hcutoffSupport y habs
    rw [show (X * Real.exp w - x) / (X / 2) = y by rfl, hz, abs_zero]
    positivity

/-- Pointwise packet-difference amplitude bound throughout the resonant cell.
This is the input for the weighted second-derivative estimate. -/
theorem norm_sourcePacketAmplitude_difference_on_resonanceCell_le
    {X x q w B : ℝ} {cutoff cutoff' outer : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q)
    (hxLower : X / 2 ≤ x) (hwUpper : Real.exp w ≤ 2 * q)
    (hB : 0 ≤ B)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B)
    (houterBound : ∀ z, |outer z| ≤ 1) :
    ‖sourcePacketAmplitude X (X / 2) x cutoff (fun _ ↦ 1) w -
        sourcePacketAmplitude X (X / 2) x cutoff outer w‖ ≤
      8 * B * q * Real.exp (w / 2) := by
  have hcut := abs_cutoff_on_resonanceCell_le_four_mul_derivBound_mul_ratio
    hX hqPos hxLower hwUpper hB hcutoffSupport hcutoffDeriv hcutoff'Bound
  have houterDiff : |1 - outer (w / 100)| ≤ 2 := by
    calc
      |1 - outer (w / 100)| ≤ |(1 : ℝ)| + |outer (w / 100)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (by norm_num) (houterBound _)
      _ = 2 := by norm_num
  unfold sourcePacketAmplitude
  change ‖(Real.exp (w / 2) : ℂ) *
      (cutoff ((X * Real.exp w - x) / (X / 2)) : ℂ) * (1 : ℂ) -
    (Real.exp (w / 2) : ℂ) *
      (cutoff ((X * Real.exp w - x) / (X / 2)) : ℂ) *
        (outer (w / 100) : ℂ)‖ ≤ 8 * B * q * Real.exp (w / 2)
  have hfactor :
      (Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / (X / 2)) : ℂ) * (1 : ℂ) -
        (Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / (X / 2)) : ℂ) *
            (outer (w / 100) : ℂ) =
      (Real.exp (w / 2) : ℂ) *
        (cutoff ((X * Real.exp w - x) / (X / 2)) : ℂ) *
          ((1 - outer (w / 100) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfactor, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (w / 2) *
          |cutoff ((X * Real.exp w - x) / (X / 2))| *
        |1 - outer (w / 100)| ≤
      Real.exp (w / 2) * (4 * B * q) * 2 := by gcongr
    _ = 8 * B * q * Real.exp (w / 2) := by ring

/-- The literal packet-difference amplitude at the stationary point therefore
has an additional factor `q`.  Absolute integration before extracting this
factor loses the endpoint estimate. -/
theorem norm_sourcePacketAmplitude_difference_at_resonance_le
    {X x q B : ℝ} {cutoff cutoff' outer : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q) (hqTail : q < Real.exp (-10))
    (hx : x ∈ Set.Ico (X / 2) (X / 2 + X * q))
    (hB : 0 ≤ B)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B)
    (houterBound : ∀ z, |outer z| ≤ 1) :
    ‖sourcePacketAmplitude X (X / 2) x cutoff (fun _ ↦ 1) (Real.log q) -
        sourcePacketAmplitude X (X / 2) x cutoff outer (Real.log q)‖ ≤
      4 * B * q * Real.exp (Real.log q / 2) := by
  have hexp : Real.exp (Real.log q) = q := Real.exp_log hqPos
  have hcut :=
    abs_cutoff_resonanceCoordinate_le_two_mul_derivBound_mul_ratio
      hX hqTail hx hB hcutoffSupport hcutoffDeriv hcutoff'Bound
  have houterDiff : |1 - outer (Real.log q / 100)| ≤ 2 := by
    calc
      |1 - outer (Real.log q / 100)| ≤ |(1 : ℝ)| + |outer (Real.log q / 100)| :=
        abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (by norm_num) (houterBound _)
      _ = 2 := by norm_num
  unfold sourcePacketAmplitude
  rw [hexp]
  change ‖(Real.exp (Real.log q / 2) : ℂ) *
      (cutoff ((X * q - x) / (X / 2)) : ℂ) * (1 : ℂ) -
    (Real.exp (Real.log q / 2) : ℂ) *
      (cutoff ((X * q - x) / (X / 2)) : ℂ) *
        (outer (Real.log q / 100) : ℂ)‖ ≤
      4 * B * q * Real.exp (Real.log q / 2)
  have hfactor :
      (Real.exp (Real.log q / 2) : ℂ) *
          (cutoff ((X * q - x) / (X / 2)) : ℂ) * (1 : ℂ) -
        (Real.exp (Real.log q / 2) : ℂ) *
          (cutoff ((X * q - x) / (X / 2)) : ℂ) *
          (outer (Real.log q / 100) : ℂ) =
      (Real.exp (Real.log q / 2) : ℂ) *
        (cutoff ((X * q - x) / (X / 2)) : ℂ) *
          ((1 - outer (Real.log q / 100) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfactor, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (Real.log q / 2) *
          |cutoff ((X * q - x) / (X / 2))| *
        |1 - outer (Real.log q / 100)| ≤
      Real.exp (Real.log q / 2) * (2 * B * q) * 2 := by
        gcongr
    _ = 4 * B * q * Real.exp (Real.log q / 2) := by ring

end

end MAPMRTSourceLowerCollarAmplitudeGain

#print axioms MAPMRTSourceLowerCollarAmplitudeGain.abs_cutoff_le_derivBound_mul_distance_from_neg_one
#print axioms MAPMRTSourceLowerCollarAmplitudeGain.abs_cutoff_resonanceCoordinate_le_two_mul_derivBound_mul_ratio
#print axioms MAPMRTSourceLowerCollarAmplitudeGain.abs_cutoff_on_resonanceCell_le_four_mul_derivBound_mul_ratio
#print axioms MAPMRTSourceLowerCollarAmplitudeGain.norm_sourcePacketAmplitude_difference_on_resonanceCell_le
#print axioms MAPMRTSourceLowerCollarAmplitudeGain.norm_sourcePacketAmplitude_difference_at_resonance_le
