import GuthMaynardMellinRapidDecay
import GuthMaynardJIterationBumpWeld

/-!
# A concrete legal Section 3 cutoff for Guth--Maynard

The paper fixes a smooth bump supported on `[1,2]` without requiring a
special formula.  This file gives one concrete realization using the already
certified `sourceBump`: translate the radius-`1/4` plateau bump to center
`3/2`, then square it.  The result is smooth, supported on `[1,2]`, and its
Mellin transform satisfies the arbitrary-order estimates proved in
`GuthMaynardMellinRapidDecay`.
-/

namespace GuthMaynardSectionThreeCutoff

open Real Complex Set MeasureTheory Metric
open scoped FourierTransform SchwartzMap ContDiff
open GuthMaynardJIteration GuthMaynardMellinRapidDecay

noncomputable section

theorem fifth_pos : (0 : ℝ) < 1 / 5 := by norm_num

/-- Two overlapping bumps give independent effective inner and outer radii:
their union is one on `[6/5,9/5]` and supported on `[1,2]`.  This avoids a
code-generation defect in the release-candidate Lean toolchain triggered by
defining a new `ContDiffBump` structure directly. -/
def sectionThreeCutoffReal (x : ℝ) : ℝ :=
  let left := GuthMaynardJIteration.sourceBump (1 / 5) fifth_pos (x - 7 / 5)
  let right := GuthMaynardJIteration.sourceBump (1 / 5) fifth_pos (x - 8 / 5)
  1 - (1 - left) * (1 - right)

def sectionThreeCutoff (x : ℝ) : ℂ :=
  (sectionThreeCutoffReal x : ℂ) ^ 2

/-- The exact plateau required by Guth--Maynard Section 3. -/
theorem sectionThreeCutoff_eq_one
    {x : ℝ} (hx : x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ)) :
    sectionThreeCutoff x = 1 := by
  by_cases hmid : x ≤ 8 / 5
  · have hleft : |x - 7 / 5| ≤ (1 / 5 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [hx.1]
    rw [sectionThreeCutoff, sectionThreeCutoffReal,
      GuthMaynardJIteration.sourceBump_eq_one_of_abs_le
        (1 / 5) fifth_pos hleft]
    norm_num
  · have hright : |x - 8 / 5| ≤ (1 / 5 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [hx.2]
    rw [sectionThreeCutoff, sectionThreeCutoffReal,
      GuthMaynardJIteration.sourceBump_eq_one_of_abs_le
        (1 / 5) fifth_pos hright]
    norm_num

theorem sectionThreeCutoff_supported
    (x : ℝ) (hx : x ∉ Set.Icc (1 : ℝ) 2) :
    sectionThreeCutoff x = 0 := by
  have hleft : 2 * (1 / 5 : ℝ) ≤ |x - 7 / 5| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have hright : 2 * (1 / 5 : ℝ) ≤ |x - 8 / 5| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  rw [sectionThreeCutoff, sectionThreeCutoffReal,
    GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
      (1 / 5) fifth_pos hleft,
    GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
      (1 / 5) fifth_pos hright]
  norm_num

theorem sectionThreeCutoff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) sectionThreeCutoff := by
  have hleft : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => GuthMaynardJIteration.sourceBump
        (1 / 5) fifth_pos (x - 7 / 5)) :=
    (GuthMaynardJIteration.sourceBump_contDiff (1 / 5) fifth_pos).comp
      (contDiff_id.sub contDiff_const)
  have hright : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => GuthMaynardJIteration.sourceBump
        (1 / 5) fifth_pos (x - 8 / 5)) :=
    (GuthMaynardJIteration.sourceBump_contDiff (1 / 5) fifth_pos).comp
      (contDiff_id.sub contDiff_const)
  have hreal : ContDiff ℝ (⊤ : ℕ∞) sectionThreeCutoffReal := by
    unfold sectionThreeCutoffReal
    exact contDiff_const.sub ((contDiff_const.sub hleft).mul
      (contDiff_const.sub hright))
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => (sectionThreeCutoffReal x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  unfold sectionThreeCutoff
  exact hc.pow 2

/-- Arbitrary-order decay for the concrete Section 3 cutoff. -/
theorem sectionThreeCutoff_mellin_rapidDecay
    (k : ℕ) (r : ℝ) :
    |r / (2 * Real.pi)| ^ k *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (mellinLogLiftSchwartz sectionThreeCutoff
          (mellinLogLift_hasCompactSupport
            (by norm_num) (by norm_num) sectionThreeCutoff_supported)
          (mellinLogLift_contDiff sectionThreeCutoff_contDiff)) :
            𝓢(ℝ, ℂ)) := by
  exact scaledPower_mul_norm_mellin_line_one_le_seminorm
    (by norm_num) (by norm_num) sectionThreeCutoff_supported
    sectionThreeCutoff_contDiff k r

/-- Positive arbitrary-order Mellin tail for the concrete cutoff. -/
theorem sectionThreeCutoff_mellin_positiveTail
    {R : ℝ} {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    let S := SchwartzMap.seminorm ℂ k 0
      (𝓕 (mellinLogLiftSchwartz sectionThreeCutoff
        (mellinLogLift_hasCompactSupport
          (by norm_num) (by norm_num) sectionThreeCutoff_supported)
        (mellinLogLift_contDiff sectionThreeCutoff_contDiff)) :
          𝓢(ℝ, ℂ))
    ‖∫ r : ℝ in Set.Ioi R,
        mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ ≤
      ((2 * Real.pi) ^ k * S) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  exact norm_integral_Ioi_mellin_line_one_le
    (by norm_num) (by norm_num) sectionThreeCutoff_supported
    sectionThreeCutoff_contDiff hk hR

/-- Negative arbitrary-order Mellin tail for the concrete cutoff. -/
theorem sectionThreeCutoff_mellin_negativeTail
    {R : ℝ} {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    let S := SchwartzMap.seminorm ℂ k 0
      (𝓕 (mellinLogLiftSchwartz sectionThreeCutoff
        (mellinLogLift_hasCompactSupport
          (by norm_num) (by norm_num) sectionThreeCutoff_supported)
        (mellinLogLift_contDiff sectionThreeCutoff_contDiff)) :
          𝓢(ℝ, ℂ))
    ‖∫ r : ℝ in Set.Iic (-R),
        mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ ≤
      ((2 * Real.pi) ^ k * S) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  exact norm_integral_Iic_mellin_line_one_le
    (by norm_num) (by norm_num) sectionThreeCutoff_supported
    sectionThreeCutoff_contDiff hk hR

end

end GuthMaynardSectionThreeCutoff

#print axioms GuthMaynardSectionThreeCutoff.sectionThreeCutoff_supported
#print axioms GuthMaynardSectionThreeCutoff.sectionThreeCutoff_eq_one
#print axioms GuthMaynardSectionThreeCutoff.sectionThreeCutoff_contDiff
#print axioms GuthMaynardSectionThreeCutoff.sectionThreeCutoff_mellin_rapidDecay
#print axioms GuthMaynardSectionThreeCutoff.sectionThreeCutoff_mellin_positiveTail
#print axioms GuthMaynardSectionThreeCutoff.sectionThreeCutoff_mellin_negativeTail
