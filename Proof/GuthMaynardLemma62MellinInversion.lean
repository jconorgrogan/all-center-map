import GuthMaynardSectionThreeCutoff
import GuthMaynardReflectionMellin

/-!
# Inhabiting the Mellin inversion used in Guth--Maynard Lemma 6.2

This discharges the convergence and vertical-integrability hypotheses for
the literal Section 3 cutoff.  The latter is obtained from the already
certified Mellin--Fourier identity and the fact that a Fourier transform of
a Schwartz function is integrable.
-/

namespace GuthMaynardLemma62MellinInversion

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
open GuthMaynardSectionThreeCutoff GuthMaynardMellinRapidDecay
open GuthMaynardReflectionMellin

noncomputable section

theorem sectionThreeCutoff_hasCompactSupport :
    HasCompactSupport sectionThreeCutoff := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
  exact sectionThreeCutoff_supported

def sectionThreeMellinLogSchwartz : 𝓢(ℝ, ℂ) :=
  mellinLogLiftSchwartz sectionThreeCutoff
    (mellinLogLift_hasCompactSupport
      (by norm_num) (by norm_num) sectionThreeCutoff_supported)
    (mellinLogLift_contDiff sectionThreeCutoff_contDiff)

theorem sectionThreeMellinLogSchwartz_apply (u : ℝ) :
    sectionThreeMellinLogSchwartz u =
      mellinLogLift sectionThreeCutoff u := rfl

/-- The exact vertical-integrability hypothesis on the Mellin line
`Re(s)=1`. -/
theorem sectionThreeCutoff_verticalIntegrable :
    Complex.VerticalIntegrable (mellin sectionThreeCutoff) 1 := by
  unfold Complex.VerticalIntegrable
  have hfourier : Integrable
      (fun r : ℝ =>
        ((𝓕 sectionThreeMellinLogSchwartz : 𝓢(ℝ, ℂ)) r)) :=
    (𝓕 sectionThreeMellinLogSchwartz : 𝓢(ℝ, ℂ)).integrable
  have hscaled := hfourier.comp_div
    (show 2 * Real.pi ≠ 0 by positivity)
  apply hscaled.congr
  filter_upwards with r
  change ((𝓕 sectionThreeMellinLogSchwartz : 𝓢(ℝ, ℂ))
      (r / (2 * Real.pi))) =
    mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)
  rw [mellin_line_one_eq_fourier_logLift]
  have hcoe := congrFun
    (SchwartzMap.fourier_coe sectionThreeMellinLogSchwartz).symm
    (r / (2 * Real.pi))
  exact hcoe.symm

theorem sectionThreeCutoff_mellinConvergent :
    MellinConvergent sectionThreeCutoff (1 : ℂ) :=
  mellinConvergent_one_of_compactSupport
    sectionThreeCutoff_contDiff.continuous
    sectionThreeCutoff_hasCompactSupport

/-- The literal line-one Mellin inversion formula used before the
`v=Nmu` reflection substitution in Lemma 6.2. -/
theorem sectionThreeCutoff_mellin_inversion
    {x : ℝ} (hx : 0 < x) :
    sectionThreeCutoff x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) *
            mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) := by
  exact mellin_inversion_line_one sectionThreeCutoff hx
    sectionThreeCutoff_mellinConvergent
    sectionThreeCutoff_verticalIntegrable
    sectionThreeCutoff_contDiff.continuous.continuousAt

end

end GuthMaynardLemma62MellinInversion

#print axioms GuthMaynardLemma62MellinInversion.sectionThreeCutoff_verticalIntegrable
#print axioms GuthMaynardLemma62MellinInversion.sectionThreeCutoff_mellin_inversion
