import GuthMaynardLemma62FarTail
import GuthMaynardLemma62MellinInversion

/-!
# Exact Mellin insertion before the reflection substitution

This is the last pointwise step before the Fubini/change-of-variables passage
in the published proof of Guth--Maynard Lemma 6.2.  It inserts the now
inhabited Mellin inversion formula into the literal Fourier coefficient on
the actual support `[1,2]`.
-/

namespace GuthMaynardLemma62MellinInsertion

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardSectionThreeCutoff
open GuthMaynardLemma62FarTail GuthMaynardLemma62MellinInversion

noncomputable section

def sectionThreeFourierPhase (xi u : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * u * xi : ℝ) : ℂ) * Complex.I)

def sectionThreeMellinLineIntegral (u : ℝ) : ℂ :=
  ∫ r : ℝ,
    (u : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) *
      mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)

/-- Exact pointwise insertion of Mellin inversion into `\widehat h_t(ξ)`.
No Fubini swap or asymptotic truncation is used here. -/
theorem sectionThreeFourierCoefficient_eq_mellinInserted
    (t xi : ℝ) :
    sectionThreeFourierCoefficient t xi =
      ∫ u : ℝ in Set.Icc (1 : ℝ) 2,
        sectionThreeFourierPhase xi u *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            sectionThreeMellinLineIntegral u) *
          (u : ℂ) ^ (Complex.I * (t : ℂ)) := by
  rw [sectionThreeFourierCoefficient_eq_integral]
  have hrestrict :
      (∫ u : ℝ,
        Complex.exp (((-2 * Real.pi * u * xi : ℝ) : ℂ) * Complex.I) *
          sectionThreeOscillatory t u) =
      ∫ u : ℝ in Set.Icc (1 : ℝ) 2,
        Complex.exp (((-2 * Real.pi * u * xi : ℝ) : ℂ) * Complex.I) *
          sectionThreeOscillatory t u := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Icc (1 : ℝ) 2
    · simp [hu]
    · simp [hu, sectionThreeOscillatory_supported t u hu]
  rw [hrestrict]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have huPos : 0 < u := by linarith [hu.1]
  unfold sectionThreeOscillatory
  rw [sectionThreeCutoff_mellin_inversion huPos]
  unfold sectionThreeFourierPhase sectionThreeMellinLineIntegral
  ring

end

end GuthMaynardLemma62MellinInsertion

#print axioms GuthMaynardLemma62MellinInsertion.sectionThreeFourierCoefficient_eq_mellinInserted
