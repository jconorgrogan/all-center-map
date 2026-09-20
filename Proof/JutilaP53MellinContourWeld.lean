import JutilaP53TwoScaleContour

/-!
# Weld from the p.53 inner series to the movable contour

This combines the two separately certified right-line integrals into the
single residue-cancelled contour integrand.  It is the exact bridge between
the divisor-expanded arithmetic series and the finite contour theorem.
-/

namespace MAPJutilaP53MellinContourWeld

open Complex MeasureTheory
open MAPJutilaP53InnerMellinRightLine
open MAPJutilaP53TwoScaleContour

noncomputable section

theorem p53InnerTwoScale_eq_rightContour
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) :
    p53InnerTwoScale chi s U V =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          p53TwoScaleContourIntegrand chi s U V
            (((1 : ℝ) : ℂ) + v * I)) := by
  rw [p53InnerTwoScale_eq_LFunction_gamma_rightLine chi hs hU hV]
  have hIntU := integrable_p53RightOneScaleIntegrand chi hs hU
  have hIntV := integrable_p53RightOneScaleIntegrand chi hs hV
  rw [← mul_sub]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ v : ℝ, p53RightOneScaleIntegrand chi s U v) -
        ∫ v : ℝ, p53RightOneScaleIntegrand chi s V v)) = _
  rw [← MeasureTheory.integral_sub hIntU hIntV]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  have hw : (((1 : ℝ) : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  rw [p53TwoScaleContourIntegrand_eq_raw chi s U V hw]
  unfold p53RightOneScaleIntegrand p53ScaleDifference
  ring

end

end MAPJutilaP53MellinContourWeld

#print axioms MAPJutilaP53MellinContourWeld.p53InnerTwoScale_eq_rightContour
