import AppendixA4Detector
import RieszKernelBoundary

/-!
# Appendix A.4 with a high-order Riesz detector

The rational Mellin kernel has no Gamma factor.  Its pole at zero is canceled
by the zero of the translated L-function exactly as in the Gamma detector.
This module proves the resulting holomorphic extension and finite-rectangle
shift on the full paper strip.
-/

namespace MAPAppendixA4RieszDetector

open Set MeasureTheory Complex Filter
open scoped Topology
open MAPAppendixA4Detector MAPAppendixA4RieszKernel
open MAPMollifierCoefficientIdentity

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The denominator left after the pole at zero is canceled. -/
def regularizedRieszDenominator (k : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range k, (z + ((j + 1 : ℕ) : ℂ))

theorem regularizedRieszDenominator_ne_zero
    (k : ℕ) {z : ℂ} (hz : z ∈ contourStrip) :
    regularizedRieszDenominator k z ≠ 0 := by
  rw [regularizedRieszDenominator, Finset.prod_ne_zero_iff]
  intro j hj
  have hre : 0 < (z + ((j + 1 : ℕ) : ℂ)).re := by
    change -1 < z.re at hz
    simp only [Complex.add_re, Complex.natCast_re]
    have hj0 : (0 : ℝ) ≤ j := by positivity
    norm_num at *
    linarith
  intro hzero
  rw [hzero] at hre
  simp at hre

theorem analyticAt_regularizedRieszKernel
    (k : ℕ) {z : ℂ} (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (regularizedRieszKernel k) z := by
  unfold regularizedRieszKernel
  apply analyticAt_const.div
  · apply Finset.analyticAt_fun_prod
    intro j hj
    fun_prop
  · simpa [regularizedRieszDenominator] using
      regularizedRieszDenominator_ne_zero k hz

/-- Canonical zero-canceled Riesz detector integrand. -/
def regularizedRieszDetectorIntegrand
    (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (U k : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  regularizedRieszKernel k z * shiftedZeroQuotient chi rho z *
    (Y : ℂ) ^ z * mollifier chi U (rho + z)

theorem analyticAt_regularizedRieszDetectorIntegrand
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho z : ℂ} {U k : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (regularizedRieszDetectorIntegrand chi rho U k Y) z := by
  unfold regularizedRieszDetectorIntegrand
  have hpowDiff : Differentiable ℂ (fun w : ℂ => (Y : ℂ) ^ w) :=
    differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  exact ((((analyticAt_regularizedRieszKernel k hz).mul
    (analyticAt_shiftedZeroQuotient chi hchi rho z)).mul
    (hpowDiff.analyticAt z)).mul
    ((analyticAt_mollifier chi (rho + z)).comp (by fun_prop)))

/-- Away from zero, the regularized product is the literal
`Riesz-kernel * L * mollifier` integrand. -/
theorem regularizedRieszDetectorIntegrand_eq_raw
    (chi : DirichletCharacter ℂ q) {rho z : ℂ} {U k : ℕ} {Y : ℝ}
    (hrho : DirichletCharacter.LFunction chi rho = 0) (hz : z ≠ 0) :
    regularizedRieszDetectorIntegrand chi rho U k Y z =
      rieszMellinKernel k z *
        DirichletCharacter.LFunction chi (rho + z) *
        (Y : ℂ) ^ z * mollifier chi U (rho + z) := by
  rw [regularizedRieszDetectorIntegrand,
    shiftedZeroQuotient_eq_div chi hrho hz,
    rieszMellinKernel_eq_div_regularized]
  field_simp

/-- Exact finite rectangle shift with the Riesz detector at the paper
endpoints.  Only the pole at zero lies between the two vertical lines, and it
has already been canceled. -/
theorem finiteRectangle_mollifiedRieszDetector_shift
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} {U k : ℕ} {Y B : ℝ}
    (hY : 0 < Y) (hB : 0 ≤ B)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1) :
    let a : ℝ := 1 / 2 - rho.re
    (∫ x : ℝ in a..(1 / 2),
        regularizedRieszDetectorIntegrand chi rho U k Y (x - B * I)) -
      (∫ x : ℝ in a..(1 / 2),
        regularizedRieszDetectorIntegrand chi rho U k Y (x + B * I)) +
      I * (∫ t : ℝ in -B..B,
        regularizedRieszDetectorIntegrand chi rho U k Y
          ((1 / 2 : ℝ) + t * I)) -
      I * (∫ t : ℝ in -B..B,
        regularizedRieszDetectorIntegrand chi rho U k Y (a + t * I)) = 0 := by
  dsimp only
  apply finite_rectangle_balance
  · linarith
  · exact hB
  · intro z hz
    apply analyticAt_regularizedRieszDetectorIntegrand chi hchi hY
    change -1 < z.re
    have hleft : 1 / 2 - rho.re ≤ z.re := by
      have hle : 1 / 2 - rho.re ≤ (1 / 2 : ℝ) := by linarith
      have hzleft := hz.1.1
      rw [min_eq_left hle] at hzleft
      exact hzleft
    linarith

end

end MAPAppendixA4RieszDetector
