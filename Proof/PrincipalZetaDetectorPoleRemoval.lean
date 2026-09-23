import PrincipalZetaCompactCrowding
import AppendixA4Detector
import AppendixA4GammaTails

/-!
# Exact pole removal for the principal zeta detector

The nonprincipal Appendix A.4 contour cannot simply be specialized to the
principal character: shifting the raw zeta detector crosses the pole at
`rho + z = 1`.  This file isolates and removes that pole exactly.

If `F(s) = (s-1) zeta(s)` is the entire principal regularization and `rho` is
a nontrivial zero, first divide `F(rho+z)` analytically by `z`.  The remaining
detector numerator `A(z)` is entire on the contour strip.  The raw detector is
`A(z)/(z-(1-rho))`; subtracting its literal residue produces the analytic
divided difference of `A` at `1-rho`.

Thus the principal repair is an explicit residue term, not an assumption that
the nonprincipal proof applies at conductor one.
-/

namespace MAPPrincipalZetaDetectorPoleRemoval

open Set MeasureTheory Complex Filter
open MAPMollifierCoefficientIdentity MAPMellinDetectorLeaf
open MAPAppendixA4Detector

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

@[simp] theorem principalRegularized_one : principalF 1 = 1 := by
  simp [MAPPrincipalZetaFixedStrip.principalRegularized,
    DirichletCharacter.LFunctionTrivChar₁]

/-- The analytic quotient `F(rho+z)/z`, filled at `z=0`. -/
def principalShiftedZeroQuotient (rho z : ℂ) : ℂ :=
  dslope principalF rho (rho + z)

theorem principalShiftedZeroQuotient_eq_div
    {rho z : ℂ} (hrho : principalF rho = 0) (hz : z ≠ 0) :
    principalShiftedZeroQuotient rho z = principalF (rho + z) / z := by
  rw [principalShiftedZeroQuotient, dslope_of_ne]
  · simp [slope, hrho, div_eq_inv_mul]
  · intro h
    apply hz
    have : rho + z = rho + 0 := by simpa using h
    exact add_left_cancel this

theorem analyticAt_principalShiftedZeroQuotient (rho z : ℂ) :
    AnalyticAt ℂ (principalShiftedZeroQuotient rho) z := by
  have hdiff : Differentiable ℂ principalF :=
    DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  by_cases hz : z = 0
  · subst z
    rcases hdiff.analyticAt rho with ⟨p, hp⟩
    have hds : AnalyticAt ℂ (dslope principalF rho) rho :=
      ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    have hds' : AnalyticAt ℂ (dslope principalF rho) (rho + 0) := by
      simpa using hds
    simpa [principalShiftedZeroQuotient, Function.comp_def] using!
      hds'.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => rho + w) 0)
  · have hdiv : AnalyticAt ℂ
        (fun w : ℂ => (principalF (rho + w) - principalF rho) / w) z := by
      apply AnalyticAt.div
      · exact ((hdiff.analyticAt (rho + z)).comp (by fun_prop)).sub
          analyticAt_const
      · exact analyticAt_id
      · exact hz
    apply hdiv.congr
    have hne : rho + z ≠ rho := by
      intro h
      apply hz
      exact add_left_cancel (by simpa using h : rho + z = rho + 0)
    have hev := dslope_eventuallyEq_slope_of_ne principalF hne
    have hmap : Tendsto (fun w : ℂ => rho + w) (nhds z) (nhds (rho + z)) :=
      tendsto_const_nhds.add tendsto_id
    filter_upwards [hev.comp_tendsto hmap, isOpen_ne.mem_nhds hz]
      with w hw hw0
    simp only [Function.comp_apply] at hw
    rw [principalShiftedZeroQuotient, hw]
    simp [slope, div_eq_inv_mul]

/-- Entire numerator left after removing the zero at `z=0`; the only raw
principal singularity still present is division by `rho+z-1`. -/
def principalDetectorNumerator
    (rho : ℂ) (U : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (z + 1) * principalShiftedZeroQuotient rho z *
    (Y : ℂ) ^ z * mollifier chiOne U (rho + z)

theorem analyticAt_principalDetectorNumerator
    {rho z : ℂ} {U : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (principalDetectorNumerator rho U Y) z := by
  unfold principalDetectorNumerator
  have hpowDiff : Differentiable ℂ (fun w : ℂ => (Y : ℂ) ^ w) :=
    differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  exact ((((analyticAt_Gamma_add_one_of_mem_contourStrip hz).mul
    (analyticAt_principalShiftedZeroQuotient rho z)).mul
    (hpowDiff.analyticAt z)).mul
    ((analyticAt_mollifier chiOne (rho + z)).comp (by fun_prop)))

/-- Away from both `z=0` and the zeta pole, the numerator divided by
`rho+z-1` is exactly the raw Gamma--zeta--mollifier detector. -/
theorem principalDetectorNumerator_div_eq_raw
    {rho z : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : principalF rho = 0) (hz : z ≠ 0)
    (hpole : rho + z ≠ 1) :
    principalDetectorNumerator rho U Y z / (rho + z - 1) =
      gammaMellinWeight Y z * riemannZeta (rho + z) *
        mollifier chiOne U (rho + z) := by
  rw [principalDetectorNumerator,
    principalShiftedZeroQuotient_eq_div hrho hz,
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hpole,
    gammaMellinWeight, Complex.Gamma_add_one z hz]
  have hden : rho + z - 1 ≠ 0 := sub_ne_zero.mpr hpole
  field_simp [hden]

/-- The crossed pole in the translation variable. -/
def principalPoleLocation (rho : ℂ) : ℂ := 1 - rho

/-- The literal residue of the raw principal detector at `rho+z=1`. -/
def principalDetectorResidue (rho : ℂ) (U : ℕ) (Y : ℝ) : ℂ :=
  principalDetectorNumerator rho U Y (principalPoleLocation rho)

/-- At the crossed zeta pole, the shifted-zero quotient is exactly the
reciprocal displacement from the zero to one. -/
theorem principalShiftedZeroQuotient_at_pole
    {rho : ℂ} (hrho : principalF rho = 0) (hrhoOne : rho ≠ 1) :
    principalShiftedZeroQuotient rho (principalPoleLocation rho) =
      1 / (1 - rho) := by
  have hz : principalPoleLocation rho ≠ 0 := by
    unfold principalPoleLocation
    exact sub_ne_zero.mpr (Ne.symm hrhoOne)
  rw [principalShiftedZeroQuotient_eq_div hrho hz]
  simp [principalPoleLocation]

/-- Closed formula for the only additional term introduced by the principal
detector.  This is the exact quantity whose exponential Gamma decay must be
absorbed in the high-ordinate branch. -/
theorem principalDetectorResidue_eq
    {rho : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : principalF rho = 0) (hrhoOne : rho ≠ 1) :
    principalDetectorResidue rho U Y =
      Complex.Gamma (2 - rho) * (1 / (1 - rho)) *
        (Y : ℂ) ^ (1 - rho) * mollifier chiOne U 1 := by
  unfold principalDetectorResidue principalDetectorNumerator
  rw [principalShiftedZeroQuotient_at_pole hrho hrhoOne]
  unfold principalPoleLocation
  congr 3 <;> ring

/-- Explicit exponential envelope for the crossed principal residue.  The
factor `1 / |Im rho|` comes from the displacement to the pole; no lower bound
for the first zeta ordinate is built into the statement. -/
theorem norm_principalDetectorResidue_le
    {rho : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : principalF rho = 0) (hrhoOne : rho ≠ 1)
    (hbetaLow : 1 / 2 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : 1 ≤ |rho.im|) (hY : 0 < Y) :
    ‖principalDetectorResidue rho U Y‖ ≤
      12 * (1 + |rho.im|) * Real.exp (-|rho.im|) *
        (1 / |rho.im|) * Real.rpow Y (1 - rho.re) * (U + 1) := by
  rw [principalDetectorResidue_eq hrho hrhoOne]
  repeat' rw [norm_mul]
  have hGamma :
      ‖Complex.Gamma (2 - rho)‖ ≤
        12 * (1 + |rho.im|) * Real.exp (-|rho.im|) := by
    have h := GammaCompactStripScratch.norm_Gamma_positive_strip_le_exp
      (s := 2 - rho.re) (t := -rho.im) (by linarith) (by linarith)
    have harg :
        (2 : ℂ) - rho =
          GammaCompactStripScratch.stripPoint (2 - rho.re) (-rho.im) := by
      apply Complex.ext <;>
        simp [GammaCompactStripScratch.stripPoint]
    rw [harg]
    simpa [abs_neg] using h
  have himNorm : |rho.im| ≤ ‖1 - rho‖ := by
    have h := Complex.abs_im_le_norm (1 - rho)
    simpa using h
  have hinv : ‖1 / (1 - rho)‖ ≤ 1 / |rho.im| := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by positivity) himNorm
  have hpow : ‖(Y : ℂ) ^ (1 - rho)‖ = Real.rpow Y (1 - rho.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp
  have hmoll : ‖mollifier chiOne U 1‖ ≤ U + 1 := by
    exact MAPAppendixA4GammaTails.norm_mollifier_le_card chiOne U (by norm_num)
  rw [hpow]
  have hfirst :
      ‖Complex.Gamma (2 - rho)‖ * ‖1 / (1 - rho)‖ ≤
        (12 * (1 + |rho.im|) * Real.exp (-|rho.im|)) *
          (1 / |rho.im|) :=
    mul_le_mul hGamma hinv (norm_nonneg _) (by positivity)
  have hsecond :
      ‖Complex.Gamma (2 - rho)‖ * ‖1 / (1 - rho)‖ *
          Real.rpow Y (1 - rho.re) ≤
        (12 * (1 + |rho.im|) * Real.exp (-|rho.im|)) *
          (1 / |rho.im|) * Real.rpow Y (1 - rho.re) :=
    mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hY.le _)
  have hrightNonneg :
      0 ≤ (12 * (1 + |rho.im|) * Real.exp (-|rho.im|)) *
          (1 / |rho.im|) * Real.rpow Y (1 - rho.re) := by
    have hfront :
        0 ≤ 12 * (1 + |rho.im|) * Real.exp (-|rho.im|) :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (Real.exp_pos _).le
    have hinvNonneg : 0 ≤ 1 / |rho.im| :=
      one_div_nonneg.mpr (abs_nonneg _)
    exact mul_nonneg (mul_nonneg hfront hinvNonneg)
      (Real.rpow_nonneg hY.le _)
  exact mul_le_mul hsecond hmoll (norm_nonneg _) hrightNonneg

/-- Analytic remainder after subtracting the crossed principal residue. -/
def principalPoleRemovedDetector
    (rho : ℂ) (U : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  dslope (principalDetectorNumerator rho U Y)
    (principalPoleLocation rho) z

theorem principalPoleLocation_mem_contourStrip
    {rho : ℂ} (hbetaHigh : rho.re ≤ 1) :
    principalPoleLocation rho ∈ contourStrip := by
  change -1 < (1 - rho).re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The pole-subtracted detector is analytic on the complete shifted
rectangle. -/
theorem analyticAt_principalPoleRemovedDetector
    {rho z : ℂ} {U : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hbetaHigh : rho.re ≤ 1) (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (principalPoleRemovedDetector rho U Y) z := by
  let A : ℂ → ℂ := principalDetectorNumerator rho U Y
  let z0 : ℂ := principalPoleLocation rho
  have hA0 : AnalyticAt ℂ A z0 :=
    analyticAt_principalDetectorNumerator hY
      (principalPoleLocation_mem_contourStrip hbetaHigh)
  have hAz : AnalyticAt ℂ A z :=
    analyticAt_principalDetectorNumerator hY hz
  by_cases heq : z = z0
  · subst z
    rcases hA0 with ⟨p, hp⟩
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hdiv : AnalyticAt ℂ (fun w => (A w - A z0) / (w - z0)) z := by
      exact (hAz.sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr heq)
    apply hdiv.congr
    filter_upwards [isOpen_ne.mem_nhds heq] with w hw
    rw [principalPoleRemovedDetector, dslope_of_ne]
    · simp [A, z0, slope, div_eq_inv_mul]
    · exact hw

/-- Exact identity: analytic remainder plus the displayed residue equals the
raw principal detector.  No pole is silently discarded. -/
theorem principalPoleRemoved_eq_raw_sub_residue
    {rho z : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : principalF rho = 0) (hz : z ≠ 0)
    (hpole : z ≠ principalPoleLocation rho) :
    principalPoleRemovedDetector rho U Y z =
      gammaMellinWeight Y z * riemannZeta (rho + z) *
          mollifier chiOne U (rho + z) -
        principalDetectorResidue rho U Y /
          (z - principalPoleLocation rho) := by
  have hsum : rho + z ≠ 1 := by
    intro h
    apply hpole
    unfold principalPoleLocation
    linear_combination h
  unfold principalPoleRemovedDetector
  rw [dslope_of_ne]
  · have hden : rho + z - 1 = z - principalPoleLocation rho := by
      unfold principalPoleLocation
      ring
    have hraw := principalDetectorNumerator_div_eq_raw
      (rho := rho) (z := z) (U := U) (Y := Y) hrho hz hsum
    rw [hden] at hraw
    unfold slope principalDetectorResidue
    simp only [vsub_eq_sub, smul_eq_mul, mul_sub]
    rw [show (z - principalPoleLocation rho)⁻¹ *
          principalDetectorNumerator rho U Y z =
        principalDetectorNumerator rho U Y z /
          (z - principalPoleLocation rho) by
            rw [div_eq_mul_inv, mul_comm],
      hraw]
    rw [show (z - principalPoleLocation rho)⁻¹ *
          principalDetectorNumerator rho U Y (principalPoleLocation rho) =
        principalDetectorNumerator rho U Y (principalPoleLocation rho) /
          (z - principalPoleLocation rho) by
            rw [div_eq_mul_inv, mul_comm]]
  · exact hpole

end
end MAPPrincipalZetaDetectorPoleRemoval

#print axioms MAPPrincipalZetaDetectorPoleRemoval.analyticAt_principalShiftedZeroQuotient
#print axioms MAPPrincipalZetaDetectorPoleRemoval.principalRegularized_one
#print axioms MAPPrincipalZetaDetectorPoleRemoval.principalShiftedZeroQuotient_at_pole
#print axioms MAPPrincipalZetaDetectorPoleRemoval.principalDetectorResidue_eq
#print axioms MAPPrincipalZetaDetectorPoleRemoval.norm_principalDetectorResidue_le
#print axioms MAPPrincipalZetaDetectorPoleRemoval.principalDetectorNumerator_div_eq_raw
#print axioms MAPPrincipalZetaDetectorPoleRemoval.analyticAt_principalPoleRemovedDetector
#print axioms MAPPrincipalZetaDetectorPoleRemoval.principalPoleRemoved_eq_raw_sub_residue
