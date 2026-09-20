import JutilaPrincipalDetectorPole
import JutilaLemma6FiniteContour
import FinitePoleRectangle
import PrincipalZetaDetectorPoleRemoval

/-!
# Exact one-pole contour displacement for the conductor-one Lemma 6 detector

The nonprincipal finite rectangle identity cannot be specialized to `χ = 1`:
the raw detector `Γ(z) ζ(ρ+z) X^z M(ρ+z)` has a simple pole at `z = 1-ρ`.
This module isolates that pole.  The holomorphic remainder is the divided
difference of the entire numerator built from `(s-1)ζ(s)`, and the residue is
the literal `principalDetectorPole` already bounded at high ordinate.

No infinite-height limit, Mellin identity, or selected-P53 estimate is
claimed here.
-/

namespace MAPJutilaPrincipalDetectorFinitePole

open Complex Real MeasureTheory Set Filter
open MAPJutilaLemma6FiniteContour
open MAPJutilaMEntire
open MAPJutilaPrincipalDetectorPole
open MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaPseudocharacterHarmonicLower
open MAPPrincipalZetaDetectorPoleRemoval
open MAPPrincipalZetaFixedStrip
open MAPAppendixA4Detector
open FinitePoleRectangle
open DirichletZeros

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Entire numerator of the conductor-one Lemma 6 detector after dividing out
the zero at `z = 0`.  The remaining singularity is the simple zeta pole
`z = 1-ρ`. -/
def principalLemmaSixNumerator (rho : ℂ) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (X : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (z + 1) * principalShiftedZeroQuotient rho z *
    (X : ℂ) ^ z * jutilaMWeightedSumComplex chiOne xi D S (rho + z)

def principalLemmaSixRemainder (rho : ℂ) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (X : ℝ) : ℂ → ℂ :=
  dslope (principalLemmaSixNumerator rho xi D S X) (principalPoleLocation rho)

/-- Residue of the raw conductor-one detector at `w = 1-ρ`. -/
def principalLemmaSixResidue (rho : ℂ) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (X : ℝ) : ℂ :=
  principalLemmaSixNumerator rho xi D S X (principalPoleLocation rho)

theorem riemannZeta_eq_zero_of_principalRegularized
    {rho : ℂ} (hrho : principalF rho = 0) (hrho1 : rho ≠ 1) :
    riemannZeta rho = 0 := by
  rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hrho1]
    at hrho
  exact (mul_eq_zero.mp hrho).resolve_left (sub_ne_zero.mpr hrho1)

theorem LFunction_chiOne_eq_zero_of_principalRegularized
    {rho : ℂ} (hrho : principalF rho = 0) (hrho1 : rho ≠ 1) :
    DirichletCharacter.LFunction chiOne rho = 0 := by
  simpa [DirichletCharacter.LFunction_modOne_eq] using
    riemannZeta_eq_zero_of_principalRegularized hrho hrho1

theorem principalRegularized_eq_zero_of_riemannZeta
    {rho : ℂ} (hrho : riemannZeta rho = 0) (hrho1 : rho ≠ 1) :
    principalF rho = 0 := by
  rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hrho1,
    hrho, mul_zero]

private theorem analyticAt_dslope_of_analyticAt
    {f : ℂ → ℂ} {p z : ℂ} (hp : AnalyticAt ℂ f p)
    (hz : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f p) z := by
  by_cases hzp : z = p
  · subst z
    rcases hp with ⟨P, hP⟩
    exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
  · have hdiv : AnalyticAt ℂ (fun w : ℂ => (f w - f p) / (w - p)) z :=
      hz.sub analyticAt_const |>.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hzp)
    apply hdiv.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne f hzp] with w hw
    rw [hw]
    simp only [slope, vsub_eq_sub, div_eq_inv_mul]
    ring

theorem analyticAt_principalLemmaSixNumerator
    {rho z : ℂ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 0 < X) (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (principalLemmaSixNumerator rho xi D S X) z := by
  unfold principalLemmaSixNumerator
  have hpow : Differentiable ℂ (fun w : ℂ => (X : ℂ) ^ w) :=
    differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hM : Differentiable ℂ (fun w : ℂ =>
      jutilaMWeightedSumComplex chiOne xi D S (rho + w)) :=
    (differentiable_jutilaMWeightedSumComplex chiOne xi hDpos S).comp
      (by fun_prop)
  exact ((((analyticAt_Gamma_add_one_of_mem_contourStrip hz).mul
    (analyticAt_principalShiftedZeroQuotient rho z)).mul
      (hpow.analyticAt z)).mul (hM.analyticAt z))

theorem analyticAt_principalLemmaSixRemainder
    {rho z : ℂ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 0 < X) (hbetaHigh : rho.re ≤ 1)
    (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (principalLemmaSixRemainder rho xi D S X) z := by
  unfold principalLemmaSixRemainder
  apply analyticAt_dslope_of_analyticAt
  · exact analyticAt_principalLemmaSixNumerator xi hDpos S hX
      (principalPoleLocation_mem_contourStrip hbetaHigh)
  · exact analyticAt_principalLemmaSixNumerator xi hDpos S hX hz

/-- The residue retains the canonical mollifier and is exactly the quantity
already bounded in `JutilaPrincipalDetectorPole`. -/
theorem principalLemmaSixResidue_eq
    {rho : ℂ} (xi : ℕ → ℂ) (D S : Finset ℕ) {X : ℝ}
    (hrho : principalF rho = 0) (hrho1 : rho ≠ 1) :
    principalLemmaSixResidue rho xi D S X =
      Complex.Gamma (1 - rho) * (X : ℂ) ^ (1 - rho) *
        jutilaMWeightedSumComplex chiOne xi D S 1 := by
  have hz : (1 - rho : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hrho1)
  have hG : Complex.Gamma ((1 - rho) + 1) =
      (1 - rho) * Complex.Gamma (1 - rho) :=
    Complex.Gamma_add_one (1 - rho) hz
  unfold principalLemmaSixResidue principalLemmaSixNumerator
  rw [principalShiftedZeroQuotient_at_pole hrho hrho1]
  simp only [principalPoleLocation]
  have harg : rho + (1 - rho) = 1 := by ring
  rw [harg, hG]
  field_simp [hz]

theorem principalLemmaSixResidue_eq_principalDetectorPole
    {rho : ℂ} {X z1 z2 : ℝ} (R : ℕ)
    (hrho : principalF rho = 0) (hrho1 : rho ≠ 1) :
    principalLemmaSixResidue rho (jutilaLambdaComplex z1 z2)
        (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) X =
      principalDetectorPole rho X z1 z2 R := by
  rw [principalLemmaSixResidue_eq (jutilaLambdaComplex z1 z2)
    (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) hrho hrho1]
  unfold principalDetectorPole
  ring

/-- Away from `z = 0` and the crossed pole, the literal Lemma 6 extension is
the holomorphic remainder plus the displayed principal part. -/
theorem principalLemmaSixIntegrand_eq_remainder_add_residue
    {rho z : ℂ} (xi : ℕ → ℂ) (D S : Finset ℕ) (X : ℝ)
    (hrho : principalF rho = 0) (hrho1 : rho ≠ 1)
    (hz0 : z ≠ 0) (hpole : z ≠ principalPoleLocation rho) :
    jutilaDetectorExtension chiOne rho xi D S X z =
      principalLemmaSixRemainder rho xi D S X z +
        principalLemmaSixResidue rho xi D S X *
          (z - principalPoleLocation rho)⁻¹ := by
  have hsum : rho + z ≠ 1 := by
    intro h
    apply hpole
    unfold principalPoleLocation
    linear_combination h
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  have hden : z - principalPoleLocation rho ≠ 0 :=
    sub_ne_zero.mpr hpole
  have hnum :
      principalLemmaSixNumerator rho xi D S X z =
        (z - principalPoleLocation rho) *
          jutilaDetectorExtension chiOne rho xi D S X z := by
    have hraw := jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz0
    have hquot := principalShiftedZeroQuotient_eq_div hrho hz0
    have hreg :=
      MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hsum
    have hG := Complex.Gamma_add_one z hz0
    have hL : DirichletCharacter.LFunction chiOne (rho + z) =
        riemannZeta (rho + z) := by
      simp [DirichletCharacter.LFunction_modOne_eq]
    have hdisp : rho + z - 1 = z - principalPoleLocation rho := by
      unfold principalPoleLocation
      ring
    unfold principalLemmaSixNumerator
    rw [hquot, hreg, hG, hraw, hL, hdisp]
    field_simp [hz0, hden]
  have hds : principalLemmaSixRemainder rho xi D S X z =
      (principalLemmaSixNumerator rho xi D S X z -
        principalLemmaSixNumerator rho xi D S X
          (principalPoleLocation rho)) /
        (z - principalPoleLocation rho) := by
    rw [principalLemmaSixRemainder, dslope_of_ne]
    · simp only [slope, vsub_eq_sub, div_eq_inv_mul]
      ring
    · exact hpole
  rw [hds, principalLemmaSixResidue, hnum]
  field_simp [hden]
  ring

/-- Exact finite rectangle shift across the sole conductor-one pole
`w = 1-ρ`. -/
theorem rectangleBoundaryIntegral_principalLemmaSix_eq_residue
    {rho : ℂ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X a b u v r : ℝ} (hX : 0 < X) (hrho : principalF rho = 0)
    (hrho1 : rho ≠ 1) (hbetaHigh : rho.re ≤ 1)
    (hr : 0 < r) (haStrip : -1 < a)
    (hleft : a < (principalPoleLocation rho).re - r)
    (hright : (principalPoleLocation rho).re + r < b)
    (hbottom : u < (principalPoleLocation rho).im - r)
    (htop : (principalPoleLocation rho).im + r < v)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    rectangleBoundaryIntegral
        (jutilaDetectorExtension chiOne rho xi D S X) a b u v =
      (2 * Real.pi * Complex.I) *
        principalLemmaSixResidue rho xi D S X := by
  let p : Unit → ℂ := fun _ => principalPoleLocation rho
  let R : Unit → ℂ := fun _ => principalLemmaSixResidue rho xi D S X
  let rad : Unit → ℝ := fun _ => r
  let g := principalLemmaSixRemainder rho xi D S X
  have hab : a ≤ b := by linarith
  have huv : u ≤ v := by linarith
  have hleft' : a < 1 - rho.re - r := by
    simpa [principalPoleLocation] using hleft
  have hright' : 1 - rho.re + r < b := by
    simpa [principalPoleLocation] using hright
  have hbottom' : u < -rho.im - r := by
    simpa [principalPoleLocation] using hbottom
  have htop' : -rho.im + r < v := by
    simpa [principalPoleLocation] using htop
  have hgdiff : DifferentiableOn ℂ g
      (Set.uIcc a b ×ℂ Set.uIcc u v) := by
    intro z hz
    have hzre : a ≤ z.re := by
      have h := hz.1.1
      rw [min_eq_left hab] at h
      exact h
    exact (analyticAt_principalLemmaSixRemainder xi hDpos S hX hbetaHigh
      (show z ∈ contourStrip from haStrip.trans_le hzre)).differentiableAt
      |>.differentiableWithinAt
  have hedge (z : ℂ) (hz0 : z ≠ 0)
      (hzp : z ≠ principalPoleLocation rho) :
      jutilaDetectorExtension chiOne rho xi D S X z =
        g z + principalLemmaSixResidue rho xi D S X *
          (z - principalPoleLocation rho)⁻¹ :=
    principalLemmaSixIntegrand_eq_remainder_add_residue xi D S X
      hrho hrho1 hz0 hzp
  have hsum : (∑ i ∈ ({()} : Finset Unit), R i) =
      principalLemmaSixResidue rho xi D S X := by simp [R]
  rw [← hsum]
  apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    ({()} : Finset Unit) p R rad
    (jutilaDetectorExtension chiOne rho xi D S X) g a b u v
  · intro i hi; simpa [rad] using hr
  · intro i hi; simpa [p, rad] using hleft
  · intro i hi; simpa [p, rad] using hright
  · intro i hi; simpa [p, rad] using hbottom
  · intro i hi; simpa [p, rad] using htop
  · exact boundaryIntervalIntegrable_of_differentiableOn hgdiff
  · exact hgdiff
  · intro x
    have hzp : (x : ℂ) + (u : ℂ) * I ≠ principalPoleLocation rho := by
      intro h
      have him := congrArg Complex.im h
      simp [principalPoleLocation] at him
      linarith [hbottom']
    have hz0 : (x : ℂ) + (u : ℂ) * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact hu0 him
    simpa [p, R, g] using hedge ((x : ℂ) + (u : ℂ) * I) hz0 hzp
  · intro x
    have hzp : (x : ℂ) + (v : ℂ) * I ≠ principalPoleLocation rho := by
      intro h
      have him := congrArg Complex.im h
      simp [principalPoleLocation] at him
      linarith [htop']
    have hz0 : (x : ℂ) + (v : ℂ) * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact hv0 him
    simpa [p, R, g] using hedge ((x : ℂ) + (v : ℂ) * I) hz0 hzp
  · intro y
    have hzp : (b : ℂ) + (y : ℂ) * I ≠ principalPoleLocation rho := by
      intro h
      have hre := congrArg Complex.re h
      simp [principalPoleLocation] at hre
      linarith [hright']
    have hz0 : (b : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact hb0 hre
    simpa [p, R, g] using hedge ((b : ℂ) + (y : ℂ) * I) hz0 hzp
  · intro y
    have hzp : (a : ℂ) + (y : ℂ) * I ≠ principalPoleLocation rho := by
      intro h
      have hre := congrArg Complex.re h
      simp [principalPoleLocation] at hre
      linarith [hleft']
    have hz0 : (a : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact ha0 hre
    simpa [p, R, g] using hedge ((a : ℂ) + (y : ℂ) * I) hz0 hzp

/-- Solved finite-line form.  Both horizontal edges and the exact residue
remain visible.  The residue is `principalDetectorPole` for the canonical
mollifier. -/
theorem principalLemmaSix_right_eq_left_add_horizontals_add_residue
    {rho : ℂ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X a b u v r : ℝ} (hX : 0 < X) (hrho : principalF rho = 0)
    (hrho1 : rho ≠ 1) (hbetaHigh : rho.re ≤ 1)
    (hr : 0 < r) (haStrip : -1 < a)
    (hleft : a < (principalPoleLocation rho).re - r)
    (hright : (principalPoleLocation rho).re + r < b)
    (hbottom : u < (principalPoleLocation rho).im - r)
    (htop : (principalPoleLocation rho).im + r < v)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    (∫ y : ℝ in u..v,
        jutilaDetectorExtension chiOne rho xi D S X (b + y * I)) =
      (∫ y : ℝ in u..v,
        jutilaDetectorExtension chiOne rho xi D S X (a + y * I)) +
      I * ((∫ x : ℝ in a..b,
        jutilaDetectorExtension chiOne rho xi D S X (x + u * I)) -
        (∫ x : ℝ in a..b,
          jutilaDetectorExtension chiOne rho xi D S X (x + v * I))) +
      (2 * Real.pi : ℂ) * principalLemmaSixResidue rho xi D S X := by
  have hrect := rectangleBoundaryIntegral_principalLemmaSix_eq_residue
    xi hDpos S hX hrho hrho1 hbetaHigh hr haStrip hleft hright hbottom htop
    ha0 hb0 hu0 hv0
  unfold rectangleBoundaryIntegral at hrect
  have hh := congrArg (fun z : ℂ => (-I) * z) hrect
  simp [mul_add, mul_sub, ← mul_assoc, Complex.I_mul_I] at hh
  have hres :
      -(I * 2 * (Real.pi : ℂ) * I *
          principalLemmaSixResidue rho xi D S X) =
        (2 * Real.pi : ℂ) * principalLemmaSixResidue rho xi D S X := by
    calc
      _ = -((I * I) * ((2 * Real.pi : ℂ) *
          principalLemmaSixResidue rho xi D S X)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hres] at hh
  linear_combination hh

/-- Source-shaped finite displacement: left line at `Re = -β`, right line at
`Re = 1`, with the canonical residue. -/
theorem principalLemmaSix_sourceRectangle_eq_residue
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X B : ℝ} (hX : 0 < X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0)
    (hB : |t| + 1 ≤ B) :
    (∫ y : ℝ in -B..B,
        jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          xi D S X ((1 : ℂ) + y * I)) =
      (∫ y : ℝ in -B..B,
        jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          xi D S X (((-beta : ℝ) : ℂ) + y * I)) +
      I * ((∫ x : ℝ in -beta..1,
        jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          xi D S X (x + (-B) * I)) -
        (∫ x : ℝ in -beta..1,
          jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
            xi D S X (x + B * I))) +
      (2 * Real.pi : ℂ) *
        principalLemmaSixResidue (lemmaSixZeroPoint beta t) xi D S X := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hre : rho.re = beta := by simp [rho, lemmaSixZeroPoint]
  have him : rho.im = t := by simp [rho, lemmaSixZeroPoint]
  have hpRe : (principalPoleLocation rho).re = 1 - beta := by
    simp [principalPoleLocation, hre]
  have hpIm : (principalPoleLocation rho).im = -t := by
    simp [principalPoleLocation, him]
  have hr : (0 : ℝ) < (1 / 8 : ℝ) := by norm_num
  have haStrip : -1 < (-beta : ℝ) := by linarith
  have hleft : (-beta : ℝ) < (principalPoleLocation rho).re - (1 / 8 : ℝ) := by
    rw [hpRe]
    linarith
  have hright : (principalPoleLocation rho).re + (1 / 8 : ℝ) < (1 : ℝ) := by
    rw [hpRe]
    linarith
  have hbottom : -B < (principalPoleLocation rho).im - (1 / 8 : ℝ) := by
    rw [hpIm]
    have := le_abs_self t
    linarith
  have htop : (principalPoleLocation rho).im + (1 / 8 : ℝ) < B := by
    rw [hpIm]
    have := neg_le_abs t
    linarith
  have hbetaHigh : rho.re ≤ 1 := by rw [hre]; linarith
  have ha0 : (-beta : ℝ) ≠ 0 := by linarith
  have hb0 : (1 : ℝ) ≠ 0 := by norm_num
  have hu0 : (-B : ℝ) ≠ 0 := by linarith
  have hv0 : (B : ℝ) ≠ 0 := by linarith
  simpa [rho, Complex.ofReal_neg] using
    principalLemmaSix_right_eq_left_add_horizontals_add_residue
      (rho := rho) xi hDpos S hX hrho hrho1 hbetaHigh hr haStrip
      hleft hright hbottom htop ha0 hb0 hu0 hv0

end

end MAPJutilaPrincipalDetectorFinitePole

#print axioms MAPJutilaPrincipalDetectorFinitePole.principalLemmaSixResidue_eq
#print axioms MAPJutilaPrincipalDetectorFinitePole.principalLemmaSixResidue_eq_principalDetectorPole
#print axioms MAPJutilaPrincipalDetectorFinitePole.principalLemmaSixIntegrand_eq_remainder_add_residue
#print axioms MAPJutilaPrincipalDetectorFinitePole.rectangleBoundaryIntegral_principalLemmaSix_eq_residue
#print axioms MAPJutilaPrincipalDetectorFinitePole.principalLemmaSix_right_eq_left_add_horizontals_add_residue
#print axioms MAPJutilaPrincipalDetectorFinitePole.principalLemmaSix_sourceRectangle_eq_residue
