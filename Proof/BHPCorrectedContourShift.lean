import BHPShiftedRamachandraWeld
import AppendixA4Detector
import FinitePoleRectangle

/-!
# The source-faithful BHP Perron rectangle

Baker--Harman--Pintz Lemma 9 starts from

`L(1/2+it+w,chi) * N^w / w`.

The printed quantity following (3.36) omits `/w` after moving the left edge
onto `Re w = 0`.  This file keeps `/w` and stops at `Re w = delta > 0`.
For a nonprincipal character the resulting rectangle is holomorphic, so the
right edge is exactly the corrected left edge minus the two oriented
horizontal edges.  The principal character is deliberately not folded into
this theorem: its translated pole at `w = 1/2-it` requires a separate residue
calculation.
-/

namespace MAPBHPCorrectedContourShift

set_option maxHeartbeats 800000

open Complex MeasureTheory Set
open MAPBHPCorrectedPerronKernel
open MAPAppendixA4Detector
open DirichletZeros
open FinitePoleRectangle

noncomputable section

/-- Literal BHP integrand before any contour movement. -/
def bhpPerronIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X t : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction chi
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) + w) *
    Complex.exp (w * Real.log X) / w

/-- Normalized upward vertical edge `Re w = a`. -/
def bhpVerticalLineIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X t a H : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ u in (-H)..H,
      bhpPerronIntegrand chi X t ((a : ℂ) + Complex.I * u)

/-- Normalized sum of the positively oriented top and bottom edges.  Both
real integrals are parameterized from the left edge to the right edge. -/
def bhpHorizontalBoundaryIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q)
    (X t delta c H : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I) *
      (∫ x in delta..c,
        bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * H)) -
    ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I) *
      (∫ x in delta..c,
        bhpPerronIntegrand chi X t ((x : ℂ) - Complex.I * H))

/-- On a nonprincipal character, the literal `/w` integrand is analytic on
every positive-offset rectangle. -/
theorem analyticAt_bhpPerronIntegrand_of_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {X t delta c H : ℝ} (hX : 0 < X)
    (hdelta : 0 < delta) (hdc : delta ≤ c)
    {w : ℂ}
    (hw : w ∈ Set.uIcc delta c ×ℂ Set.uIcc (-H) H) :
    AnalyticAt ℂ (bhpPerronIntegrand chi X t) w := by
  have hwre : delta ≤ w.re := by
    have hleft := hw.1.1
    rw [min_eq_left hdc] at hleft
    exact hleft
  have hw0 : w ≠ 0 := by
    intro heq
    subst w
    simp at hwre
    linarith
  unfold bhpPerronIntegrand
  have hL : AnalyticAt ℂ
      (fun z : ℂ => DirichletCharacter.LFunction chi
        ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) + z)) w :=
    ((DirichletCharacter.differentiable_LFunction hchi).analyticAt _).comp
      (by fun_prop)
  have hpow : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (z * Real.log X)) w := by
    fun_prop
  exact (hL.mul hpow).div (by fun_prop) hw0

/-- Exact finite rectangle identity for the corrected nonprincipal contour.
No norm estimate, Perron approximation, or Rademacher bound is used. -/
theorem bhpVerticalLineIntegral_eq_shifted_sub_horizontal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {X t delta c H : ℝ} (hX : 0 < X)
    (hdelta : 0 < delta) (hdc : delta ≤ c) (hH : 0 ≤ H) :
    bhpVerticalLineIntegral chi X t c H =
      bhpVerticalLineIntegral chi X t delta H -
        bhpHorizontalBoundaryIntegral chi X t delta c H := by
  have hrect := finite_rectangle_balance
    (bhpPerronIntegrand chi X t) hdc hH
      (fun w hw => analyticAt_bhpPerronIntegrand_of_nonprincipal
        chi hchi hX hdelta hdc hw)
  have hrect' :
      (∫ x : ℝ in delta..c,
          bhpPerronIntegrand chi X t ((x : ℂ) - Complex.I * H)) -
        (∫ x : ℝ in delta..c,
          bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * H)) +
        Complex.I * (∫ u : ℝ in (-H)..H,
          bhpPerronIntegrand chi X t ((c : ℂ) + Complex.I * u)) -
        Complex.I * (∫ u : ℝ in (-H)..H,
          bhpPerronIntegrand chi X t ((delta : ℂ) + Complex.I * u)) = 0 := by
    simpa [mul_comm] using hrect
  unfold bhpVerticalLineIntegral bhpHorizontalBoundaryIntegral
  have hraw :
      (∫ u : ℝ in (-H)..H,
          bhpPerronIntegrand chi X t ((c : ℂ) + Complex.I * u)) =
        (∫ u : ℝ in (-H)..H,
          bhpPerronIntegrand chi X t ((delta : ℂ) + Complex.I * u)) -
        Complex.I * (∫ x : ℝ in delta..c,
          bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * H)) +
        Complex.I * (∫ x : ℝ in delta..c,
          bhpPerronIntegrand chi X t ((x : ℂ) - Complex.I * H)) := by
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    simp [mul_sub, mul_add, ← mul_assoc, Complex.I_mul_I]
    linear_combination hrect'
  rw [hraw]
  ring

/-- The positive-offset vertical edge is exactly the already bounded
`shiftedLeftLineIntegral`; in particular the retained `/w` is not a new or
weaker object hidden by notation. -/
theorem bhpVerticalLineIntegral_eq_shiftedLeftLineIntegral
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X t delta H : ℝ} (hX : 0 < X) :
    bhpVerticalLineIntegral chi X t delta H =
      shiftedLeftLineIntegral chi X delta H t := by
  unfold bhpVerticalLineIntegral shiftedLeftLineIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  unfold bhpPerronIntegrand shiftedLeftLineIntegrand
  rw [PerronKernel.verticalPower_eq_exp hX]
  have harg :
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
          ((delta : ℂ) + Complex.I * u)) =
        ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) +
          (t + u) * Complex.I) := by
    push_cast
    ring
  dsimp only
  rw [harg]

/-- Source-faithful nonprincipal contour shift with the corrected left edge
spelled in the form consumed by the shifted Holder theorem. -/
theorem bhpRightLine_eq_correctedLeft_sub_horizontal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {X t delta c H : ℝ} (hX : 0 < X)
    (hdelta : 0 < delta) (hdc : delta ≤ c) (hH : 0 ≤ H) :
    bhpVerticalLineIntegral chi X t c H =
      shiftedLeftLineIntegral chi X delta H t -
        bhpHorizontalBoundaryIntegral chi X t delta c H := by
  rw [bhpVerticalLineIntegral_eq_shifted_sub_horizontal
    chi hchi hX hdelta hdc hH]
  rw [bhpVerticalLineIntegral_eq_shiftedLeftLineIntegral chi hX]

/-! ## Principal character: exact translated-pole residue -/

/-- Location of the translated pole `1/2 + it + w = 1`. -/
def bhpPrincipalPole (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) - t * Complex.I

/-- Entire principal L-function factor, with the harmless Perron pole `w=0`
still excluded by the positive-offset rectangle. -/
def bhpPrincipalNumerator (q : ℕ) [NeZero q]
    (X t : ℝ) (w : ℂ) : ℂ :=
  regularizedLFunction (1 : DirichletCharacter ℂ q)
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) + w) *
    Complex.exp (w * Real.log X) / w

/-- The actual residue.  For a principal character modulo a nontrivial
modulus this retains the correct Euler-factor residue; it is not silently
replaced by the indicator `delta_chi`. -/
def bhpPrincipalResidue (q : ℕ) [NeZero q]
    (X t : ℝ) : ℂ :=
  bhpPrincipalNumerator q X t (bhpPrincipalPole t)

/-- Holomorphic remainder after subtracting the translated principal pole. -/
def bhpPrincipalRemainder (q : ℕ) [NeZero q]
    (X t : ℝ) : ℂ → ℂ :=
  dslope (bhpPrincipalNumerator q X t) (bhpPrincipalPole t)

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

theorem analyticAt_bhpPrincipalNumerator_of_pos_re
    {q : ℕ} [NeZero q] {X t : ℝ} {w : ℂ}
    (hw : 0 < w.re) :
    AnalyticAt ℂ (bhpPrincipalNumerator q X t) w := by
  have hw0 : w ≠ 0 := by
    intro heq
    subst w
    simp at hw
  unfold bhpPrincipalNumerator
  have hL : AnalyticAt ℂ
      (fun z : ℂ => regularizedLFunction (1 : DirichletCharacter ℂ q)
        ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) + z)) w :=
    ((differentiable_regularizedLFunction
      (1 : DirichletCharacter ℂ q)).analyticAt _).comp (by fun_prop)
  have hpow : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (z * Real.log X)) w := by fun_prop
  exact (hL.mul hpow).div (by fun_prop) hw0

theorem analyticAt_bhpPrincipalRemainder_of_pos_re
    {q : ℕ} [NeZero q] {X t : ℝ} {w : ℂ}
    (hw : 0 < w.re) :
    AnalyticAt ℂ (bhpPrincipalRemainder q X t) w := by
  unfold bhpPrincipalRemainder
  apply analyticAt_dslope_of_analyticAt
  · apply analyticAt_bhpPrincipalNumerator_of_pos_re
    simp [bhpPrincipalPole]
  · exact analyticAt_bhpPrincipalNumerator_of_pos_re hw

/-- Away from the translated pole, the literal principal-character BHP
integrand is the holomorphic remainder plus its exact principal part. -/
theorem bhpPrincipalIntegrand_eq_remainder_add_residue
    {q : ℕ} [NeZero q] {X t : ℝ} {w : ℂ}
    (hw0 : w ≠ 0) (hwp : w ≠ bhpPrincipalPole t) :
    bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t w =
      bhpPrincipalRemainder q X t w +
        bhpPrincipalResidue q X t * (w - bhpPrincipalPole t)⁻¹ := by
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) + t * Complex.I) + w
  have hsform : s - 1 = w - bhpPrincipalPole t := by
    dsimp [s, bhpPrincipalPole]
    push_cast
    ring
  have hs1 : s ≠ 1 := by
    intro hs
    apply hwp
    apply sub_eq_zero.mp
    rw [← hsform, hs, sub_self]
  have hreg :
      regularizedLFunction (1 : DirichletCharacter ℂ q) s =
        (s - 1) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) s := by
    simp only [regularizedLFunction, if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hs1]
  have hden : w - bhpPrincipalPole t ≠ 0 := sub_ne_zero.mpr hwp
  have hraw :
      bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t w =
        bhpPrincipalNumerator q X t w /
          (w - bhpPrincipalPole t) := by
    unfold bhpPerronIntegrand bhpPrincipalNumerator
    change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
        Complex.exp (w * Real.log X) / w = _
    rw [show regularizedLFunction (1 : DirichletCharacter ℂ q)
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) + w) =
        regularizedLFunction (1 : DirichletCharacter ℂ q) s by rfl]
    rw [hreg, hsform]
    field_simp [hw0, hden]
  have hds : bhpPrincipalRemainder q X t w =
      (bhpPrincipalNumerator q X t w -
        bhpPrincipalNumerator q X t (bhpPrincipalPole t)) /
          (w - bhpPrincipalPole t) := by
    rw [bhpPrincipalRemainder, dslope_of_ne]
    · simp only [slope, vsub_eq_sub, div_eq_inv_mul]
      ring
    · exact hwp
  rw [hraw, hds]
  unfold bhpPrincipalResidue
  field_simp [hden]
  ring

/-- Exact finite principal rectangle, with the sole translated L-pole and its
true residue.  The radius hypotheses say that the excision square lies
strictly inside the positive-offset rectangle. -/
theorem rectangleBoundaryIntegral_bhpPrincipal_eq_residue
    {q : ℕ} [NeZero q] {X t delta c H r : ℝ}
    (hdelta : 0 < delta) (hdc : delta ≤ c)
    (hr : 0 < r)
    (hleft : delta < (bhpPrincipalPole t).re - r)
    (hright : (bhpPrincipalPole t).re + r < c)
    (hbottom : -H < (bhpPrincipalPole t).im - r)
    (htop : (bhpPrincipalPole t).im + r < H) :
    rectangleBoundaryIntegral
        (bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t)
        delta c (-H) H =
      (2 * Real.pi * Complex.I) * bhpPrincipalResidue q X t := by
  let p : Unit → ℂ := fun _ => bhpPrincipalPole t
  let R : Unit → ℂ := fun _ => bhpPrincipalResidue q X t
  let rad : Unit → ℝ := fun _ => r
  let g := bhpPrincipalRemainder q X t
  have hgdiff : DifferentiableOn ℂ g
      (Set.uIcc delta c ×ℂ Set.uIcc (-H) H) := by
    intro z hz
    have hzre : delta ≤ z.re := by
      have h := hz.1.1
      rw [min_eq_left hdc] at h
      exact h
    exact (analyticAt_bhpPrincipalRemainder_of_pos_re
      (hdelta.trans_le hzre)).differentiableAt.differentiableWithinAt
  have hedge (z : ℂ) (hz0 : z ≠ 0)
      (hzp : z ≠ bhpPrincipalPole t) :
      bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t z =
        g z + bhpPrincipalResidue q X t *
          (z - bhpPrincipalPole t)⁻¹ := by
    apply bhpPrincipalIntegrand_eq_remainder_add_residue
    · exact hz0
    · exact hzp
  have hleft' : delta < (1 / 2 : ℝ) - r := by
    simpa [bhpPrincipalPole] using hleft
  have hright' : (1 / 2 : ℝ) + r < c := by
    simpa [bhpPrincipalPole] using hright
  have hbottom' : -H < -t - r := by
    simpa [bhpPrincipalPole] using hbottom
  have htop' : -t + r < H := by
    simpa [bhpPrincipalPole] using htop
  have hHpos : 0 < H := by
    linarith
  have hsum : (∑ i ∈ ({()} : Finset Unit), R i) =
      bhpPrincipalResidue q X t := by simp [R]
  rw [← hsum]
  apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    ({()} : Finset Unit) p R rad
    (bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t) g
    delta c (-H) H
  · intro i hi; simpa [rad] using hr
  · intro i hi; simpa [p, rad] using hleft
  · intro i hi; simpa [p, rad] using hright
  · intro i hi; simpa [p, rad] using hbottom
  · intro i hi; simpa [p, rad] using htop
  · exact boundaryIntervalIntegrable_of_differentiableOn hgdiff
  · exact hgdiff
  · intro x
    have hz0 : (x : ℂ) + (-H : ℂ) * Complex.I ≠ 0 := by
      intro hz
      have him := congrArg Complex.im hz
      simp at him
      linarith
    have hzp : (x : ℂ) + (-H : ℂ) * Complex.I ≠
        bhpPrincipalPole t := by
      intro hpole
      have him := congrArg Complex.im hpole
      simp [bhpPrincipalPole] at him
      linarith [hbottom']
    simpa [p, R, g] using hedge
      ((x : ℂ) + (-H : ℂ) * Complex.I) hz0 hzp
  · intro x
    have hz0 : (x : ℂ) + (H : ℂ) * Complex.I ≠ 0 := by
      intro hz
      have him := congrArg Complex.im hz
      simp at him
      linarith
    have hzp : (x : ℂ) + (H : ℂ) * Complex.I ≠
        bhpPrincipalPole t := by
      intro hpole
      have him := congrArg Complex.im hpole
      simp [bhpPrincipalPole] at him
      linarith [htop']
    simpa [p, R, g] using hedge
      ((x : ℂ) + (H : ℂ) * Complex.I) hz0 hzp
  · intro y
    have hcpos : 0 < c := hdelta.trans_le hdc
    have hz0 : (c : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      simp at hre
      linarith
    have hzp : (c : ℂ) + (y : ℂ) * Complex.I ≠
        bhpPrincipalPole t := by
      intro hpole
      have hre := congrArg Complex.re hpole
      simp [bhpPrincipalPole] at hre
      linarith [hright']
    simpa [p, R, g] using hedge
      ((c : ℂ) + (y : ℂ) * Complex.I) hz0 hzp
  · intro y
    have hz0 : (delta : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      simp at hre
      linarith
    have hzp : (delta : ℂ) + (y : ℂ) * Complex.I ≠
        bhpPrincipalPole t := by
      intro hpole
      have hre := congrArg Complex.re hpole
      simp [bhpPrincipalPole] at hre
      linarith [hleft']
    simpa [p, R, g] using hedge
      ((delta : ℂ) + (y : ℂ) * Complex.I) hz0 hzp

/-- Normalized principal contour shift.  This is the exact analogue of the
nonprincipal identity, now with the true translated-pole residue added. -/
theorem bhpPrincipalRightLine_eq_correctedLeft_sub_horizontal_add_residue
    {q : ℕ} [NeZero q] {X t delta c H r : ℝ}
    (hX : 0 < X) (hdelta : 0 < delta) (hdc : delta ≤ c)
    (hr : 0 < r)
    (hleft : delta < (bhpPrincipalPole t).re - r)
    (hright : (bhpPrincipalPole t).re + r < c)
    (hbottom : -H < (bhpPrincipalPole t).im - r)
    (htop : (bhpPrincipalPole t).im + r < H) :
    bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) X t c H =
      shiftedLeftLineIntegral (1 : DirichletCharacter ℂ q)
          X delta H t -
        bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
          X t delta c H +
        bhpPrincipalResidue q X t := by
  have hrect := rectangleBoundaryIntegral_bhpPrincipal_eq_residue
    (q := q) (X := X) (t := t) (delta := delta) (c := c)
      (H := H) (r := r) hdelta hdc hr hleft hright hbottom htop
  have hraw :
      (∫ u : ℝ in (-H)..H,
          bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
            ((c : ℂ) + Complex.I * u)) =
        (∫ u : ℝ in (-H)..H,
          bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
            ((delta : ℂ) + Complex.I * u)) -
        Complex.I * (∫ x : ℝ in delta..c,
          bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
            ((x : ℂ) + Complex.I * H)) +
        Complex.I * (∫ x : ℝ in delta..c,
          bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
            ((x : ℂ) - Complex.I * H)) +
        (2 * Real.pi : ℝ) * bhpPrincipalResidue q X t := by
    unfold rectangleBoundaryIntegral at hrect
    have hrect' :
        (∫ x : ℝ in delta..c,
            bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
              ((x : ℂ) - Complex.I * H)) -
          (∫ x : ℝ in delta..c,
            bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
              ((x : ℂ) + Complex.I * H)) +
          Complex.I * (∫ u : ℝ in (-H)..H,
            bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
              ((c : ℂ) + Complex.I * u)) -
          Complex.I * (∫ u : ℝ in (-H)..H,
            bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
              ((delta : ℂ) + Complex.I * u)) =
          (2 * Real.pi * Complex.I) * bhpPrincipalResidue q X t := by
      simpa [mul_comm] using hrect
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    simp [mul_sub, mul_add, ← mul_assoc, Complex.I_mul_I]
    linear_combination hrect'
  rw [← bhpVerticalLineIntegral_eq_shiftedLeftLineIntegral
    (1 : DirichletCharacter ℂ q) hX]
  unfold bhpVerticalLineIntegral bhpHorizontalBoundaryIntegral
  rw [hraw]
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  field_simp [hpi]
  ring

end
end MAPBHPCorrectedContourShift

#print axioms MAPBHPCorrectedContourShift.analyticAt_bhpPerronIntegrand_of_nonprincipal
#print axioms MAPBHPCorrectedContourShift.bhpVerticalLineIntegral_eq_shifted_sub_horizontal
#print axioms MAPBHPCorrectedContourShift.bhpVerticalLineIntegral_eq_shiftedLeftLineIntegral
#print axioms MAPBHPCorrectedContourShift.bhpRightLine_eq_correctedLeft_sub_horizontal
#print axioms MAPBHPCorrectedContourShift.bhpPrincipalIntegrand_eq_remainder_add_residue
#print axioms MAPBHPCorrectedContourShift.rectangleBoundaryIntegral_bhpPrincipal_eq_residue
#print axioms MAPBHPCorrectedContourShift.bhpPrincipalRightLine_eq_correctedLeft_sub_horizontal_add_residue
