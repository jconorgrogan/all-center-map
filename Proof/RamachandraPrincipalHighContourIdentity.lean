import RamachandraShiftedNonprincipalContourIdentity
import PrincipalZetaPoleContour
import PrincipalZetaFixedStrip

/-!
# Principal high-range contour in shifted Ramachandra Lemma 3

The conductor-one primitive character introduces a translated double zeta
pole in addition to the Gamma pole at zero.  This module keeps that pole and
its residue explicit.
-/

namespace RamachandraPrincipalHighContourIdentity

open Complex MeasureTheory Set Filter
open scoped BigOperators LSeries.notation Interval Topology
open FinitePoleRectangle
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraShiftedGammaPoleContour
open MAPGoldfeldSiegel

noncomputable section

set_option maxHeartbeats 800000

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- The boundary integral of a double principal part is zero.  Unlike a
simple pole, `(z-p)^{-2}` has the single-valued primitive `-(z-p)^{-1}`;
the four endpoint contributions cancel exactly. -/
theorem rectangleBoundaryIntegral_sub_inv_sq_eq_zero
    (p : ℂ) {a b u v : ℝ}
    (ha : a ≠ p.re) (hb : b ≠ p.re)
    (hu : u ≠ p.im) (hv : v ≠ p.im) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹ ^ 2)
      a b u v = 0 := by
  let g : ℂ → ℂ := fun z => (z - p)⁻¹
  have horizontal_deriv (y x : ℝ) (hy : y ≠ p.im) :
      HasDerivAt (fun r : ℝ => g ((r : ℂ) + (y : ℂ) * I))
        (-((((x : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) x := by
    let e : ℂ → ℂ := fun z => g (z + (y : ℂ) * I)
    have hden : ((x : ℂ) + (y : ℂ) * I) - p ≠ 0 := by
      intro h
      apply hy
      have him := congrArg Complex.im h
      exact sub_eq_zero.mp (by simpa using him)
    have he : HasDerivAt e
        (-((((x : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) (x : ℂ) := by
      dsimp [e, g]
      simpa [div_eq_mul_inv, inv_pow] using!
        (((hasDerivAt_id (x : ℂ)).add_const
          ((y : ℂ) * I)).sub_const p).inv hden
    simpa [e, g] using he.comp_ofReal
  have vertical_deriv (x y : ℝ) (hx : x ≠ p.re) :
      HasDerivAt (fun r : ℝ => g ((x : ℂ) + (r : ℂ) * I))
        (-I * ((((x : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) y := by
    let e : ℂ → ℂ := fun z => g ((x : ℂ) + z * I)
    have hden : ((x : ℂ) + (y : ℂ) * I) - p ≠ 0 := by
      intro h
      apply hx
      have hre := congrArg Complex.re h
      exact sub_eq_zero.mp (by simpa using hre)
    have he : HasDerivAt e
        (-I * ((((x : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) (y : ℂ) := by
      dsimp [e, g]
      have hinner : HasDerivAt (fun z : ℂ => (x : ℂ) + z * I) I (y : ℂ) := by
        simpa using! ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)
      simpa [div_eq_mul_inv, inv_pow, mul_comm] using!
        (hinner.sub_const p).inv hden
    simpa [e, g] using he.comp_ofReal
  have hbottom :
      (∫ x in a..b, ((((x : ℂ) + (u : ℂ) * I) - p)⁻¹ ^ 2)) =
        g ((a : ℂ) + (u : ℂ) * I) -
          g ((b : ℂ) + (u : ℂ) * I) := by
    have hderiv : deriv (fun x : ℝ =>
        g ((x : ℂ) + (u : ℂ) * I)) =
      fun x : ℝ => -(((((x : ℂ) + (u : ℂ) * I) - p)⁻¹ ^ 2)) := by
      funext x
      exact (horizontal_deriv u x hu).deriv
    have hftc := intervalIntegral.integral_deriv_eq_sub'
      (a := a) (b := b)
      (fun x : ℝ => g ((x : ℂ) + (u : ℂ) * I)) hderiv
      (by intro x hx; exact (horizontal_deriv u x hu).differentiableAt)
      (by
        apply Continuous.continuousOn
        apply Continuous.neg
        apply Continuous.pow
        apply Continuous.inv₀
        · fun_prop
        · intro x h
          apply hu
          have him := congrArg Complex.im h
          exact sub_eq_zero.mp (by simpa using him))
    rw [intervalIntegral.integral_neg] at hftc
    linear_combination (-1) * hftc
  have htop :
      (∫ x in a..b, ((((x : ℂ) + (v : ℂ) * I) - p)⁻¹ ^ 2)) =
        g ((a : ℂ) + (v : ℂ) * I) -
          g ((b : ℂ) + (v : ℂ) * I) := by
    have hderiv : deriv (fun x : ℝ =>
        g ((x : ℂ) + (v : ℂ) * I)) =
      fun x : ℝ => -(((((x : ℂ) + (v : ℂ) * I) - p)⁻¹ ^ 2)) := by
      funext x
      exact (horizontal_deriv v x hv).deriv
    have hftc := intervalIntegral.integral_deriv_eq_sub'
      (a := a) (b := b)
      (fun x : ℝ => g ((x : ℂ) + (v : ℂ) * I)) hderiv
      (by intro x hx; exact (horizontal_deriv v x hv).differentiableAt)
      (by
        apply Continuous.continuousOn
        apply Continuous.neg
        apply Continuous.pow
        apply Continuous.inv₀
        · fun_prop
        · intro x h
          apply hv
          have him := congrArg Complex.im h
          exact sub_eq_zero.mp (by simpa using him))
    rw [intervalIntegral.integral_neg] at hftc
    linear_combination (-1) * hftc
  have hright :
      (∫ y in u..v, ((((b : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) =
        I * (g ((b : ℂ) + (v : ℂ) * I) -
          g ((b : ℂ) + (u : ℂ) * I)) := by
    have hderiv : deriv (fun y : ℝ =>
        g ((b : ℂ) + (y : ℂ) * I)) =
      fun y : ℝ => -I * (((((b : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) := by
      funext y
      exact (vertical_deriv b y hb).deriv
    have hftc := intervalIntegral.integral_deriv_eq_sub'
      (a := u) (b := v)
      (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * I)) hderiv
      (by intro y hy; exact (vertical_deriv b y hb).differentiableAt)
      (by
        apply Continuous.continuousOn
        apply Continuous.const_mul
        apply Continuous.pow
        apply Continuous.inv₀
        · fun_prop
        · intro y h
          apply hb
          have hre := congrArg Complex.re h
          exact sub_eq_zero.mp (by simpa using hre))
    rw [intervalIntegral.integral_const_mul] at hftc
    have hI : I * (-I) = (1 : ℂ) := by simp [I_sq]
    calc
      (∫ y in u..v, ((((b : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) =
          I * (-I * ∫ y in u..v,
            ((((b : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) := by
              rw [← mul_assoc, hI, one_mul]
      _ = I * (g ((b : ℂ) + (v : ℂ) * I) -
          g ((b : ℂ) + (u : ℂ) * I)) := by rw [hftc]
  have hleft :
      (∫ y in u..v, ((((a : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) =
        I * (g ((a : ℂ) + (v : ℂ) * I) -
          g ((a : ℂ) + (u : ℂ) * I)) := by
    have hderiv : deriv (fun y : ℝ =>
        g ((a : ℂ) + (y : ℂ) * I)) =
      fun y : ℝ => -I * (((((a : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) := by
      funext y
      exact (vertical_deriv a y ha).deriv
    have hftc := intervalIntegral.integral_deriv_eq_sub'
      (a := u) (b := v)
      (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * I)) hderiv
      (by intro y hy; exact (vertical_deriv a y ha).differentiableAt)
      (by
        apply Continuous.continuousOn
        apply Continuous.const_mul
        apply Continuous.pow
        apply Continuous.inv₀
        · fun_prop
        · intro y h
          apply ha
          have hre := congrArg Complex.re h
          exact sub_eq_zero.mp (by simpa using hre))
    rw [intervalIntegral.integral_const_mul] at hftc
    have hI : I * (-I) = (1 : ℂ) := by simp [I_sq]
    calc
      (∫ y in u..v, ((((a : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) =
          I * (-I * ∫ y in u..v,
            ((((a : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ 2)) := by
              rw [← mul_assoc, hI, one_mul]
      _ = I * (g ((a : ℂ) + (v : ℂ) * I) -
          g ((a : ℂ) + (u : ℂ) * I)) := by rw [hftc]
  unfold rectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]
  dsimp [g]
  simp only [← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]
  ring

/-! ## Two-stage analytic removal of the Gamma and translated zeta poles -/

/-- Entire numerator after multiplying the raw principal integrand by the
Gamma variable and by the square of the translated zeta-pole displacement. -/
def principalShiftedGammaCore (s : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  principalF (s + w) ^ 2 * Complex.Gamma (w + 1) * (X : ℂ) ^ w

def principalTranslatedPole (s : ℂ) : ℂ := 1 - s

/-- Numerator whose zero at `w=0` removes the Gamma residue while retaining
the translated double pole. -/
def principalGammaZeroKernel (s : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  let p := principalTranslatedPole s
  p ^ 2 * principalShiftedGammaCore s X w -
    principalShiftedGammaCore s X 0 * (w - p) ^ 2

/-- Analytic numerator left after the Gamma pole has been removed. -/
def principalAfterGammaPole (s : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  dslope (principalGammaZeroKernel s X) 0 w /
    principalTranslatedPole s ^ 2

/-- First divided difference at the translated zeta pole.  Its value at the
pole is the literal residue coefficient of the double-pole term. -/
def principalTranslatedFirstDifference (s : ℂ) (X : ℝ) : ℂ → ℂ :=
  dslope (principalAfterGammaPole s X) (principalTranslatedPole s)

/-- Analytic remainder after removing both the double and simple translated
principal parts. -/
def principalTranslatedPoleRemainder (s : ℂ) (X : ℝ) : ℂ → ℂ :=
  dslope (principalTranslatedFirstDifference s X)
    (principalTranslatedPole s)

theorem analyticAt_principalShiftedGammaCore
    (s : ℂ) {X : ℝ} (hX : 0 < X) {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (principalShiftedGammaCore s X) w := by
  unfold principalShiftedGammaCore
  have hF : AnalyticAt ℂ (fun z : ℂ => principalF (s + z)) w :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt
      (s + w) |>.comp (by fun_prop)
  have hGamma : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w := by
    apply MAPAppendixA4Detector.analyticAt_Gamma_add_one_of_mem_contourStrip
    exact hw
  have hpow : AnalyticAt ℂ (fun z : ℂ => (X : ℂ) ^ z) w :=
    (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).analyticAt w
  exact ((hF.pow 2).mul hGamma).mul hpow

theorem analyticAt_principalGammaZeroKernel
    (s : ℂ) {X : ℝ} (hX : 0 < X) {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (principalGammaZeroKernel s X) w := by
  unfold principalGammaZeroKernel
  exact (analyticAt_const.mul (analyticAt_principalShiftedGammaCore s hX hw)).sub
    (analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow 2))

theorem principalGammaZeroKernel_zero (s : ℂ) (X : ℝ) :
    principalGammaZeroKernel s X 0 = 0 := by
  unfold principalGammaZeroKernel principalTranslatedPole
  ring

theorem analyticAt_principalAfterGammaPole
    (s : ℂ) {X : ℝ} (hX : 0 < X) (hs : s ≠ 1)
    {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (principalAfterGammaPole s X) w := by
  unfold principalAfterGammaPole
  have hp : principalTranslatedPole s ≠ 0 := by
    unfold principalTranslatedPole
    exact sub_ne_zero.mpr (Ne.symm hs)
  have hzero : AnalyticAt ℂ (principalGammaZeroKernel s X) 0 :=
    analyticAt_principalGammaZeroKernel s hX (by norm_num)
  have hhere : AnalyticAt ℂ (principalGammaZeroKernel s X) w :=
    analyticAt_principalGammaZeroKernel s hX hw
  have hds : AnalyticAt ℂ (dslope (principalGammaZeroKernel s X) 0) w :=
    analyticAt_dslope_of_analyticAt hzero hhere
  exact hds.div analyticAt_const (pow_ne_zero 2 hp)

theorem analyticAt_principalTranslatedFirstDifference
    (s : ℂ) {X : ℝ} (hX : 0 < X) (hs : s ≠ 1)
    (hpStrip : -1 < (principalTranslatedPole s).re)
    {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (principalTranslatedFirstDifference s X) w := by
  unfold principalTranslatedFirstDifference
  exact analyticAt_dslope_of_analyticAt
    (analyticAt_principalAfterGammaPole s hX hs hpStrip)
    (analyticAt_principalAfterGammaPole s hX hs hw)

theorem analyticAt_principalTranslatedPoleRemainder
    (s : ℂ) {X : ℝ} (hX : 0 < X) (hs : s ≠ 1)
    (hpStrip : -1 < (principalTranslatedPole s).re)
    {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (principalTranslatedPoleRemainder s X) w := by
  unfold principalTranslatedPoleRemainder
  exact analyticAt_dslope_of_analyticAt
    (analyticAt_principalTranslatedFirstDifference s hX hs hpStrip hpStrip)
    (analyticAt_principalTranslatedFirstDifference s hX hs hpStrip hw)

/-- Exact relation between the regularized analytic core and the raw
Gamma--zeta integrand away from its two poles. -/
theorem principalShiftedGammaCore_eq_raw
    {s w : ℂ} {X : ℝ} (hw : w ≠ 0)
    (hpole : s + w ≠ 1) :
    principalShiftedGammaCore s X w =
      w * (w - principalTranslatedPole s) ^ 2 *
        shiftedGammaRawIntegrand chiOne s X w := by
  rw [principalShiftedGammaCore,
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hpole,
    Complex.Gamma_add_one w hw]
  unfold shiftedGammaRawIntegrand principalTranslatedPole
  rw [DirichletCharacter.LFunction_modOne_eq]
  ring

theorem principalShiftedGammaCore_zero_eq
    {s : ℂ} {X : ℝ} (hs : s ≠ 1) :
    principalShiftedGammaCore s X 0 =
      principalTranslatedPole s ^ 2 *
        DirichletCharacter.LFunction chiOne s ^ 2 := by
  rw [principalShiftedGammaCore]
  simp only [add_zero]
  rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs,
    DirichletCharacter.LFunction_modOne_eq]
  simp [principalTranslatedPole]
  ring

/-- First exact pole split: Gamma residue plus a translated double pole with
analytic numerator. -/
theorem shiftedGammaRawIntegrand_principal_eq_gamma_add_double
    {s w : ℂ} {X : ℝ} (hs : s ≠ 1) (hw : w ≠ 0)
    (hpole : w ≠ principalTranslatedPole s) :
    shiftedGammaRawIntegrand chiOne s X w =
      DirichletCharacter.LFunction chiOne s ^ 2 * w⁻¹ +
        principalAfterGammaPole s X w *
          (w - principalTranslatedPole s)⁻¹ ^ 2 := by
  have hp : principalTranslatedPole s ≠ 0 := by
    unfold principalTranslatedPole
    exact sub_ne_zero.mpr (Ne.symm hs)
  have hsp : s + w ≠ 1 := by
    intro h
    apply hpole
    unfold principalTranslatedPole
    linear_combination h
  have hcore := principalShiftedGammaCore_eq_raw
    (s := s) (w := w) (X := X) hw hsp
  have hcore0 := principalShiftedGammaCore_zero_eq (s := s) (X := X) hs
  have hkernel0 := principalGammaZeroKernel_zero s X
  have hds : dslope (principalGammaZeroKernel s X) 0 w =
      principalGammaZeroKernel s X w / w := by
    rw [dslope_of_ne]
    · simp [slope, hkernel0, div_eq_inv_mul]
    · exact hw
  unfold principalAfterGammaPole
  rw [hds]
  unfold principalGammaZeroKernel
  rw [hcore, hcore0]
  field_simp [hw, hp, sub_ne_zero.mpr hpole]
  ring

/-- Full principal-part expansion: Gamma residue, double translated pole,
simple translated residue, and an analytic remainder. -/
theorem shiftedGammaRawIntegrand_principal_pole_expansion
    {s w : ℂ} {X : ℝ} (hs : s ≠ 1) (hw : w ≠ 0)
    (hpole : w ≠ principalTranslatedPole s) :
    shiftedGammaRawIntegrand chiOne s X w =
      principalTranslatedPoleRemainder s X w +
        DirichletCharacter.LFunction chiOne s ^ 2 * w⁻¹ +
        principalAfterGammaPole s X (principalTranslatedPole s) *
          (w - principalTranslatedPole s)⁻¹ ^ 2 +
        principalTranslatedFirstDifference s X
            (principalTranslatedPole s) *
          (w - principalTranslatedPole s)⁻¹ := by
  have hfirst :
      principalTranslatedFirstDifference s X w =
        (principalAfterGammaPole s X w -
          principalAfterGammaPole s X (principalTranslatedPole s)) /
            (w - principalTranslatedPole s) := by
    rw [principalTranslatedFirstDifference, dslope_of_ne]
    · simp [slope, div_eq_inv_mul]
    · exact hpole
  have hsecond :
      principalTranslatedPoleRemainder s X w =
        (principalTranslatedFirstDifference s X w -
          principalTranslatedFirstDifference s X
            (principalTranslatedPole s)) /
              (w - principalTranslatedPole s) := by
    rw [principalTranslatedPoleRemainder, dslope_of_ne]
    · simp [slope, div_eq_inv_mul]
    · exact hpole
  rw [hfirst] at hsecond
  rw [shiftedGammaRawIntegrand_principal_eq_gamma_add_double hs hw hpole]
  have hden : w - principalTranslatedPole s ≠ 0 :=
    sub_ne_zero.mpr hpole
  have hsecondClear :
      principalTranslatedPoleRemainder s X w *
          (w - principalTranslatedPole s) ^ 2 =
        principalAfterGammaPole s X w -
          principalAfterGammaPole s X (principalTranslatedPole s) -
          (w - principalTranslatedPole s) *
            principalTranslatedFirstDifference s X
              (principalTranslatedPole s) := by
    field_simp [hden] at hsecond
    exact hsecond
  have htail :
      principalAfterGammaPole s X w *
          (w - principalTranslatedPole s)⁻¹ ^ 2 =
        principalTranslatedPoleRemainder s X w +
          principalAfterGammaPole s X (principalTranslatedPole s) *
            (w - principalTranslatedPole s)⁻¹ ^ 2 +
          principalTranslatedFirstDifference s X
              (principalTranslatedPole s) *
            (w - principalTranslatedPole s)⁻¹ := by
    field_simp [hden]
    linear_combination (-1) * hsecondClear
  rw [htail]
  ring

theorem boundaryIntervalIntegrable_sub_inv_pow
    (p : ℂ) (n : ℕ) {a b u v : ℝ}
    (ha : a ≠ p.re) (hb : b ≠ p.re)
    (hu : u ≠ p.im) (hv : v ≠ p.im) :
    BoundaryIntervalIntegrable (fun z : ℂ => (z - p)⁻¹ ^ n) a b u v := by
  have hhorizontal (y : ℝ) (hy : y ≠ p.im) :
      Continuous (fun x : ℝ =>
        ((((x : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ n)) := by
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro x h
      apply hy
      have him := congrArg Complex.im h
      exact sub_eq_zero.mp (by simpa using him)
  have hvertical (x : ℝ) (hx : x ≠ p.re) :
      Continuous (fun y : ℝ =>
        ((((x : ℂ) + (y : ℂ) * I) - p)⁻¹ ^ n)) := by
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro y h
      apply hx
      have hre := congrArg Complex.re h
      exact sub_eq_zero.mp (by simpa using hre)
  exact ⟨by simpa using (hhorizontal u hu).intervalIntegrable a b,
    by simpa using (hhorizontal v hv).intervalIntegrable a b,
    by simpa using (hvertical b hb).intervalIntegrable u v,
    by simpa using (hvertical a ha).intervalIntegrable u v⟩

theorem BoundaryIntervalIntegrable.add
    {f g : ℂ → ℂ} {a b u v : ℝ}
    (hf : BoundaryIntervalIntegrable f a b u v)
    (hg : BoundaryIntervalIntegrable g a b u v) :
    BoundaryIntervalIntegrable (fun z => f z + g z) a b u v :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

theorem BoundaryIntervalIntegrable.const_mul
    {f : ℂ → ℂ} {a b u v : ℝ}
    (hf : BoundaryIntervalIntegrable f a b u v) (c : ℂ) :
    BoundaryIntervalIntegrable (fun z => c * f z) a b u v :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c,
    hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩

theorem rectangleBoundaryIntegral_add
    {f g : ℂ → ℂ} {a b u v : ℝ}
    (hf : BoundaryIntervalIntegrable f a b u v)
    (hg : BoundaryIntervalIntegrable g a b u v) :
    rectangleBoundaryIntegral (fun z => f z + g z) a b u v =
      rectangleBoundaryIntegral f a b u v +
        rectangleBoundaryIntegral g a b u v := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem rectangleBoundaryIntegral_const_mul
    (c : ℂ) (f : ℂ → ℂ) (a b u v : ℝ) :
    rectangleBoundaryIntegral (fun z => c * f z) a b u v =
      c * rectangleBoundaryIntegral f a b u v := by
  unfold rectangleBoundaryIntegral
  simp_rw [intervalIntegral.integral_const_mul]
  ring

/-- Exact finite principal rectangle: the Gamma residue and the translated
zeta residue both survive; the translated double principal part integrates
to zero. -/
theorem rectangleBoundaryIntegral_shiftedGammaRaw_principal
    (s : ℂ) {X a b u v r0 rp : ℝ}
    (hX : 0 < X) (hs : s ≠ 1) (haStrip : -1 < a)
    (hr0 : 0 < r0) (ha0 : a < -r0) (hb0 : r0 < b)
    (hu0 : u < -r0) (hv0 : r0 < v)
    (hrp : 0 < rp)
    (hap : a < (principalTranslatedPole s).re - rp)
    (hbp : (principalTranslatedPole s).re + rp < b)
    (hup : u < (principalTranslatedPole s).im - rp)
    (hvp : (principalTranslatedPole s).im + rp < v) :
    rectangleBoundaryIntegral (shiftedGammaRawIntegrand chiOne s X)
        a b u v =
      (2 * Real.pi * I) *
        (DirichletCharacter.LFunction chiOne s ^ 2 +
          principalTranslatedFirstDifference s X
            (principalTranslatedPole s)) := by
  let p : Bool → ℂ := fun i => if i then principalTranslatedPole s else 0
  let residue : Bool → ℂ := fun i => if i then
    principalTranslatedFirstDifference s X (principalTranslatedPole s)
    else DirichletCharacter.LFunction chiOne s ^ 2
  let radius : Bool → ℝ := fun i => if i then rp else r0
  let g : ℂ → ℂ := principalTranslatedPoleRemainder s X
  let fSimple : ℂ → ℂ := fun z => g z +
    DirichletCharacter.LFunction chiOne s ^ 2 * z⁻¹ +
    principalTranslatedFirstDifference s X (principalTranslatedPole s) *
      (z - principalTranslatedPole s)⁻¹
  let doublePart : ℂ → ℂ := fun z =>
    principalAfterGammaPole s X (principalTranslatedPole s) *
      (z - principalTranslatedPole s)⁻¹ ^ 2
  have hab : a ≤ b := by linarith
  have huv : u ≤ v := by linarith
  have hpStrip : -1 < (principalTranslatedPole s).re := by
    linarith
  have hgdiff : DifferentiableOn ℂ g (uIcc a b ×ℂ uIcc u v) := by
    intro z hz
    have hzre : a ≤ z.re := by
      have h := hz.1.1
      rw [min_eq_left hab] at h
      exact h
    exact (analyticAt_principalTranslatedPoleRemainder s hX hs hpStrip
      (haStrip.trans_le hzre)).differentiableAt.differentiableWithinAt
  have hgBI : BoundaryIntervalIntegrable g a b u v :=
    boundaryIntervalIntegrable_of_differentiableOn hgdiff
  have h0BI : BoundaryIntervalIntegrable
      (fun z : ℂ => (z - (0 : ℂ))⁻¹ ^ 1) a b u v :=
    boundaryIntervalIntegrable_sub_inv_pow
      (a := a) (b := b) (u := u) (v := v) (0 : ℂ) 1
      (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)
  have hpBI : BoundaryIntervalIntegrable
      (fun z : ℂ => (z - principalTranslatedPole s)⁻¹ ^ 1) a b u v :=
    boundaryIntervalIntegrable_sub_inv_pow
      (a := a) (b := b) (u := u) (v := v)
      (principalTranslatedPole s) 1
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hsimpleBI : BoundaryIntervalIntegrable fSimple a b u v := by
    have h0term : BoundaryIntervalIntegrable
        (fun z : ℂ => DirichletCharacter.LFunction chiOne s ^ 2 * z⁻¹)
        a b u v := by
      simpa [pow_one] using
        (BoundaryIntervalIntegrable.const_mul h0BI
          (DirichletCharacter.LFunction chiOne s ^ 2))
    have hpterm : BoundaryIntervalIntegrable
        (fun z : ℂ =>
          principalTranslatedFirstDifference s X (principalTranslatedPole s) *
            (z - principalTranslatedPole s)⁻¹) a b u v := by
      simpa [pow_one] using
        (BoundaryIntervalIntegrable.const_mul hpBI
          (principalTranslatedFirstDifference s X
            (principalTranslatedPole s)))
    exact BoundaryIntervalIntegrable.add
      (BoundaryIntervalIntegrable.add hgBI h0term) hpterm
  have hsimpleBoundary : rectangleBoundaryIntegral fSimple a b u v =
      (2 * Real.pi * I) *
        (DirichletCharacter.LFunction chiOne s ^ 2 +
          principalTranslatedFirstDifference s X
            (principalTranslatedPole s)) := by
    have hsum : (∑ i ∈ ({false, true} : Finset Bool), residue i) =
        DirichletCharacter.LFunction chiOne s ^ 2 +
          principalTranslatedFirstDifference s X
            (principalTranslatedPole s) := by
      simp [residue, add_comm]
    rw [← hsum]
    apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
      ({false, true} : Finset Bool) p residue radius fSimple g a b u v
    · intro i hi
      cases i <;> simp [radius, hr0, hrp]
    · intro i hi
      cases i <;> simp [p, radius] <;> linarith
    · intro i hi
      cases i <;> simp [p, radius] <;> linarith
    · intro i hi
      cases i <;> simp [p, radius] <;> linarith
    · intro i hi
      cases i <;> simp [p, radius] <;> linarith
    · exact hgBI
    · exact hgdiff
    all_goals
      intro x
      simp [fSimple, g, p, residue]
      ring
  have hpDoubleBI : BoundaryIntervalIntegrable
      (fun z : ℂ => (z - principalTranslatedPole s)⁻¹ ^ 2) a b u v :=
    boundaryIntervalIntegrable_sub_inv_pow
      (a := a) (b := b) (u := u) (v := v)
      (principalTranslatedPole s) 2
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hdoubleBI : BoundaryIntervalIntegrable doublePart a b u v :=
    BoundaryIntervalIntegrable.const_mul hpDoubleBI _
  have hdoubleZero : rectangleBoundaryIntegral doublePart a b u v = 0 := by
    rw [show rectangleBoundaryIntegral doublePart a b u v =
      principalAfterGammaPole s X (principalTranslatedPole s) *
        rectangleBoundaryIntegral
          (fun z : ℂ => (z - principalTranslatedPole s)⁻¹ ^ 2)
          a b u v by
      exact rectangleBoundaryIntegral_const_mul _ _ _ _ _ _]
    rw [rectangleBoundaryIntegral_sub_inv_sq_eq_zero
      (principalTranslatedPole s)
      (by linarith) (by linarith) (by linarith) (by linarith), mul_zero]
  have hrawBoundaryEq : ∀ z : ℂ,
      z ≠ 0 → z ≠ principalTranslatedPole s →
      shiftedGammaRawIntegrand chiOne s X z = fSimple z + doublePart z := by
    intro z hz0 hzp
    rw [shiftedGammaRawIntegrand_principal_pole_expansion hs hz0 hzp]
    simp [fSimple, doublePart, g]
    ring
  have hedgeBottom (x : ℝ) :
      shiftedGammaRawIntegrand chiOne s X
          ((x : ℂ) + (u : ℂ) * I) =
        fSimple ((x : ℂ) + (u : ℂ) * I) +
          doublePart ((x : ℂ) + (u : ℂ) * I) := by
    apply hrawBoundaryEq
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  have hedgeTop (x : ℝ) :
      shiftedGammaRawIntegrand chiOne s X
          ((x : ℂ) + (v : ℂ) * I) =
        fSimple ((x : ℂ) + (v : ℂ) * I) +
          doublePart ((x : ℂ) + (v : ℂ) * I) := by
    apply hrawBoundaryEq
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  have hedgeRight (y : ℝ) :
      shiftedGammaRawIntegrand chiOne s X
          ((b : ℂ) + (y : ℂ) * I) =
        fSimple ((b : ℂ) + (y : ℂ) * I) +
          doublePart ((b : ℂ) + (y : ℂ) * I) := by
    apply hrawBoundaryEq
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
  have hedgeLeft (y : ℝ) :
      shiftedGammaRawIntegrand chiOne s X
          ((a : ℂ) + (y : ℂ) * I) =
        fSimple ((a : ℂ) + (y : ℂ) * I) +
          doublePart ((a : ℂ) + (y : ℂ) * I) := by
    apply hrawBoundaryEq
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
  have hrawAdd : rectangleBoundaryIntegral
      (shiftedGammaRawIntegrand chiOne s X) a b u v =
      rectangleBoundaryIntegral fSimple a b u v +
        rectangleBoundaryIntegral doublePart a b u v := by
    unfold rectangleBoundaryIntegral
    rw [show (∫ x in a..b, shiftedGammaRawIntegrand chiOne s X
        ((x : ℂ) + (u : ℂ) * I)) =
      ∫ x in a..b, fSimple ((x : ℂ) + (u : ℂ) * I) +
        doublePart ((x : ℂ) + (u : ℂ) * I) by
          apply intervalIntegral.integral_congr
          intro x hx
          exact hedgeBottom x,
      intervalIntegral.integral_add hsimpleBI.1 hdoubleBI.1]
    rw [show (∫ x in a..b, shiftedGammaRawIntegrand chiOne s X
        ((x : ℂ) + (v : ℂ) * I)) =
      ∫ x in a..b, fSimple ((x : ℂ) + (v : ℂ) * I) +
        doublePart ((x : ℂ) + (v : ℂ) * I) by
          apply intervalIntegral.integral_congr
          intro x hx
          exact hedgeTop x,
      intervalIntegral.integral_add hsimpleBI.2.1 hdoubleBI.2.1]
    rw [show (∫ y in u..v, shiftedGammaRawIntegrand chiOne s X
        ((b : ℂ) + (y : ℂ) * I)) =
      ∫ y in u..v, fSimple ((b : ℂ) + (y : ℂ) * I) +
        doublePart ((b : ℂ) + (y : ℂ) * I) by
          apply intervalIntegral.integral_congr
          intro y hy
          exact hedgeRight y,
      intervalIntegral.integral_add hsimpleBI.2.2.1 hdoubleBI.2.2.1]
    rw [show (∫ y in u..v, shiftedGammaRawIntegrand chiOne s X
        ((a : ℂ) + (y : ℂ) * I)) =
      ∫ y in u..v, fSimple ((a : ℂ) + (y : ℂ) * I) +
        doublePart ((a : ℂ) + (y : ℂ) * I) by
          apply intervalIntegral.integral_congr
          intro y hy
          exact hedgeLeft y,
      intervalIntegral.integral_add hsimpleBI.2.2.2 hdoubleBI.2.2.2]
    ring
  rw [hrawAdd, hdoubleZero, add_zero, hsimpleBoundary]

end
end RamachandraPrincipalHighContourIdentity

#print axioms RamachandraPrincipalHighContourIdentity.rectangleBoundaryIntegral_sub_inv_sq_eq_zero
#print axioms RamachandraPrincipalHighContourIdentity.rectangleBoundaryIntegral_shiftedGammaRaw_principal
