import MRTVanDerCorputCore
import Mathlib.Analysis.BoundedVariation

/-!
# The stationary-packet van der Corput estimate in MRT Proposition 5.1

The weighted second-derivative test, the fixed-window amplitude variation,
and their specialization to the literal `Jₓ(t)` packet are all proved here.
No proposition-valued citation boundary remains in the stationary step.
-/

namespace MAPMRTVanDerCorput

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTProposition51Source
open MAPMRTCorollary53Source

noncomputable section

/-- The outer factor `cutoff(w/100)` in (80) confines the literal amplitude
to `[-100,100]`, independently of `H/X`.  This is the support fact that keeps
the proof valid in the full MAP half-range `H ≤ X/2`. -/
theorem sourcePacketAmplitude_eq_zero_of_not_mem_outerWindow
    {X H x w : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0)
    (hw : w ∉ Set.Ioc (-100 : ℝ) 100) :
    sourcePacketAmplitude X H x cutoff outerCutoff w = 0 := by
  have habs : 1 ≤ |w / 100| := by
    simp only [Set.mem_Ioc, not_and_or, not_lt] at hw
    rcases hw with hw | hw
    · rw [abs_of_nonpos (by linarith : w / 100 ≤ 0)]
      linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ w / 100)]
      linarith
  unfold sourcePacketAmplitude
  rw [houterSupport _ habs]
  simp

/-- Equation (80)'s whole-line packet is exactly its interval integral on the
fixed outer window. -/
theorem sourceStationaryPacket_eq_onOuterWindow
    {X H x beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0) :
    sourceStationaryPacket X H x beta t cutoff outerCutoff =
      stationaryPacketOn X beta t
        (sourcePacketAmplitude X H x cutoff outerCutoff) (-100) 100 := by
  let integrand : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x cutoff outerCutoff w
  have hindicator : integrand = Set.indicator (Set.Ioc (-100 : ℝ) 100) integrand := by
    funext w
    by_cases hw : w ∈ Set.Ioc (-100 : ℝ) 100
    · simp [hw]
    · have hz := sourcePacketAmplitude_eq_zero_of_not_mem_outerWindow
        (X := X) (H := H) (x := x) (cutoff := cutoff)
        houterSupport hw
      simp [integrand, hw, hz]
  unfold sourceStationaryPacket stationaryPacketOn
  change (∫ w : ℝ, integrand w) = _
  rw [hindicator, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-100 : ℝ) ≤ 100)]

/-- The exact second derivative of the phase `βXe^w+tw/(2π)`. -/
theorem hasDerivAt_stationaryPacketPhase_firstDerivative
    (X beta t w : ℝ) :
    HasDerivAt (fun z ↦ beta * X * Real.exp z + t / (2 * Real.pi))
      (beta * X * Real.exp w) w :=
  hasDerivAt_stationaryPacketPhase_deriv X beta t w

/-- On the fixed outer window, the curvature has a uniform lower bound with
the exact absolute constant `exp(-100)`. -/
theorem stationaryPacketPhase_curvature_lower_on_outerWindow
    {X beta w : ℝ} (hX : 0 ≤ X)
    (hw : w ∈ Set.Icc (-100 : ℝ) 100) :
    |beta| * X * Real.exp (-100) ≤ |beta * X * Real.exp w| := by
  have hexp : Real.exp (-100) ≤ Real.exp w :=
    Real.exp_le_exp.mpr hw.1
  rw [abs_mul, abs_mul, abs_of_nonneg hX, abs_of_pos (Real.exp_pos w)]
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (abs_nonneg beta) hX)


/-- The literal derivative of MRT equation (80)'s amplitude. -/
def sourcePacketAmplitudeDeriv
    (X H x : ℝ) (cutoff cutoff' outerCutoff outerCutoff' : ℝ → ℝ)
    (w : ℝ) : ℂ :=
  ((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
      (cutoff ((X * Real.exp w - x) / H) : ℂ) *
        (outerCutoff (w / 100) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      ((cutoff' ((X * Real.exp w - x) / H) *
        (X * Real.exp w / H) : ℝ) : ℂ) *
        (outerCutoff (w / 100) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      (cutoff ((X * Real.exp w - x) / H) : ℂ) *
        ((outerCutoff' (w / 100) / 100 : ℝ) : ℂ)

/-- Product and chain rule for the exact source amplitude. -/
theorem hasDerivAt_sourcePacketAmplitude
    {X H x w : ℝ} {cutoff cutoff' outerCutoff outerCutoff' : ℝ → ℝ}
    (hcutoff : ∀ y : ℝ, HasDerivAt cutoff (cutoff' y) y)
    (houter : ∀ y : ℝ, HasDerivAt outerCutoff (outerCutoff' y) y) :
    HasDerivAt (sourcePacketAmplitude X H x cutoff outerCutoff)
      (sourcePacketAmplitudeDeriv X H x cutoff cutoff' outerCutoff outerCutoff' w) w := by
  have hexpHalfReal : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2))
      (Real.exp (w / 2) / 2) w := by
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_div, one_mul] using!
      (Real.hasDerivAt_exp (w / 2)).comp w ((hasDerivAt_id w).div_const 2)
  have hz : HasDerivAt (fun y : ℝ ↦ (X * Real.exp y - x) / H)
      (X * Real.exp w / H) w := by
    convert ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H using 1 <;> ring
  have hcutReal := (hcutoff ((X * Real.exp w - x) / H)).scomp w hz
  have houterArg : HasDerivAt (fun y : ℝ ↦ y / 100) (1 / 100) w := by
    simpa only [id_eq] using! (hasDerivAt_id w).div_const 100
  have houterReal := (houter (w / 100)).scomp w houterArg
  have hprod := (hexpHalfReal.ofReal_comp.mul hcutReal.ofReal_comp).mul
    houterReal.ofReal_comp
  change HasDerivAt (sourcePacketAmplitude X H x cutoff outerCutoff) _ w at hprod
  convert hprod using 1
  simp only [sourcePacketAmplitudeDeriv, Function.comp_apply, Pi.mul_apply,
    one_div, smul_eq_mul]
  push_cast
  ring

theorem intervalIntegral_le_integral_of_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Integrable f) (hnonneg : ∀ y, 0 ≤ f y) :
    (∫ y : ℝ in a..b, f y) ≤ ∫ y : ℝ, f y := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall hnonneg) hf

/-- The manuscript's `O(1)` amplitude-variation calculation, with every
constant exposed.  The two global derivative integrals are the fixed smooth
cutoff budgets; the packet parameters do not enter the resulting bound. -/
theorem integral_norm_sourcePacketAmplitudeDeriv_le
    {X H x Dcut Dout : ℝ}
    {cutoff cutoff' outerCutoff outerCutoff' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outerCutoff y| ≤ 1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outerCutoff (outerCutoff' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outerCutoff')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (houter'Int : Integrable (fun y ↦ |outerCutoff' y|))
    (hDcut : (∫ y : ℝ, |cutoff' y|) ≤ Dcut)
    (hDout : (∫ y : ℝ, |outerCutoff' y|) ≤ Dout) :
    (∫ w : ℝ in (-100)..100,
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff'
        outerCutoff outerCutoff' w‖) ≤
      Real.exp 50 * (100 + Dcut + Dout) := by
  let z : ℝ → ℝ := fun w ↦ (X * Real.exp w - x) / H
  let zd : ℝ → ℝ := fun w ↦ X * Real.exp w / H
  have hzDeriv : ∀ w, HasDerivAt z (zd w) w := by
    intro w
    unfold z zd
    convert ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H using 1 <;> ring
  have hzdNonneg : ∀ w, 0 ≤ zd w := by
    intro w
    unfold zd
    positivity
  have hzCont : Continuous z := by
    fun_prop
  have hchangeCutoff :
      (∫ w : ℝ in (-100)..100, |cutoff' (z w)| * zd w) =
        ∫ y : ℝ in z (-100)..z 100, |cutoff' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := (-100 : ℝ)) (b := 100) (f := z) (f' := zd)
        (g := fun y ↦ |cutoff' y|)
        hzCont.continuousOn (fun w _hw ↦ hzDeriv w) (fun w _hw ↦ hzdNonneg w))
  have hzOrder : z (-100) ≤ z 100 := by
    unfold z
    apply div_le_div_of_nonneg_right _ hH.le
    have he : Real.exp (-100) ≤ Real.exp 100 :=
      Real.exp_le_exp.mpr (by norm_num)
    have hXe := mul_le_mul_of_nonneg_left he hX.le
    linarith
  have hcutoffInterval :
      (∫ y : ℝ in z (-100)..z 100, |cutoff' y|) ≤ Dcut := by
    exact (intervalIntegral_le_integral_of_nonneg hzOrder hcutoff'Int
      (fun y ↦ abs_nonneg _)).trans hDcut
  let r : ℝ → ℝ := fun w ↦ w / 100
  let rd : ℝ → ℝ := fun _w ↦ 1 / 100
  have hrDeriv : ∀ w, HasDerivAt r (rd w) w := by
    intro w
    unfold r rd
    simpa only [id_eq] using! (hasDerivAt_id w).div_const 100
  have hrdNonneg : ∀ w, 0 ≤ rd w := by
    intro w
    unfold rd
    norm_num
  have hrCont : Continuous r := by fun_prop
  have hchangeOuter :
      (∫ w : ℝ in (-100)..100, |outerCutoff' (r w)| * rd w) =
        ∫ y : ℝ in r (-100)..r 100, |outerCutoff' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := (-100 : ℝ)) (b := 100) (f := r) (f' := rd)
        (g := fun y ↦ |outerCutoff' y|)
        hrCont.continuousOn (fun w _hw ↦ hrDeriv w) (fun w _hw ↦ hrdNonneg w))
  have hrOrder : r (-100) ≤ r 100 := by unfold r; norm_num
  have houterInterval :
      (∫ y : ℝ in r (-100)..r 100, |outerCutoff' y|) ≤ Dout := by
    exact (intervalIntegral_le_integral_of_nonneg hrOrder houter'Int
      (fun y ↦ abs_nonneg _)).trans hDout
  have hpoint : ∀ w ∈ Set.Icc (-100 : ℝ) 100,
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff'
        outerCutoff outerCutoff' w‖ ≤
        Real.exp 50 / 2 +
          Real.exp 50 * (|cutoff' (z w)| * zd w) +
          Real.exp 50 * (|outerCutoff' (r w)| * rd w) := by
    intro w hw
    have hexp : Real.exp (w / 2) ≤ Real.exp 50 := by
      apply Real.exp_le_exp.mpr
      have hwUpper := hw.2
      linarith
    have hexpNonneg : 0 ≤ Real.exp (w / 2) := (Real.exp_pos _).le
    have hcutNonneg : 0 ≤ |cutoff ((X * Real.exp w - x) / H)| := abs_nonneg _
    have houterNonneg : 0 ≤ |outerCutoff (w / 100)| := abs_nonneg _
    have hterm1 :
        ‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
          (outerCutoff (w / 100) : ℂ)‖ ≤ Real.exp 50 / 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ Real.exp (w / 2) / 2)]
      calc
        Real.exp (w / 2) / 2 *
            |cutoff ((X * Real.exp w - x) / H)| * |outerCutoff (w / 100)| ≤
            Real.exp (w / 2) / 2 * 1 * 1 := by
          gcongr
          · exact hcutoffBound _
          · exact houterBound _
        _ ≤ Real.exp 50 / 2 := by nlinarith
    have hterm2 :
        ‖(Real.exp (w / 2) : ℂ) *
          ((cutoff' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) : ℝ) : ℂ) *
          (outerCutoff (w / 100) : ℂ)‖ ≤
            Real.exp 50 * (|cutoff' (z w)| * zd w) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_mul]
      rw [abs_of_nonneg (hzdNonneg w)]
      unfold z zd
      calc
        Real.exp (w / 2) *
            (|cutoff' ((X * Real.exp w - x) / H)| * (X * Real.exp w / H)) *
            |outerCutoff (w / 100)| ≤
            Real.exp 50 *
              (|cutoff' ((X * Real.exp w - x) / H)| * (X * Real.exp w / H)) * 1 := by
          gcongr
          exact houterBound _
        _ = Real.exp 50 *
            (|cutoff' ((X * Real.exp w - x) / H)| * (X * Real.exp w / H)) := by ring
    have hterm3 :
        ‖(Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
          ((outerCutoff' (w / 100) / 100 : ℝ) : ℂ)‖ ≤
            Real.exp 50 * (|outerCutoff' (r w)| * rd w) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_div]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 100)]
      unfold r rd
      calc
        Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
            (|outerCutoff' (w / 100)| / 100) ≤
            Real.exp 50 * 1 * (|outerCutoff' (w / 100)| / 100) := by
          gcongr
          exact hcutoffBound _
        _ = Real.exp 50 * (|outerCutoff' (w / 100)| * (1 / 100)) := by ring
    unfold sourcePacketAmplitudeDeriv
    exact (norm_add_le _ _).trans <| add_le_add
      ((norm_add_le _ _).trans (add_le_add hterm1 hterm2)) hterm3
  have hiDeriv : IntervalIntegrable
      (fun w ↦ ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff'
        outerCutoff outerCutoff' w‖) volume (-100) 100 := by
    have hcutoffCont : Continuous cutoff :=
      continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
    have houterCont : Continuous outerCutoff :=
      continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    unfold sourcePacketAmplitudeDeriv
    fun_prop
  have hiCutTerm : IntervalIntegrable
      (fun w ↦ |cutoff' (z w)| * zd w) volume (-100) 100 := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    exact (hcutoff'Cont.abs.comp hzCont).mul (by unfold zd; fun_prop)
  have hiOuterTerm : IntervalIntegrable
      (fun w ↦ |outerCutoff' (r w)| * rd w) volume (-100) 100 := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    exact (houter'Cont.abs.comp hrCont).mul (by unfold rd; fun_prop)
  have hiConst : IntervalIntegrable (fun _w : ℝ ↦ Real.exp 50 / 2)
      volume (-100) 100 := intervalIntegrable_const
  have hiMajorant : IntervalIntegrable
      (fun w ↦ Real.exp 50 / 2 +
        Real.exp 50 * (|cutoff' (z w)| * zd w) +
        Real.exp 50 * (|outerCutoff' (r w)| * rd w))
      volume (-100) 100 :=
    (hiConst.add (hiCutTerm.const_mul (Real.exp 50))).add
      (hiOuterTerm.const_mul (Real.exp 50))
  calc
    (∫ w : ℝ in (-100)..100,
        ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff'
          outerCutoff outerCutoff' w‖) ≤
        ∫ w : ℝ in (-100)..100,
          (Real.exp 50 / 2 +
            Real.exp 50 * (|cutoff' (z w)| * zd w) +
            Real.exp 50 * (|outerCutoff' (r w)| * rd w)) :=
      intervalIntegral.integral_mono_on (by norm_num) hiDeriv hiMajorant hpoint
    _ = 100 * Real.exp 50 +
        Real.exp 50 * (∫ w : ℝ in (-100)..100, |cutoff' (z w)| * zd w) +
        Real.exp 50 * (∫ w : ℝ in (-100)..100, |outerCutoff' (r w)| * rd w) := by
      rw [intervalIntegral.integral_add
          (hiConst.add (hiCutTerm.const_mul (Real.exp 50)))
          (hiOuterTerm.const_mul (Real.exp 50)),
        intervalIntegral.integral_add hiConst
          (hiCutTerm.const_mul (Real.exp 50)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      simp
      ring
    _ = 100 * Real.exp 50 +
        Real.exp 50 * (∫ y : ℝ in z (-100)..z 100, |cutoff' y|) +
        Real.exp 50 * (∫ y : ℝ in r (-100)..r 100, |outerCutoff' y|) := by
      rw [hchangeCutoff, hchangeOuter]
    _ ≤ 100 * Real.exp 50 + Real.exp 50 * Dcut + Real.exp 50 * Dout := by
      gcongr
    _ = Real.exp 50 * (100 + Dcut + Dout) := by ring

/-- Fully internal stationary-packet bound used below (83).  The constant is
explicit in the two fixed cutoff derivative budgets; there is no proposition
or citation boundary left in the van der Corput step. -/
theorem norm_sourceStationaryPacket_le
    {X H x beta eta t Dcut Dout : ℝ}
    {cutoff cutoff' outerCutoff outerCutoff' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (_hetaPos : 0 < eta) (_hetaHard : eta < 1 / 100)
    (_hxLower : X / 2 ≤ x) (_hxUpper : x ≤ 4 * X)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outerCutoff y| ≤ 1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outerCutoff (outerCutoff' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outerCutoff')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (houter'Int : Integrable (fun y ↦ |outerCutoff' y|))
    (hDcut : (∫ y : ℝ, |cutoff' y|) ≤ Dcut)
    (hDout : (∫ y : ℝ, |outerCutoff' y|) ≤ Dout) :
    ‖sourceStationaryPacket X H x beta t cutoff outerCutoff‖ ≤
      10 * Real.exp 50 * (101 + Dcut + Dout) /
        Real.sqrt (|beta| * X * Real.exp (-100)) := by
  have hX : 0 < X := by linarith
  have hbeta : beta ≠ 0 := by
    intro hb
    subst beta
    norm_num at hhard
  let lambda : ℝ := |beta| * X * Real.exp (-100)
  let m : ℝ := Real.sqrt lambda
  have hlambda : 0 < lambda := by
    unfold lambda
    positivity
  have hm : 0 < m := by
    unfold m
    positivity
  have hmSq : m ^ 2 = lambda := by
    unfold m
    exact Real.sq_sqrt hlambda.le
  have hphaseSign :
      (∀ w ∈ Set.Icc (-100 : ℝ) 100, 0 ≤ beta * X * Real.exp w) ∨
      (∀ w ∈ Set.Icc (-100 : ℝ) 100, beta * X * Real.exp w ≤ 0) := by
    rcases le_total 0 beta with hbetaNonneg | hbetaNonpos
    · left
      intro w hw
      positivity
    · right
      intro w hw
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hbetaNonpos hX.le) (Real.exp_pos w).le
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outerCutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hampDerivCont : Continuous
      (sourcePacketAmplitudeDeriv X H x cutoff cutoff'
        outerCutoff outerCutoff') := by
    unfold sourcePacketAmplitudeDeriv
    fun_prop
  have hampBound : ∀ w ∈ Set.Icc (-100 : ℝ) 100,
      ‖sourcePacketAmplitude X H x cutoff outerCutoff w‖ ≤ Real.exp 50 := by
    intro w hw
    unfold sourcePacketAmplitude
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (w / 2) ≤ Real.exp 50 := by
      apply Real.exp_le_exp.mpr
      have hwUpper := hw.2
      linarith
    calc
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          |outerCutoff (w / 100)| ≤ Real.exp 50 * 1 * 1 := by
        gcongr
        · exact hcutoffBound _
        · exact houterBound _
      _ = Real.exp 50 := by ring
  have hvdc := MAPMRTVanDerCorputProof.weightedSecondDerivativeVanDerCorputC1
    (a := (-100 : ℝ)) (b := 100) (m := m) (M := Real.exp 50)
    (phase := stationaryPacketPhase X beta t)
    (phase' := fun w ↦ beta * X * Real.exp w + t / (2 * Real.pi))
    (phase'' := fun w ↦ beta * X * Real.exp w)
    (amplitude := sourcePacketAmplitude X H x cutoff outerCutoff)
    (amplitude' := sourcePacketAmplitudeDeriv X H x cutoff cutoff'
      outerCutoff outerCutoff')
    (by norm_num) hm (Real.exp_pos 50).le
    (fun w _hw ↦ hasDerivAt_stationaryPacketPhase X beta t w)
    (fun w _hw ↦ hasDerivAt_stationaryPacketPhase_firstDerivative X beta t w)
    (fun w hw ↦ by
      rw [hmSq]
      exact stationaryPacketPhase_curvature_lower_on_outerWindow hX.le hw)
    hphaseSign
    (fun w _hw ↦ hasDerivAt_sourcePacketAmplitude hcutoffDeriv houterDeriv)
    (by fun_prop) hampDerivCont.continuousOn hampBound
  have hvariation := integral_norm_sourcePacketAmplitudeDeriv_le
    (X := X) (H := H) (x := x) (Dcut := Dcut) (Dout := Dout)
    (cutoff := cutoff) (cutoff' := cutoff')
    (outerCutoff := outerCutoff) (outerCutoff' := outerCutoff')
    hX (lt_of_lt_of_le zero_lt_one hH) hcutoffBound houterBound
    hcutoffDeriv houterDeriv hcutoff'Cont houter'Cont
    hcutoff'Int houter'Int hDcut hDout
  rw [sourceStationaryPacket_eq_onOuterWindow houterSupport]
  unfold stationaryPacketOn
  refine hvdc.trans ?_
  rw [show m = Real.sqrt (|beta| * X * Real.exp (-100)) by rfl]
  apply div_le_div_of_nonneg_right _ hm.le
  calc
    10 * (Real.exp 50 +
        ∫ w : ℝ in (-100)..100,
          ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff'
            outerCutoff outerCutoff' w‖) ≤
        10 * (Real.exp 50 + Real.exp 50 * (100 + Dcut + Dout)) := by
      gcongr
    _ = 10 * Real.exp 50 * (101 + Dcut + Dout) := by ring

#print axioms MAPMRTVanDerCorput.integral_norm_sourcePacketAmplitudeDeriv_le
#print axioms MAPMRTVanDerCorput.norm_sourceStationaryPacket_le

end
end MAPMRTVanDerCorput
