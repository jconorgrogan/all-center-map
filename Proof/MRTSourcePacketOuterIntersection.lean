import MRTSourcePacketEquation84

/-!
# The outer-window/cutoff intersection in the `H > X/4` collar

This file deliberately does not enlarge the scope of the sharp logarithmic
window theorem.  It records the different interval forced by intersecting the
fixed outer window with the one-sided logarithmic cutoff window.
-/

namespace MAPMRTSourcePacketOuterIntersection

set_option maxHeartbeats 800000

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorput MAPMRTSourcePacketAmplitudeC2

noncomputable section

/-- The left endpoint of the support intersection.  When `x-H ≤ 0`, the
lower cutoff inequality is automatic and the outer endpoint is used. -/
def sourcePacketIntersectionLeft (X H x : ℝ) : ℝ :=
  if 0 < x - H then max (-100) (Real.log ((x - H) / X)) else -100

/-- In the source range the upper logarithmic endpoint lies inside the fixed
outer window, so it is the right endpoint of the intersection. -/
def sourcePacketIntersectionRight (X H x : ℝ) : ℝ :=
  Real.log ((x + H) / X)

theorem sourcePacketIntersection_geometry
    {X H x : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    let a := sourcePacketIntersectionLeft X H x
    let b := sourcePacketIntersectionRight X H x
    (-100 ≤ a ∧ a ≤ b ∧ b ≤ 100 ∧
      ∀ w ∈ Set.Icc a b, |X * Real.exp w - x| ≤ H) := by
  dsimp
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  have hxPlus : 0 < x + H := by linarith
  have hratioPlus : 0 < (x + H) / X := div_pos hxPlus hX
  have hbUpperExp : Real.exp b = (x + H) / X := by
    simp [b, sourcePacketIntersectionRight, Real.exp_log hratioPlus]
  have hbUpper : b ≤ 100 := by
    have hratioFive : (x + H) / X ≤ 5 := by
      rw [div_le_iff₀ hX]
      linarith
    have hlogBound : Real.log ((x + H) / X) ≤ (x + H) / X - 1 :=
      Real.log_le_sub_one_of_pos hratioPlus
    dsimp [b, sourcePacketIntersectionRight]
    linarith
  have hbLower : -100 ≤ b := by
    have hinv : ((x + H) / X)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hratioPlus (by norm_num : (0 : ℝ) < 2)]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, le_div_iff₀ hX]
      linarith
    have hlogLower := Real.one_sub_inv_le_log_of_pos hratioPlus
    dsimp [b, sourcePacketIntersectionRight]
    linarith
  have haLower : -100 ≤ a := by
    unfold a sourcePacketIntersectionLeft
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hab : a ≤ b := by
    unfold a sourcePacketIntersectionLeft b sourcePacketIntersectionRight
    split_ifs with hxMinus
    · apply max_le
      · exact hbLower
      · apply Real.log_le_log (div_pos hxMinus hX)
        exact div_le_div_of_nonneg_right (by linarith) hX.le
    · have hlogNonneg : 0 ≤ Real.log ((x + H) / X) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hX]
        linarith
      linarith
  refine ⟨haLower, hab, hbUpper, ?_⟩
  intro w hw
  have hupperExp : X * Real.exp w ≤ x + H := by
    have : Real.exp w ≤ Real.exp b := Real.exp_le_exp.mpr hw.2
    rw [hbUpperExp] at this
    simpa [mul_comm] using (le_div_iff₀ hX).mp this
  have hlowerExp : x - H ≤ X * Real.exp w := by
    by_cases hxMinus : 0 < x - H
    · have hlogLower : Real.log ((x - H) / X) ≤ a := by
        simp [a, sourcePacketIntersectionLeft, hxMinus]
      have hwlog : Real.log ((x - H) / X) ≤ w := hlogLower.trans hw.1
      have hexp : (x - H) / X ≤ Real.exp w := by
        rw [← Real.exp_log (div_pos hxMinus hX)]
        exact Real.exp_le_exp.mpr hwlog
      simpa [mul_comm] using (div_le_iff₀ hX).mp hexp
    · have : x - H ≤ 0 := le_of_not_gt hxMinus
      exact this.trans (mul_nonneg hX.le (Real.exp_nonneg w))
  rw [abs_le]
  constructor <;> linarith

theorem sourcePacketAmplitude_eq_zero_of_not_mem_intersection
    {X H x w : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hw : w ∉ Set.Ioc (sourcePacketIntersectionLeft X H x)
      (sourcePacketIntersectionRight X H x)) :
    sourcePacketAmplitude X H x cutoff outer w = 0 := by
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  have hgeom := sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper
  have hab : a ≤ b := by simpa [a, b] using hgeom.2.1
  simp only [Set.mem_Ioc, not_and_or, not_le] at hw
  rcases hw with hwLeft | hwRight
  · by_cases hxMinus : 0 < x - H
    · by_cases hwhich : (-100 : ℝ) ≤ Real.log ((x - H) / X)
      · have ha : a = Real.log ((x - H) / X) := by
          simp [a, sourcePacketIntersectionLeft, hxMinus, max_eq_right hwhich]
        have hwA : w ≤ a := by simpa [a] using le_of_not_gt hwLeft
        have hexp : Real.exp w ≤ (x - H) / X := by
          rw [← Real.exp_log (div_pos hxMinus hX)]
          exact Real.exp_le_exp.mpr (by simpa [ha] using hwA)
        have hnum : X * Real.exp w - x ≤ -H := by
          have := (le_div_iff₀ hX).mp hexp
          linarith
        have hquot : (X * Real.exp w - x) / H ≤ -1 := by
          rw [div_le_iff₀ hH]
          linarith
        have hz := hcutoffSupport _ (by
          rw [abs_of_nonpos (hquot.trans (by norm_num))]
          linarith)
        simp [sourcePacketAmplitude, hz]
      · have ha : a = -100 := by
          have : Real.log ((x - H) / X) ≤ -100 := le_of_not_ge hwhich
          simp [a, sourcePacketIntersectionLeft, hxMinus, max_eq_left this]
        have hwA : w ≤ a := by simpa [a] using le_of_not_gt hwLeft
        have hw100 : w ≤ -100 := by simpa [ha] using hwA
        have hz := houterSupport (w / 100) (by
          rw [abs_of_nonpos (by linarith : w / 100 ≤ 0)]
          linarith)
        simp [sourcePacketAmplitude, hz]
    · have ha : a = -100 := by
        simp [a, sourcePacketIntersectionLeft, hxMinus]
      have hwA : w ≤ a := by simpa [a] using le_of_not_gt hwLeft
      have hw100 : w ≤ -100 := by simpa [ha] using hwA
      have hz := houterSupport (w / 100) (by
        rw [abs_of_nonpos (by linarith : w / 100 ≤ 0)]
        linarith)
      simp [sourcePacketAmplitude, hz]
  · have hxPlus : 0 < x + H := by linarith
    have hexp : (x + H) / X < Real.exp w := by
      rw [← Real.exp_log (div_pos hxPlus hX)]
      exact Real.exp_lt_exp.mpr (by simpa [b, sourcePacketIntersectionRight] using hwRight)
    have hnum : H < X * Real.exp w - x := by
      have := (div_lt_iff₀ hX).mp hexp
      linarith
    have hquot : 1 < (X * Real.exp w - x) / H := by
      rw [lt_div_iff₀ hH]
      linarith
    have hz := hcutoffSupport _ (by
      rw [abs_of_pos (lt_trans (by norm_num) hquot)]
      exact hquot.le)
    simp [sourcePacketAmplitude, hz]

theorem sourceStationaryPacket_eq_onIntersectionWindow
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    sourceStationaryPacket X H x beta t cutoff outer =
      stationaryPacketOn X beta t (sourcePacketAmplitude X H x cutoff outer)
        (sourcePacketIntersectionLeft X H x)
        (sourcePacketIntersectionRight X H x) := by
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  let integrand : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x cutoff outer w
  have hab : a ≤ b := by
    simpa [a, b] using
      (sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper).2.1
  have hindicator : integrand = Set.indicator (Set.Ioc a b) integrand := by
    funext w
    by_cases hw : w ∈ Set.Ioc a b
    · simp [hw]
    · have hz := sourcePacketAmplitude_eq_zero_of_not_mem_intersection
        (X := X) (H := H) (x := x) (cutoff := cutoff) (outer := outer)
        hX hH hHalf hxLower hxUpper hcutoffSupport houterSupport (by simpa [a, b] using hw)
      simp [integrand, hw, hz]
  unfold sourceStationaryPacket stationaryPacketOn
  change (∫ w : ℝ, integrand w) = _
  rw [hindicator, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hab]

theorem sourcePacketAmplitude_intersection_endpoints
    {X H x : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutNeg : cutoff (-1) = 0) (hcutPos : cutoff 1 = 0)
    (hcut'Neg : cutoff' (-1) = 0) (hcut'Pos : cutoff' 1 = 0)
    (houterNeg : outer (-1) = 0) (houter'Neg : outer' (-1) = 0) :
    let a := sourcePacketIntersectionLeft X H x
    let b := sourcePacketIntersectionRight X H x
    sourcePacketAmplitude X H x cutoff outer a = 0 ∧
      sourcePacketAmplitude X H x cutoff outer b = 0 ∧
      sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' a = 0 ∧
      sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' b = 0 := by
  dsimp
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  have hxPlus : 0 < x + H := by linarith
  have hzb : (X * Real.exp b - x) / H = 1 := by
    simp only [b, sourcePacketIntersectionRight]
    rw [Real.exp_log (div_pos hxPlus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  have hright0 : sourcePacketAmplitude X H x cutoff outer b = 0 := by
    simp [sourcePacketAmplitude, hzb, hcutPos]
  have hright1 : sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' b = 0 := by
    simp [sourcePacketAmplitudeDeriv, hzb, hcutPos, hcut'Pos]
  have hleft : sourcePacketAmplitude X H x cutoff outer a = 0 ∧
      sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' a = 0 := by
    by_cases hxMinus : 0 < x - H
    · by_cases hwhich : (-100 : ℝ) ≤ Real.log ((x - H) / X)
      · have ha : a = Real.log ((x - H) / X) := by
          simp [a, sourcePacketIntersectionLeft, hxMinus, max_eq_right hwhich]
        have hza : (X * Real.exp a - x) / H = -1 := by
          rw [ha, Real.exp_log (div_pos hxMinus hX)]
          field_simp [ne_of_gt hX, ne_of_gt hH]
          ring
        constructor
        · simp [sourcePacketAmplitude, hza, hcutNeg]
        · simp [sourcePacketAmplitudeDeriv, hza, hcutNeg, hcut'Neg]
      · have ha : a = -100 := by
          have hle : Real.log ((x - H) / X) ≤ -100 := le_of_not_ge hwhich
          simp [a, sourcePacketIntersectionLeft, hxMinus, max_eq_left hle]
        constructor
        · simp [sourcePacketAmplitude, ha, houterNeg]
        · simp [sourcePacketAmplitudeDeriv, ha, houterNeg, houter'Neg]
    · have ha : a = -100 := by simp [a, sourcePacketIntersectionLeft, hxMinus]
      constructor
      · simp [sourcePacketAmplitude, ha, houterNeg]
      · simp [sourcePacketAmplitudeDeriv, ha, houterNeg, houter'Neg]
  exact ⟨hleft.1, hright0, hleft.2, hright1⟩

/-- The phase separation needed for two integrations by parts remains valid
on the literal intersection interval. -/
theorem stationaryPacketPhase_deriv_lower_on_intersectionWindow
    {X H x beta t D : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hD : D = |t / (2 * Real.pi) + beta * x|)
    (hscale : 4 * |beta| * H ≤ D)
    (hw : w ∈ Set.Icc (sourcePacketIntersectionLeft X H x)
      (sourcePacketIntersectionRight X H x)) :
    3 * D / 4 ≤ |beta * X * Real.exp w + t / (2 * Real.pi)| := by
  have hclose := (sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper).2.2.2 w hw
  have hpert : |beta * (X * Real.exp w - x)| ≤ D / 4 := by
    rw [abs_mul]
    have hm := mul_le_mul_of_nonneg_left hclose (abs_nonneg beta)
    nlinarith
  have htri := abs_sub_abs_le_abs_sub
    (t / (2 * Real.pi) + beta * x)
    (t / (2 * Real.pi) + beta * X * Real.exp w)
  have hrearrange :
      (t / (2 * Real.pi) + beta * x) -
          (t / (2 * Real.pi) + beta * X * Real.exp w) =
        -(beta * (X * Real.exp w - x)) := by ring
  rw [hrearrange, abs_neg] at htri
  rw [show beta * X * Real.exp w + t / (2 * Real.pi) =
      t / (2 * Real.pi) + beta * X * Real.exp w by ring]
  rw [hD]
  linarith

/-- The matching first/second phase-derivative upper bound in the half-range.
The constant changes from `17/4` on the sharp window to `9/2` in the collar. -/
theorem stationaryPacketPhase_exp_deriv_upper_on_intersectionWindow
    {X H x beta w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ Set.Icc (sourcePacketIntersectionLeft X H x)
      (sourcePacketIntersectionRight X H x)) :
    |beta * X * Real.exp w| ≤ 9 * |beta| * X / 2 := by
  have hclose :=
    (sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper).2.2.2 w hw
  have hxe : X * Real.exp w ≤ x + H := by
    rw [abs_le] at hclose
    linarith
  have hxH : x + H ≤ 9 * X / 2 := by linarith
  rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
  calc
    |beta| * X * Real.exp w = |beta| * (X * Real.exp w) := by ring
    _ ≤ |beta| * (9 * X / 2) :=
      mul_le_mul_of_nonneg_left (hxe.trans hxH) (abs_nonneg beta)
    _ = 9 * |beta| * X / 2 := by ring

theorem sourcePacketIntersection_length_le
    {X H x : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    sourcePacketIntersectionRight X H x - sourcePacketIntersectionLeft X H x ≤ 200 := by
  have hg := sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper
  linarith [hg.1, hg.2.2.1]

theorem integral_norm_sourcePacketAmplitude_on_intersection_le
    {X H x : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer) :
    let a := sourcePacketIntersectionLeft X H x
    let b := sourcePacketIntersectionRight X H x
    (∫ w : ℝ in a..b, ‖sourcePacketAmplitude X H x cutoff outer w‖) ≤ 600 := by
  dsimp
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  have hg := sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper
  have hab : a ≤ b := by simpa [a, b] using hg.2.1
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖sourcePacketAmplitude X H x cutoff outer w‖ ≤ 3 := by
    intro w hw
    have hclose : |X * Real.exp w - x| ≤ H := by
      exact hg.2.2.2 w (by simpa [a, b] using hw)
    have hexpFive : Real.exp w ≤ 5 := by
      have hxe : X * Real.exp w ≤ x + H := by rw [abs_le] at hclose; linarith
      have hexpr : Real.exp w ≤ (x + H) / X :=
        (le_div_iff₀ hX).2 (by simpa [mul_comm] using hxe)
      have hratio : (x + H) / X ≤ 5 := by rw [div_le_iff₀ hX]; linarith
      linarith
    have hsquare : Real.exp (w / 2) ^ 2 = Real.exp w := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hew : Real.exp (w / 2) ≤ 3 := by
      nlinarith [Real.exp_pos (w / 2)]
    unfold sourcePacketAmplitude
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          |outer (w / 100)| ≤ 3 * 1 * 1 := by
        gcongr
        · exact hcutoffBound _
        · exact houterBound _
      _ = 3 := by norm_num
  have hi : IntervalIntegrable
      (fun w ↦ ‖sourcePacketAmplitude X H x cutoff outer w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    unfold sourcePacketAmplitude
    fun_prop
  have hlen : b - a ≤ 200 := by
    simpa [a, b] using sourcePacketIntersection_length_le hX hH hHalf hxLower hxUpper
  calc
    (∫ w : ℝ in a..b, ‖sourcePacketAmplitude X H x cutoff outer w‖) ≤
        ∫ _w : ℝ in a..b, (3 : ℝ) :=
      intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hpoint
    _ = 3 * (b - a) := by simp; ring
    _ ≤ 3 * 200 := mul_le_mul_of_nonneg_left hlen (by norm_num)
    _ = 600 := by norm_num

theorem integral_norm_sourcePacketAmplitudeDeriv_on_intersection_le
    {X H x D1 B1 : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (hcutoff'Cont : Continuous cutoff') (houter'Cont : Continuous outer')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1) :
    let a := sourcePacketIntersectionLeft X H x
    let b := sourcePacketIntersectionRight X H x
    (∫ w : ℝ in a..b,
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖) ≤
      300 + 6 * B1 + 3 * D1 := by
  dsimp
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  let z : ℝ → ℝ := fun w ↦ (X * Real.exp w - x) / H
  let r : ℝ → ℝ := fun w ↦ X * Real.exp w / H
  have hg := sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper
  have hab : a ≤ b := by simpa [a, b] using hg.2.1
  have hxPlus : 0 < x + H := by linarith
  have hzDeriv : ∀ w, HasDerivAt z (r w) w := by
    intro w
    unfold z r
    convert ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H
      using 1 <;> ring
  have hzCont : Continuous z := by unfold z; fun_prop
  have hrNonneg : ∀ w, 0 ≤ r w := by intro w; unfold r; positivity
  have hchange :
      (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) =
        ∫ y : ℝ in z a..z b, |cutoff' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := a) (b := b) (f := z) (f' := r)
        (g := fun y ↦ |cutoff' y|) hzCont.continuousOn
        (fun w _ ↦ hzDeriv w) (fun w _ ↦ hrNonneg w))
  have hzb : z b = 1 := by
    unfold z b sourcePacketIntersectionRight
    rw [Real.exp_log (div_pos hxPlus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  have hzaLe : z a ≤ 1 := by
    have haMem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hclose := hg.2.2.2 a (by simpa [a, b] using haMem)
    unfold z
    rw [abs_le] at hclose
    rw [div_le_iff₀ hH]
    linarith
  have hI1 : (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) ≤ D1 := by
    rw [hchange, hzb]
    exact (MAPMRTVanDerCorput.intervalIntegral_le_integral_of_nonneg hzaLe
      hcutoff'Int (fun y ↦ abs_nonneg _)).trans hD1
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hD1nonneg : 0 ≤ D1 :=
    le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hiI1 : IntervalIntegrable (fun w ↦ |cutoff' (z w)| * r w)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖ ≤
        3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100 := by
    intro w hw
    have hclose := hg.2.2.2 w (by simpa [a, b] using hw)
    have hexpFive : Real.exp w ≤ 5 := by
      have hxe : X * Real.exp w ≤ x + H := by rw [abs_le] at hclose; linarith
      have hexpr : Real.exp w ≤ (x + H) / X :=
        (le_div_iff₀ hX).2 (by simpa [mul_comm] using hxe)
      have hratio : (x + H) / X ≤ 5 := by rw [div_le_iff₀ hX]; linarith
      linarith
    have hsquare : Real.exp (w / 2) ^ 2 = Real.exp w := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hew : Real.exp (w / 2) ≤ 3 := by nlinarith [Real.exp_pos (w / 2)]
    have hrn := hrNonneg w
    have h0 := hcutoffBound ((X * Real.exp w - x) / H)
    have ho0 := houterBound (w / 100)
    have ho1 := houter'Bound (w / 100)
    have ht1 :
        ‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) * (outer (w / 100) : ℂ)‖ ≤
          3 / 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (Real.exp_pos _)]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        Real.exp (w / 2) / 2 * |cutoff ((X * Real.exp w - x) / H)| *
            |outer (w / 100)| ≤ 3 / 2 * 1 * 1 := by gcongr
        _ = 3 / 2 := by ring
    have ht2 :
        ‖(Real.exp (w / 2) : ℂ) *
          ((cutoff' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) : ℝ) : ℂ) * (outer (w / 100) : ℂ)‖ ≤
          3 * (|cutoff' (z w)| * r w) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_mul]
      rw [abs_of_nonneg hrn]
      unfold z r
      calc
        Real.exp (w / 2) *
            (|cutoff' ((X * Real.exp w - x) / H)| * (X * Real.exp w / H)) *
              |outer (w / 100)| ≤
            3 * (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) * 1 := by gcongr
        _ = 3 * (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) := by ring
    have ht3 :
        ‖(Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            ((outer' (w / 100) / 100 : ℝ) : ℂ)‖ ≤ 3 * B1 / 100 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_div]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 100)]
      calc
        Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
            (|outer' (w / 100)| / 100) ≤ 3 * 1 * (B1 / 100) := by gcongr
        _ = 3 * B1 / 100 := by ring
    unfold sourcePacketAmplitudeDeriv
    exact (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ht1 ht2)) ht3)
  have hiDeriv : IntervalIntegrable (fun w ↦
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    unfold sourcePacketAmplitudeDeriv
    fun_prop
  have hiMajor : IntervalIntegrable (fun w ↦
      3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hlen : b - a ≤ 200 := by
    simpa [a, b] using sourcePacketIntersection_length_le hX hH hHalf hxLower hxUpper
  calc
    (∫ w : ℝ in a..b,
        ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖) ≤
      ∫ w : ℝ in a..b,
        (3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100) :=
      intervalIntegral.integral_mono_on hab hiDeriv hiMajor hpoint
    _ = (3 / 2 + 3 * B1 / 100) * (b - a) +
        3 * (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) := by
      rw [show (∫ w : ℝ in a..b,
          (3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100)) =
          ∫ w : ℝ in a..b, ((3 / 2 + 3 * B1 / 100) +
            3 * (|cutoff' (z w)| * r w)) by
        exact intervalIntegral.integral_congr (fun w _ ↦ by ring)]
      rw [intervalIntegral.integral_add intervalIntegrable_const (hiI1.const_mul 3),
        intervalIntegral.integral_const_mul]
      simp
      ring
    _ ≤ (3 / 2 + 3 * B1 / 100) * 200 + 3 * D1 := by gcongr
    _ = 300 + 6 * B1 + 3 * D1 := by ring


theorem integral_norm_sourcePacketAmplitudeSecond_on_intersection_le
    {X H x D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hCollar : X / 4 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'') (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    let a := sourcePacketIntersectionLeft X H x
    let b := sourcePacketIntersectionRight X H x
    (∫ w : ℝ in a..b,
      ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff'' outer outer' outer'' w‖) ≤
      (X / H) * (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2) := by
  dsimp
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  let z : ℝ → ℝ := fun w ↦ (X * Real.exp w - x) / H
  let r : ℝ → ℝ := fun w ↦ X * Real.exp w / H
  have hg := sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper
  have hab : a ≤ b := by simpa [a, b] using hg.2.1
  have hxPlus : 0 < x + H := by linarith
  have hzDeriv : ∀ w, HasDerivAt z (r w) w := by
    intro w
    unfold z r
    convert ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H using 1 <;> ring
  have hrNonneg : ∀ w, 0 ≤ r w := by intro w; unfold r; positivity
  have hzCont : Continuous z := by unfold z; fun_prop
  have hchange1 : (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) =
      ∫ y : ℝ in z a..z b, |cutoff' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := a) (b := b) (f := z) (f' := r) (g := fun y ↦ |cutoff' y|)
        hzCont.continuousOn (fun w _ ↦ hzDeriv w) (fun w _ ↦ hrNonneg w))
  have hchange2 : (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w) =
      ∫ y : ℝ in z a..z b, |cutoff'' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := a) (b := b) (f := z) (f' := r) (g := fun y ↦ |cutoff'' y|)
        hzCont.continuousOn (fun w _ ↦ hzDeriv w) (fun w _ ↦ hrNonneg w))
  have hzb : z b = 1 := by
    unfold z b sourcePacketIntersectionRight
    rw [Real.exp_log (div_pos hxPlus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  have hzaLe : z a ≤ 1 := by
    have haMem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hclose := hg.2.2.2 a (by simpa [a, b] using haMem)
    unfold z
    rw [abs_le] at hclose
    rw [div_le_iff₀ hH]
    linarith
  have hI1 : (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) ≤ D1 := by
    rw [hchange1, hzb]
    exact (MAPMRTVanDerCorput.intervalIntegral_le_integral_of_nonneg hzaLe
      hcutoff'Int (fun y ↦ abs_nonneg _)).trans hD1
  have hI2base : (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w) ≤ D2 := by
    rw [hchange2, hzb]
    exact (MAPMRTVanDerCorput.intervalIntegral_le_integral_of_nonneg hzaLe
      hcutoff''Int (fun y ↦ abs_nonneg _)).trans hD2
  have hrUpper : ∀ w ∈ Set.Icc a b, r w ≤ 9 * X / (2 * H) := by
    intro w hw
    have hclose := hg.2.2.2 w (by simpa [a, b] using hw)
    have hxe : X * Real.exp w ≤ x + H := by rw [abs_le] at hclose; linarith
    unfold r
    apply (div_le_div_iff₀ hH (mul_pos (by norm_num) hH)).2
    have hxH : x + H ≤ 9 * X / 2 := by linarith
    nlinarith
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffSecond y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterSecond y).continuousAt)
  have hiI1 : IntervalIntegrable (fun w ↦ |cutoff' (z w)| * r w) volume a b := by
    apply ContinuousOn.intervalIntegrable; apply Continuous.continuousOn; fun_prop
  have hiI2 : IntervalIntegrable (fun w ↦ |cutoff'' (z w)| * r w ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable; apply Continuous.continuousOn; fun_prop
  have hiI2base : IntervalIntegrable (fun w ↦ |cutoff'' (z w)| * r w) volume a b := by
    apply ContinuousOn.intervalIntegrable; apply Continuous.continuousOn; fun_prop
  have hI2 : (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w ^ 2) ≤
      (9 * X / (2 * H)) * D2 := by
    calc
      (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w ^ 2) ≤
          ∫ w : ℝ in a..b, (9 * X / (2 * H)) * (|cutoff'' (z w)| * r w) := by
        apply intervalIntegral.integral_mono_on hab hiI2
          (hiI2base.const_mul (9 * X / (2 * H)))
        intro w hw
        have hru := hrUpper w hw
        have hn := abs_nonneg (cutoff'' (z w))
        have hrn := hrNonneg w
        calc
          |cutoff'' (z w)| * r w ^ 2 = (|cutoff'' (z w)| * r w) * r w := by ring
          _ ≤ (|cutoff'' (z w)| * r w) * (9 * X / (2 * H)) :=
            mul_le_mul_of_nonneg_left hru (mul_nonneg hn hrn)
          _ = (9 * X / (2 * H)) * (|cutoff'' (z w)| * r w) := by ring
      _ = (9 * X / (2 * H)) * (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w) := by
        exact intervalIntegral.integral_const_mul _ _
      _ ≤ (9 * X / (2 * H)) * D2 := mul_le_mul_of_nonneg_left hI2base (by positivity)
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'' w‖ ≤
        3 / 4 + 6 * (|cutoff' (z w)| * r w) +
          3 * (|cutoff'' (z w)| * r w ^ 2) +
          3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
          3 * B2 / 10000 := by
    intro w hw
    have hew : Real.exp (w / 2) ≤ 3 := by
      have hexpUpper : Real.exp w ≤ (x + H) / X := by
        rw [← Real.exp_log (div_pos hxPlus hX)]
        exact Real.exp_le_exp.mpr hw.2
      have hratio : (x + H) / X ≤ 5 := by
        rw [div_le_iff₀ hX]
        linarith
      have hsquare : Real.exp (w / 2) ^ 2 = Real.exp w := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      nlinarith [Real.exp_pos (w / 2)]
    have h0 := hcutoffBound ((X * Real.exp w - x) / H)
    have ho0 := houterBound (w / 100)
    have ho1 := houter'Bound (w / 100)
    have ho2 := houter''Bound (w / 100)
    have hrn := hrNonneg w
    have ht1 :
        ‖((Real.exp (w / 2) / 4 : ℝ) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) * (outer (w / 100) : ℂ)‖ ≤
          3 / 4 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_div, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc
        Real.exp (w / 2) / 4 * |cutoff ((X * Real.exp w - x) / H)| *
            |outer (w / 100)| ≤ 3 / 4 * 1 * 1 := by gcongr
        _ = 3 / 4 := by ring
    have ht2 :
        ‖2 * (Real.exp (w / 2) : ℂ) *
          ((cutoff' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) : ℝ) : ℂ) * (outer (w / 100) : ℂ)‖ ≤
          6 * (|cutoff' (z w)| * r w) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_mul]
      norm_num
      rw [abs_of_nonneg hrn]
      unfold z r
      calc
        2 * Real.exp (w / 2) *
            (|cutoff' ((X * Real.exp w - x) / H)| * (X * Real.exp w / H)) *
              |outer (w / 100)| ≤
            2 * 3 * (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) * 1 := by
          gcongr
        _ = 6 * (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) := by ring
    have ht3 :
        ‖(Real.exp (w / 2) : ℂ) *
          ((cutoff'' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) ^ 2 : ℝ) : ℂ) * (outer (w / 100) : ℂ)‖ ≤
          3 * (|cutoff'' (z w)| * r w ^ 2) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_mul, abs_pow]
      unfold z r
      calc
        Real.exp (w / 2) *
            (|cutoff'' ((X * Real.exp w - x) / H)| *
              |X * Real.exp w / H| ^ 2) * |outer (w / 100)| ≤
            3 * (|cutoff'' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H) ^ 2) * 1 := by
          rw [abs_of_nonneg hrn]
          gcongr
        _ = 3 * (|cutoff'' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H) ^ 2) := by ring
    have ht4 :
        ‖(Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            ((outer' (w / 100) / 100 : ℝ) : ℂ)‖ ≤ 3 * B1 / 100 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_div]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 100)]
      calc
        Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
            (|outer' (w / 100)| / 100) ≤ 3 * 1 * (B1 / 100) := by gcongr
        _ = 3 * B1 / 100 := by ring
    have ht5 :
        ‖2 * (Real.exp (w / 2) : ℂ) *
          ((cutoff' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) : ℝ) : ℂ) *
              ((outer' (w / 100) / 100 : ℝ) : ℂ)‖ ≤
          6 * B1 / 100 * (|cutoff' (z w)| * r w) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_mul, abs_div]
      norm_num
      rw [abs_of_pos hX, abs_of_pos hH]
      unfold z r
      calc
        2 * Real.exp (w / 2) *
            (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) * (|outer' (w / 100)| / 100) ≤
            2 * 3 *
              (|cutoff' ((X * Real.exp w - x) / H)| *
                (X * Real.exp w / H)) * (B1 / 100) := by gcongr
        _ = 6 * B1 / 100 *
            (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) := by ring
    have ht6 :
        ‖(Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            ((outer'' (w / 100) / 10000 : ℝ) : ℂ)‖ ≤ 3 * B2 / 10000 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_div]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 10000)]
      calc
        Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
            (|outer'' (w / 100)| / 10000) ≤ 3 * 1 * (B2 / 10000) := by gcongr
        _ = 3 * B2 / 10000 := by ring
    unfold sourcePacketAmplitudeSecond
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add ht1 ht2)) ht3)) ht4)) ht5)) ht6)

  have hsecondCont : Continuous
      (sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff'' outer outer' outer'') := by
    unfold sourcePacketAmplitudeSecond
    fun_prop
  have hiSecondNorm : IntervalIntegrable (fun w ↦
      ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff'' outer outer' outer'' w‖)
      volume a b := hsecondCont.norm.continuousOn.intervalIntegrable
  have hmajorInt : IntervalIntegrable (fun w ↦
      3 / 4 + 6 * (|cutoff' (z w)| * r w) +
        3 * (|cutoff'' (z w)| * r w ^ 2) +
        3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
        3 * B2 / 10000) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg (outer'' 0)) (houter''Bound 0)
  have hD1nonneg : 0 ≤ D1 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hD2nonneg : 0 ≤ D2 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD2
  have hlen : b - a ≤ 200 := by
    simpa [a, b] using sourcePacketIntersection_length_le hX hH hHalf hxLower hxUpper
  have hraw : (∫ w : ℝ in a..b,
      ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff'' outer outer' outer'' w‖) ≤
      (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * 200 +
        (6 + 6 * B1 / 100) * D1 + 3 * ((9 * X / (2 * H)) * D2) := by
    calc
      _ ≤ ∫ w : ℝ in a..b,
          (3 / 4 + 6 * (|cutoff' (z w)| * r w) +
            3 * (|cutoff'' (z w)| * r w ^ 2) +
            3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
            3 * B2 / 10000) :=
        intervalIntegral.integral_mono_on hab hiSecondNorm hmajorInt hpoint
      _ = (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * (b - a) +
          (6 + 6 * B1 / 100) * (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) +
          3 * (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w ^ 2) := by
        rw [show (∫ w : ℝ in a..b,
          (3 / 4 + 6 * (|cutoff' (z w)| * r w) +
            3 * (|cutoff'' (z w)| * r w ^ 2) + 3 * B1 / 100 +
            6 * B1 / 100 * (|cutoff' (z w)| * r w) + 3 * B2 / 10000)) =
          ∫ w : ℝ in a..b, ((3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) +
            ((6 + 6 * B1 / 100) * (|cutoff' (z w)| * r w) +
              3 * (|cutoff'' (z w)| * r w ^ 2))) by
            exact intervalIntegral.integral_congr (fun w _ ↦ by ring)]
        rw [intervalIntegral.integral_add intervalIntegrable_const
              ((hiI1.const_mul _).add (hiI2.const_mul _)),
            intervalIntegral.integral_add (hiI1.const_mul _) (hiI2.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        simp
        ring
      _ ≤ _ := by gcongr
  have hRlow : 2 ≤ X / H := by rw [le_div_iff₀ hH]; linarith
  have hRpos : 0 < X / H := div_pos hX hH
  calc
    _ ≤ _ := hraw
    _ ≤ (X / H) * (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2) := by
      have hB1D1 : 0 ≤ B1 * D1 := mul_nonneg hB1 hD1nonneg
      have hc :
          (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * 200 ≤
            (X / H) * (100 + 10 * B1 + B2) := by
        nlinarith [mul_nonneg hRpos.le hB1, mul_nonneg hRpos.le hB2]
      have hd1 : (6 + 6 * B1 / 100) * D1 ≤
          (X / H) * (10 * (1 + B1) * D1) := by
        nlinarith [mul_nonneg hRpos.le hD1nonneg,
          mul_nonneg hRpos.le hB1D1]
      have hd2 : 3 * ((9 * X / (2 * H)) * D2) ≤
          (X / H) * (14 * D2) := by
        have hratioEq : 9 * X / (2 * H) = (9 / 2) * (X / H) := by
          field_simp [ne_of_gt hH]
        rw [hratioEq]
        have hRD : 0 ≤ (X / H) * D2 := mul_nonneg hRpos.le hD2nonneg
        nlinarith only [hRD]
      calc
        (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * 200 +
            (6 + 6 * B1 / 100) * D1 + 3 * ((9 * X / (2 * H)) * D2) ≤
          (X / H) * (100 + 10 * B1 + B2) +
            (X / H) * (10 * (1 + B1) * D1) +
              (X / H) * (14 * D2) := by linarith
        _ = (X / H) *
            (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2) := by ring

#print axioms integral_norm_sourcePacketAmplitudeSecond_on_intersection_le

#print axioms sourceStationaryPacket_eq_onIntersectionWindow
#print axioms sourcePacketAmplitude_intersection_endpoints
#print axioms stationaryPacketPhase_deriv_lower_on_intersectionWindow
#print axioms stationaryPacketPhase_exp_deriv_upper_on_intersectionWindow
#print axioms integral_norm_sourcePacketAmplitude_on_intersection_le
#print axioms integral_norm_sourcePacketAmplitudeDeriv_on_intersection_le

end
end MAPMRTSourcePacketOuterIntersection
