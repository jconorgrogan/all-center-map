import MRTSourcePacketAmplitudeC2

/-! The manuscript `O(X/H)` BV budget for the twice differentiated packet amplitude. -/

namespace MAPMRTSourcePacketAmplitudeC2Budget

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTVanDerCorput
open MAPMRTSourcePacketAmplitudeC2

noncomputable section

/-- The exact cutoff-window `L¹` budget for the second amplitude derivative.
The displayed constant is deliberately generous; its dependence is only on
the fixed smooth cutoffs, while the parameter dependence is exactly `X/H`. -/
theorem integral_norm_sourcePacketAmplitudeSecond_le
    {X H x D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    let a := Real.log ((x - H) / X)
    let b := Real.log ((x + H) / X)
    (∫ w : ℝ in a..b,
      ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'' w‖) ≤
      (X / H) * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2) := by
  dsimp
  let a : ℝ := Real.log ((x - H) / X)
  let b : ℝ := Real.log ((x + H) / X)
  let z : ℝ → ℝ := fun w ↦ (X * Real.exp w - x) / H
  let r : ℝ → ℝ := fun w ↦ X * Real.exp w / H
  have hxMinus : 0 < x - H := by linarith
  have hxPlus : 0 < x + H := by linarith
  have hab : a ≤ b := by
    unfold a b
    apply Real.log_le_log (div_pos hxMinus hX)
    exact div_le_div_of_nonneg_right (by linarith) hX.le
  have hzDeriv : ∀ w, HasDerivAt z (r w) w := by
    intro w
    unfold z r
    convert ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H
      using 1 <;> ring
  have hrNonneg : ∀ w, 0 ≤ r w := by intro w; unfold r; positivity
  have hzCont : Continuous z := by unfold z; fun_prop
  have hchange1 :
      (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) =
        ∫ y : ℝ in z a..z b, |cutoff' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := a) (b := b) (f := z) (f' := r)
        (g := fun y ↦ |cutoff' y|) hzCont.continuousOn
        (fun w _ ↦ hzDeriv w) (fun w _ ↦ hrNonneg w))
  have hchange2 :
      (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w) =
        ∫ y : ℝ in z a..z b, |cutoff'' y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := a) (b := b) (f := z) (f' := r)
        (g := fun y ↦ |cutoff'' y|) hzCont.continuousOn
        (fun w _ ↦ hzDeriv w) (fun w _ ↦ hrNonneg w))
  have hza : z a = -1 := by
    unfold z a
    rw [Real.exp_log (div_pos hxMinus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  have hzb : z b = 1 := by
    unfold z b
    rw [Real.exp_log (div_pos hxPlus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  have hI1 : (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) ≤ D1 := by
    rw [hchange1, hza, hzb]
    exact (intervalIntegral_le_integral_of_nonneg (by norm_num)
      hcutoff'Int (fun y ↦ abs_nonneg _)).trans hD1
  have hI2base : (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w) ≤ D2 := by
    rw [hchange2, hza, hzb]
    exact (intervalIntegral_le_integral_of_nonneg (by norm_num)
      hcutoff''Int (fun y ↦ abs_nonneg _)).trans hD2
  have hrUpper : ∀ w ∈ Set.Icc a b, r w ≤ 17 * X / (4 * H) := by
    intro w hw
    have hexpUpper : Real.exp w ≤ (x + H) / X := by
      rw [← Real.exp_log (div_pos hxPlus hX)]
      exact Real.exp_le_exp.mpr hw.2
    unfold r
    have hxe : X * Real.exp w ≤ x + H := by
      simpa [mul_comm] using (le_div_iff₀ hX).mp hexpUpper
    apply (div_le_div_iff₀ hH (mul_pos (by norm_num) hH)).2
    have hxH : x + H ≤ 17 * X / 4 := by linarith
    nlinarith
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffSecond y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterSecond y).continuousAt)
  have hiI2 : IntervalIntegrable (fun w ↦ |cutoff'' (z w)| * r w ^ 2)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hiI2base : IntervalIntegrable (fun w ↦ |cutoff'' (z w)| * r w)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hI2 : (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w ^ 2) ≤
      (17 * X / (4 * H)) * D2 := by
    calc
      (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w ^ 2) ≤
          ∫ w : ℝ in a..b,
            (17 * X / (4 * H)) * (|cutoff'' (z w)| * r w) := by
        apply intervalIntegral.integral_mono_on hab hiI2
          (hiI2base.const_mul (17 * X / (4 * H)))
        intro w hw
        have hru := hrUpper w hw
        have hn := abs_nonneg (cutoff'' (z w))
        have hrn := hrNonneg w
        calc
          |cutoff'' (z w)| * r w ^ 2 =
              (|cutoff'' (z w)| * r w) * r w := by ring
          _ ≤ (|cutoff'' (z w)| * r w) * (17 * X / (4 * H)) :=
            mul_le_mul_of_nonneg_left hru (mul_nonneg hn hrn)
          _ = (17 * X / (4 * H)) * (|cutoff'' (z w)| * r w) := by ring
      _ = (17 * X / (4 * H)) *
          (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w) := by
        exact intervalIntegral.integral_const_mul _ _
      _ ≤ (17 * X / (4 * H)) * D2 := by
        exact mul_le_mul_of_nonneg_left hI2base (by positivity)
  have hlength := sourcePacketWindow_length_le hX hH.le hHquarter hxLower
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
      have hratio : (x + H) / X ≤ 17 / 4 := by
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
      (sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'') := by
    unfold sourcePacketAmplitudeSecond
    fun_prop
  have hiSecondNorm : IntervalIntegrable (fun w ↦
      ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'' w‖) volume a b :=
    hsecondCont.norm.continuousOn.intervalIntegrable
  have hiI1 : IntervalIntegrable (fun w ↦ |cutoff' (z w)| * r w)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hmajorInt : IntervalIntegrable (fun w ↦
      3 / 4 + 6 * (|cutoff' (z w)| * r w) +
        3 * (|cutoff'' (z w)| * r w ^ 2) +
        3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
        3 * B2 / 10000) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hD1nonneg : 0 ≤ D1 :=
    le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hD2nonneg : 0 ≤ D2 :=
    le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD2
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg (outer'' 0)) (houter''Bound 0)
  have hC0 : 0 ≤ 3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000 := by positivity
  have hC1 : 0 ≤ 6 + 6 * B1 / 100 := by positivity
  have hlength' : b - a ≤ 8 * H / X := by
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [← abs_of_nonneg hba]
    simpa [a, b] using hlength
  have hmajorEq :
      (∫ w : ℝ in a..b,
        (3 / 4 + 6 * (|cutoff' (z w)| * r w) +
          3 * (|cutoff'' (z w)| * r w ^ 2) +
          3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
          3 * B2 / 10000)) =
        (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * (b - a) +
          (6 + 6 * B1 / 100) *
            (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) +
          3 * (∫ w : ℝ in a..b, |cutoff'' (z w)| * r w ^ 2) := by
    calc
      (∫ w : ℝ in a..b,
        (3 / 4 + 6 * (|cutoff' (z w)| * r w) +
          3 * (|cutoff'' (z w)| * r w ^ 2) +
          3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
          3 * B2 / 10000)) =
          ∫ w : ℝ in a..b,
            ((3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) +
              ((6 + 6 * B1 / 100) * (|cutoff' (z w)| * r w) +
                3 * (|cutoff'' (z w)| * r w ^ 2))) := by
        exact intervalIntegral.integral_congr (fun w _ ↦ by ring)
      _ = (∫ _w : ℝ in a..b,
            (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000)) +
          ∫ w : ℝ in a..b,
            ((6 + 6 * B1 / 100) * (|cutoff' (z w)| * r w) +
              3 * (|cutoff'' (z w)| * r w ^ 2)) :=
        intervalIntegral.integral_add intervalIntegrable_const
          ((hiI1.const_mul _).add (hiI2.const_mul _))
      _ = (∫ _w : ℝ in a..b,
            (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000)) +
          ((∫ w : ℝ in a..b,
              (6 + 6 * B1 / 100) * (|cutoff' (z w)| * r w)) +
            ∫ w : ℝ in a..b,
              3 * (|cutoff'' (z w)| * r w ^ 2)) := by
        rw [intervalIntegral.integral_add (hiI1.const_mul _) (hiI2.const_mul _)]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        simp
        ring
  calc
    (∫ w : ℝ in a..b, ‖sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'' w‖) ≤
        ∫ w : ℝ in a..b,
          (3 / 4 + 6 * (|cutoff' (z w)| * r w) +
            3 * (|cutoff'' (z w)| * r w ^ 2) +
            3 * B1 / 100 + 6 * B1 / 100 * (|cutoff' (z w)| * r w) +
            3 * B2 / 10000) :=
      intervalIntegral.integral_mono_on hab hiSecondNorm hmajorInt hpoint
    _ ≤ (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * (8 * H / X) +
        (6 + 6 * B1 / 100) * D1 + 3 * ((17 * X / (4 * H)) * D2) := by
      rw [hmajorEq]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hlength' hC0
        · exact mul_le_mul_of_nonneg_left hI1 hC1
      · exact mul_le_mul_of_nonneg_left hI2 (by norm_num)
    _ ≤ (X / H) * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2) := by
      have hHX : H / X ≤ X / H := by
        rw [div_le_div_iff₀ hX hH]
        nlinarith
      have hOneRatio : 1 ≤ X / H := by
        rw [le_div_iff₀ hH]
        linarith
      have hconstCoeff :
          (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * (8 * H / X) ≤
            (X / H) * (10 + B1 + B2) := by
        calc
          (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000) * (8 * H / X) =
              (8 * (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000)) *
                (H / X) := by ring
          _ ≤ (8 * (3 / 4 + 3 * B1 / 100 + 3 * B2 / 10000)) *
                (X / H) := mul_le_mul_of_nonneg_left hHX (by positivity)
          _ ≤ (10 + B1 + B2) * (X / H) := by
            gcongr
            linarith
          _ = (X / H) * (10 + B1 + B2) := by ring
      have hD1term : (6 + 6 * B1 / 100) * D1 ≤
          (X / H) * (10 * (1 + B1) * D1) := by
        calc
          (6 + 6 * B1 / 100) * D1 ≤ 10 * (1 + B1) * D1 := by
            gcongr
            linarith
          _ ≤ (X / H) * (10 * (1 + B1) * D1) := by
            simpa [one_mul] using mul_le_mul_of_nonneg_right hOneRatio
              (by positivity : 0 ≤ 10 * (1 + B1) * D1)
      have hD2term : 3 * ((17 * X / (4 * H)) * D2) ≤
          (X / H) * (20 * D2) := by
        have hratioEq : 17 * X / (4 * H) = (17 / 4) * (X / H) := by
          field_simp [ne_of_gt hH]
        rw [hratioEq]
        have hprod : 0 ≤ (X / H) * D2 :=
          mul_nonneg (by positivity) hD2nonneg
        calc
          3 * ((17 / 4) * (X / H) * D2) =
              (51 / 4) * ((X / H) * D2) := by ring
          _ ≤ 20 * ((X / H) * D2) :=
            mul_le_mul_of_nonneg_right (by norm_num) hprod
          _ = (X / H) * (20 * D2) := by ring
      calc
        _ ≤ (X / H) * (10 + B1 + B2) +
            (X / H) * (10 * (1 + B1) * D1) +
            (X / H) * (20 * D2) := by gcongr
        _ = _ := by ring

end
end MAPMRTSourcePacketAmplitudeC2Budget
