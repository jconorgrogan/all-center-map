import MRTSourcePacketAmplitudeC2Budget

/-! The remaining literal amplitude `L¹` budgets for equation (84). -/

namespace MAPMRTSourcePacketAmplitudeBudgets

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTVanDerCorput

noncomputable section

theorem integral_norm_sourcePacketAmplitude_le
    {X H x : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (houter : ∀ y, |outer y| ≤ 1)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer) :
    let a := Real.log ((x - H) / X)
    let b := Real.log ((x + H) / X)
    (∫ w : ℝ in a..b, ‖sourcePacketAmplitude X H x cutoff outer w‖) ≤
      24 * H / X := by
  dsimp
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
  have hxMinus : 0 < x - H := by linarith
  have hxPlus : 0 < x + H := by linarith
  have hab : a ≤ b := by
    unfold a b
    apply Real.log_le_log (div_pos hxMinus hX)
    exact div_le_div_of_nonneg_right (by linarith) hX.le
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖sourcePacketAmplitude X H x cutoff outer w‖ ≤ 3 := by
    intro w hw
    exact norm_sourcePacketAmplitude_le_three hX hH.le hHquarter hxLower hxUpper
      (by simpa [sourcePacketWindow, a, b] using hw) hcutoff houter
  have hi : IntervalIntegrable
      (fun w ↦ ‖sourcePacketAmplitude X H x cutoff outer w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    unfold sourcePacketAmplitude
    fun_prop
  have hlen := sourcePacketWindow_length_le hX hH.le hHquarter hxLower
  have hlen' : b - a ≤ 8 * H / X := by
    have : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [← abs_of_nonneg this]
    simpa [a, b] using hlen
  calc
    (∫ w : ℝ in a..b, ‖sourcePacketAmplitude X H x cutoff outer w‖) ≤
        ∫ _w : ℝ in a..b, (3 : ℝ) :=
      intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hpoint
    _ = 3 * (b - a) := by simp; ring
    _ ≤ 3 * (8 * H / X) := mul_le_mul_of_nonneg_left hlen' (by norm_num)
    _ = 24 * H / X := by ring

theorem integral_norm_sourcePacketAmplitudeDeriv_on_cutoffWindow_le
    {X H x D1 B1 : ℝ}
    {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outer')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1) :
    let a := Real.log ((x - H) / X)
    let b := Real.log ((x + H) / X)
    (∫ w : ℝ in a..b,
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖) ≤
      10 * (1 + B1) * (1 + D1) := by
  dsimp
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
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
    rw [hchange, hza, hzb]
    exact (intervalIntegral_le_integral_of_nonneg (by norm_num)
      hcutoff'Int (fun y ↦ abs_nonneg _)).trans hD1
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hiI1 : IntervalIntegrable (fun w ↦ |cutoff' (z w)| * r w)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hD1nonneg : 0 ≤ D1 :=
    le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖ ≤
        3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100 := by
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
    have hrn := hrNonneg w
    have h0 := hcutoffBound ((X * Real.exp w - x) / H)
    have ho0 := houterBound (w / 100)
    have ho1 := houter'Bound (w / 100)
    have ht1 :
        ‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) * (outer (w / 100) : ℂ)‖ ≤
          3 / 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_div, abs_of_pos (Real.exp_pos _)]
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
            (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) * |outer (w / 100)| ≤
            3 * (|cutoff' ((X * Real.exp w - x) / H)| *
              (X * Real.exp w / H)) * 1 := by
          gcongr
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
            (|outer' (w / 100)| / 100) ≤ 3 * 1 * (B1 / 100) := by
          gcongr
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
  have hlen := sourcePacketWindow_length_le hX hH.le hHquarter hxLower
  have hlen' : b - a ≤ 8 * H / X := by
    have : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [← abs_of_nonneg this]
    simpa [a, b] using hlen
  have hmajorEq :
      (∫ w : ℝ in a..b,
        (3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100)) =
        (3 / 2 + 3 * B1 / 100) * (b - a) +
          3 * (∫ w : ℝ in a..b, |cutoff' (z w)| * r w) := by
    calc
      _ = ∫ w : ℝ in a..b,
          ((3 / 2 + 3 * B1 / 100) + 3 * (|cutoff' (z w)| * r w)) := by
        exact intervalIntegral.integral_congr (fun w _ ↦ by ring)
      _ = (∫ _w : ℝ in a..b, (3 / 2 + 3 * B1 / 100)) +
          ∫ w : ℝ in a..b, 3 * (|cutoff' (z w)| * r w) :=
        intervalIntegral.integral_add intervalIntegrable_const (hiI1.const_mul 3)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        simp
        ring
  have hiMajor : IntervalIntegrable (fun w ↦
      (3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    fun_prop
  calc
    (∫ w : ℝ in a..b,
        ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖) ≤
        ∫ w : ℝ in a..b,
          (3 / 2 + 3 * (|cutoff' (z w)| * r w) + 3 * B1 / 100) := by
      exact intervalIntegral.integral_mono_on hab hiDeriv
        hiMajor hpoint
    _ = _ := hmajorEq
    _ ≤ (3 / 2 + 3 * B1 / 100) * (8 * H / X) + 3 * D1 := by
      gcongr
    _ ≤ 10 * (1 + B1) * (1 + D1) := by
      have hratio : H / X ≤ 1 / 4 := by
        rw [div_le_iff₀ hX]
        nlinarith
      have hconst : (3 / 2 + 3 * B1 / 100) * (8 * H / X) ≤
          3 + 3 * B1 / 50 := by
        calc
          (3 / 2 + 3 * B1 / 100) * (8 * H / X) =
              (8 * (3 / 2 + 3 * B1 / 100)) * (H / X) := by ring
          _ ≤ (8 * (3 / 2 + 3 * B1 / 100)) * (1 / 4) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = 3 + 3 * B1 / 50 := by ring
      nlinarith [mul_nonneg hB1 hD1nonneg]

end
end MAPMRTSourcePacketAmplitudeBudgets
