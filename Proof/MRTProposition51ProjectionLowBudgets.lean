import MRTProposition51ProjectionLowAmplitude
import MRTProposition51ProjectionOneIBP
import MRTVanDerCorput

/-!
# Quantitative budgets for the p. 47 low-frequency amplitude
-/

namespace MAPMRTProposition51ProjectionLowBudgets

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTProposition51ProjectionLowAmplitude

noncomputable section

theorem integral_norm_lowKernelArgument
    {X beta eta : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (u : ℝ) (kernel : ℝ → ℂ) :
    (∫ w : ℝ, ‖kernel (lowKernelArgument X beta eta u w)‖) =
      (2 * Real.pi / lowProjectionScale X beta eta) *
        ∫ v : ℝ, ‖kernel v‖ := by
  let A := lowProjectionScale X beta eta / (2 * Real.pi)
  let g : ℝ → ℝ := fun v ↦ ‖kernel v‖
  let f : ℝ → ℝ := fun y ↦ g ((-A) * y)
  have hscale : 0 < lowProjectionScale X beta eta := by
    unfold lowProjectionScale
    positivity
  have hA : 0 < A := div_pos hscale (by positivity)
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := volume) f (-u)
  have hmul := Measure.integral_comp_mul_left g (-A)
  have hleft : (fun w : ℝ ↦
      ‖kernel (lowKernelArgument X beta eta u w)‖) =
      (fun w : ℝ ↦ f (w + (-u))) := by
    funext w
    simp only [f, g, lowKernelArgument, A]
    congr 2
    ring
  rw [hleft, hshift, hmul]
  simp only [smul_eq_mul, abs_inv, abs_neg, abs_of_pos hA]
  unfold A
  simp only [g]
  field_simp [ne_of_gt hscale, Real.pi_ne_zero]

theorem integrable_norm_lowKernelArgument
    {X beta eta : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (u : ℝ) {kernel : ℝ → ℂ} (hkernel : Integrable kernel) :
    Integrable (fun w : ℝ ↦
      ‖kernel (lowKernelArgument X beta eta u w)‖) := by
  let A := lowProjectionScale X beta eta / (2 * Real.pi)
  let g : ℝ → ℝ := fun v ↦ ‖kernel v‖
  have hscale : 0 < lowProjectionScale X beta eta := by
    unfold lowProjectionScale
    positivity
  have hA : A ≠ 0 := (div_pos hscale (by positivity)).ne'
  have hg : Integrable g := hkernel.norm
  have hscaled : Integrable (fun y : ℝ ↦ g ((-A) * y)) :=
    (integrable_comp_mul_left_iff g (neg_ne_zero.mpr hA)).2 hg
  have hshift := hscaled.comp_add_right (-u)
  apply hshift.congr
  filter_upwards with w
  simp only [g, A, lowKernelArgument]
  congr 2
  ring

theorem norm_lowProjectionAmplitude_le_kernel
    {X H beta eta x u w : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X H x)
    (hcutoff : ∀ y, |cutoff y| ≤ 1) :
    ‖lowProjectionAmplitude X H beta eta x u cutoff kernel w‖ ≤
      3 * ‖kernel (lowKernelArgument X beta eta u w)‖ := by
  have hphysical := norm_sourcePacketAmplitude_le_three
    (cutoff := cutoff) (outerCutoff := fun _ ↦ 1)
    hX hH hHquarter hxLower hxUpper hw hcutoff (by simp)
  have hphysical' : Real.exp (w / 2) *
      |cutoff ((X * Real.exp w - x) / H)| ≤ 3 := by
    simpa [sourcePacketAmplitude, norm_mul, Complex.norm_real, Complex.norm_exp,
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using hphysical
  unfold lowProjectionAmplitude
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  nlinarith [hphysical',
    norm_nonneg (kernel (lowKernelArgument X beta eta u w))]

theorem physical_derivative_factor_le
    {X H x w : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hHquarter : H ≤ X / 4) (hxLower : X / 2 ≤ x)
    (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X H x) :
    X * Real.exp w / H ≤ 17 * X / (4 * H) := by
  have hxPlus : 0 < x + H := by nlinarith
  have hratio : 0 < (x + H) / X := div_pos hxPlus hX
  have hexp : Real.exp w ≤ (x + H) / X := by
    rw [← Real.exp_log hratio]
    exact Real.exp_le_exp.mpr hw.2
  have hXexp : X * Real.exp w ≤ x + H := by
    simpa [mul_comm] using (le_div_iff₀ hX).mp hexp
  rw [show 17 * X / (4 * H) = (17 * X / 4) / H by
    field_simp [hH.ne']]
  exact div_le_div_of_nonneg_right (by nlinarith) hH.le

theorem norm_lowProjectionAmplitudeDeriv_le_kernel
    {X H beta eta x u w Bcut : ℝ}
    {cutoff cutoff' : ℝ → ℝ} {kernel kernel' : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X H x)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (hcutoff' : ∀ y, |cutoff' y| ≤ Bcut) (hBcut : 0 ≤ Bcut) :
    ‖lowProjectionAmplitudeDeriv X H beta eta x u
        cutoff cutoff' kernel kernel' w‖ ≤
      (3 / 2 + 51 * Bcut * X / (4 * H)) *
          ‖kernel (lowKernelArgument X beta eta u w)‖ +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          ‖kernel' (lowKernelArgument X beta eta u w)‖ := by
  have hhalf := exp_half_le_three_of_physical_inside (w := w)
    hX hH.le hHquarter hxUpper (by
      have hxMinus : 0 < x - H := by
        have : X / 4 ≤ x - H := by linarith
        exact lt_of_lt_of_le (by positivity : 0 < X / 4) this
      have hxPlus : 0 < x + H := by linarith
      have ha : 0 < (x - H) / X := div_pos hxMinus hX
      have hb : 0 < (x + H) / X := div_pos hxPlus hX
      have hlower : (x - H) / X ≤ Real.exp w := by
        rw [← Real.exp_log ha]
        exact Real.exp_le_exp.mpr hw.1
      have hupper : Real.exp w ≤ (x + H) / X := by
        rw [← Real.exp_log hb]
        exact Real.exp_le_exp.mpr hw.2
      rw [abs_le]
      constructor
      · have := (div_le_iff₀ hX).mp hlower
        have : x - H ≤ X * Real.exp w := by simpa [mul_comm] using this
        linarith
      · have := (le_div_iff₀ hX).mp hupper
        have : X * Real.exp w ≤ x + H := by simpa [mul_comm] using this
        linarith)
  have hphys := physical_derivative_factor_le hX hH hHquarter hxLower hxUpper hw
  have hcut := hcutoff ((X * Real.exp w - x) / H)
  have hcut' := hcutoff' ((X * Real.exp w - x) / H)
  unfold lowProjectionAmplitudeDeriv
  calc
    ‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          kernel (lowKernelArgument X beta eta u w) *
            (cutoff ((X * Real.exp w - x) / H) : ℂ) +
        (Real.exp (w / 2) : ℂ) *
          ((-(lowProjectionScale X beta eta / (2 * Real.pi)) : ℝ) : ℂ) *
            kernel' (lowKernelArgument X beta eta u w) *
              (cutoff ((X * Real.exp w - x) / H) : ℂ) +
        (Real.exp (w / 2) : ℂ) *
          kernel (lowKernelArgument X beta eta u w) *
            (cutoff' ((X * Real.exp w - x) / H) : ℂ) *
              (((X * Real.exp w) / H : ℝ) : ℂ)‖ ≤
        ‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          kernel (lowKernelArgument X beta eta u w) *
            (cutoff ((X * Real.exp w - x) / H) : ℂ)‖ +
        ‖(Real.exp (w / 2) : ℂ) *
          ((-(lowProjectionScale X beta eta / (2 * Real.pi)) : ℝ) : ℂ) *
            kernel' (lowKernelArgument X beta eta u w) *
              (cutoff ((X * Real.exp w - x) / H) : ℂ)‖ +
        ‖(Real.exp (w / 2) : ℂ) *
          kernel (lowKernelArgument X beta eta u w) *
            (cutoff' ((X * Real.exp w - x) / H) : ℂ) *
              (((X * Real.exp w) / H : ℝ) : ℂ)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (3 / 2 + 51 * Bcut * X / (4 * H)) *
          ‖kernel (lowKernelArgument X beta eta u w)‖ +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          ‖kernel' (lowKernelArgument X beta eta u w)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _), abs_neg, abs_div,
        abs_of_pos hH]
      rw [abs_mul X (Real.exp w), abs_of_pos hX,
        abs_of_pos (Real.exp_pos w)]
      have hK := norm_nonneg (kernel (lowKernelArgument X beta eta u w))
      have hK' := norm_nonneg (kernel' (lowKernelArgument X beta eta u w))
      have hphys0 : 0 ≤ X * Real.exp w / H := by positivity
      have hscale0 : 0 ≤
          |lowProjectionScale X beta eta| / |2 * Real.pi| := by positivity
      have hterm1 :
          Real.exp (w / 2) / |(2 : ℝ)| *
              ‖kernel (lowKernelArgument X beta eta u w)‖ *
                |cutoff ((X * Real.exp w - x) / H)| ≤
            (3 / 2) * ‖kernel (lowKernelArgument X beta eta u w)‖ := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        calc
          Real.exp (w / 2) / 2 *
                ‖kernel (lowKernelArgument X beta eta u w)‖ *
                  |cutoff ((X * Real.exp w - x) / H)| ≤
              3 / 2 * ‖kernel (lowKernelArgument X beta eta u w)‖ * 1 := by
            gcongr
          _ = _ := by ring
      have hterm2 :
          Real.exp (w / 2) *
              (|lowProjectionScale X beta eta| / |2 * Real.pi|) *
                ‖kernel' (lowKernelArgument X beta eta u w)‖ *
                  |cutoff ((X * Real.exp w - x) / H)| ≤
            3 * (|lowProjectionScale X beta eta| / |2 * Real.pi|) *
              ‖kernel' (lowKernelArgument X beta eta u w)‖ := by
        calc
          _ ≤ 3 * (|lowProjectionScale X beta eta| / |2 * Real.pi|) *
                ‖kernel' (lowKernelArgument X beta eta u w)‖ * 1 := by
            gcongr
          _ = _ := by ring
      have hterm3 :
          Real.exp (w / 2) *
              ‖kernel (lowKernelArgument X beta eta u w)‖ *
                |cutoff' ((X * Real.exp w - x) / H)| *
                  (X * Real.exp w / H) ≤
            (51 * Bcut * X / (4 * H)) *
              ‖kernel (lowKernelArgument X beta eta u w)‖ := by
        calc
          _ ≤ 3 * ‖kernel (lowKernelArgument X beta eta u w)‖ *
                Bcut * (17 * X / (4 * H)) := by
            gcongr
          _ = _ := by ring
      calc
        _ ≤ (3 / 2) * ‖kernel (lowKernelArgument X beta eta u w)‖ +
            3 * (|lowProjectionScale X beta eta| / |2 * Real.pi|) *
              ‖kernel' (lowKernelArgument X beta eta u w)‖ +
            (51 * Bcut * X / (4 * H)) *
              ‖kernel (lowKernelArgument X beta eta u w)‖ :=
          add_le_add (add_le_add hterm1 hterm2) hterm3
        _ = (3 / 2 + 51 * Bcut * X / (4 * H)) *
              ‖kernel (lowKernelArgument X beta eta u w)‖ +
            3 * (|lowProjectionScale X beta eta| / |2 * Real.pi|) *
              ‖kernel' (lowKernelArgument X beta eta u w)‖ := by ring

theorem sourcePacketWindow_order
    {X H x : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hHquarter : H ≤ X / 4) (hxLower : X / 2 ≤ x) :
    Real.log ((x - H) / X) ≤ Real.log ((x + H) / X) := by
  have hxMinus : 0 < x - H := by
    have : X / 4 ≤ x - H := by linarith
    exact lt_of_lt_of_le (by positivity : 0 < X / 4) this
  apply Real.log_le_log (div_pos hxMinus hX)
  apply div_le_div_of_nonneg_right _ hX.le
  linarith

theorem interval_integral_norm_lowProjectionAmplitude_le
    {X H beta eta x u : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (hcutoffCont : Continuous cutoff) (hkernelCont : Continuous kernel)
    (hkernelInt : Integrable kernel) :
    (∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
      ‖lowProjectionAmplitude X H beta eta x u cutoff kernel w‖) ≤
      3 * (2 * Real.pi / lowProjectionScale X beta eta) *
        ∫ v : ℝ, ‖kernel v‖ := by
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
  have hab : a ≤ b := sourcePacketWindow_order hX hH hHquarter hxLower
  have hargInt := integrable_norm_lowKernelArgument hX hbeta heta u hkernelInt
  have hmajorInt : IntervalIntegrable
      (fun w : ℝ ↦ 3 * ‖kernel (lowKernelArgument X beta eta u w)‖)
      volume a b := hargInt.const_mul 3 |>.intervalIntegrable
  have hampCont : Continuous
      (lowProjectionAmplitude X H beta eta x u cutoff kernel) := by
    unfold lowProjectionAmplitude lowKernelArgument
    fun_prop
  have hampInt : IntervalIntegrable
      (fun w : ℝ ↦
        ‖lowProjectionAmplitude X H beta eta x u cutoff kernel w‖)
      volume a b := hampCont.norm.intervalIntegrable _ _
  have hmono : (∫ w : ℝ in a..b,
      ‖lowProjectionAmplitude X H beta eta x u cutoff kernel w‖) ≤
      ∫ w : ℝ in a..b,
        3 * ‖kernel (lowKernelArgument X beta eta u w)‖ := by
    apply intervalIntegral.integral_mono_on hab hampInt hmajorInt
    intro w hw
    exact norm_lowProjectionAmplitude_le_kernel hX hH.le hHquarter
      hxLower hxUpper (by simpa [a, b, sourcePacketWindow] using hw) hcutoff
  have hwhole := MAPMRTVanDerCorput.intervalIntegral_le_integral_of_nonneg
    hab hargInt (fun w ↦ norm_nonneg (kernel (lowKernelArgument X beta eta u w)))
  calc
    _ ≤ ∫ w : ℝ in a..b,
        3 * ‖kernel (lowKernelArgument X beta eta u w)‖ := hmono
    _ = 3 * (∫ w : ℝ in a..b,
        ‖kernel (lowKernelArgument X beta eta u w)‖) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 3 * (∫ w : ℝ,
        ‖kernel (lowKernelArgument X beta eta u w)‖) := by gcongr
    _ = _ := by
      rw [integral_norm_lowKernelArgument hX hbeta heta]
      ring

theorem interval_integral_norm_lowProjectionAmplitudeDeriv_le
    {X H beta eta x u Bcut : ℝ}
    {cutoff cutoff' : ℝ → ℝ} {kernel kernel' : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (hcutoff' : ∀ y, |cutoff' y| ≤ Bcut) (hBcut : 0 ≤ Bcut)
    (hcutoffCont : Continuous cutoff) (hcutoff'Cont : Continuous cutoff')
    (hkernelCont : Continuous kernel) (hkernel'Cont : Continuous kernel')
    (hkernelInt : Integrable kernel) (hkernel'Int : Integrable kernel') :
    (∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
      ‖lowProjectionAmplitudeDeriv X H beta eta x u
        cutoff cutoff' kernel kernel' w‖) ≤
      (3 / 2 + 51 * Bcut * X / (4 * H)) *
          (2 * Real.pi / lowProjectionScale X beta eta) *
            (∫ v : ℝ, ‖kernel v‖) +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          (2 * Real.pi / lowProjectionScale X beta eta) *
            (∫ v : ℝ, ‖kernel' v‖) := by
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
  let C0 := 3 / 2 + 51 * Bcut * X / (4 * H)
  let C1 := 3 * |lowProjectionScale X beta eta / (2 * Real.pi)|
  have hab : a ≤ b := sourcePacketWindow_order hX hH hHquarter hxLower
  have harg0 := integrable_norm_lowKernelArgument hX hbeta heta u hkernelInt
  have harg1 := integrable_norm_lowKernelArgument hX hbeta heta u hkernel'Int
  have hC0 : 0 ≤ C0 := by unfold C0; positivity
  have hC1 : 0 ≤ C1 := by unfold C1; positivity
  have hmajorInt : IntervalIntegrable
      (fun w : ℝ ↦ C0 * ‖kernel (lowKernelArgument X beta eta u w)‖ +
        C1 * ‖kernel' (lowKernelArgument X beta eta u w)‖) volume a b :=
    (harg0.const_mul C0).add (harg1.const_mul C1) |>.intervalIntegrable
  have hmajor0Int : IntervalIntegrable
      (fun w : ℝ ↦ C0 * ‖kernel (lowKernelArgument X beta eta u w)‖)
      volume a b := (harg0.const_mul C0).intervalIntegrable
  have hmajor1Int : IntervalIntegrable
      (fun w : ℝ ↦ C1 * ‖kernel' (lowKernelArgument X beta eta u w)‖)
      volume a b := (harg1.const_mul C1).intervalIntegrable
  have hampDerivCont : Continuous
      (lowProjectionAmplitudeDeriv X H beta eta x u
        cutoff cutoff' kernel kernel') := by
    unfold lowProjectionAmplitudeDeriv lowKernelArgument
    fun_prop
  have hampInt : IntervalIntegrable
      (fun w : ℝ ↦ ‖lowProjectionAmplitudeDeriv X H beta eta x u
        cutoff cutoff' kernel kernel' w‖) volume a b :=
    hampDerivCont.norm.intervalIntegrable _ _
  have hmono : (∫ w : ℝ in a..b,
      ‖lowProjectionAmplitudeDeriv X H beta eta x u
        cutoff cutoff' kernel kernel' w‖) ≤
      ∫ w : ℝ in a..b,
        (C0 * ‖kernel (lowKernelArgument X beta eta u w)‖ +
          C1 * ‖kernel' (lowKernelArgument X beta eta u w)‖) := by
    apply intervalIntegral.integral_mono_on hab hampInt hmajorInt
    intro w hw
    exact norm_lowProjectionAmplitudeDeriv_le_kernel hX hH hHquarter
      hxLower hxUpper (by simpa [a, b, sourcePacketWindow] using hw)
      hcutoff hcutoff' hBcut
  have hwhole0 := MAPMRTVanDerCorput.intervalIntegral_le_integral_of_nonneg
    hab harg0 (fun w ↦ norm_nonneg (kernel (lowKernelArgument X beta eta u w)))
  have hwhole1 := MAPMRTVanDerCorput.intervalIntegral_le_integral_of_nonneg
    hab harg1 (fun w ↦ norm_nonneg (kernel' (lowKernelArgument X beta eta u w)))
  calc
    _ ≤ ∫ w : ℝ in a..b,
        (C0 * ‖kernel (lowKernelArgument X beta eta u w)‖ +
          C1 * ‖kernel' (lowKernelArgument X beta eta u w)‖) := hmono
    _ = C0 * (∫ w : ℝ in a..b,
          ‖kernel (lowKernelArgument X beta eta u w)‖) +
        C1 * (∫ w : ℝ in a..b,
          ‖kernel' (lowKernelArgument X beta eta u w)‖) := by
      rw [intervalIntegral.integral_add hmajor0Int hmajor1Int,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ C0 * (∫ w : ℝ,
          ‖kernel (lowKernelArgument X beta eta u w)‖) +
        C1 * (∫ w : ℝ,
          ‖kernel' (lowKernelArgument X beta eta u w)‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hwhole0 hC0)
        (mul_le_mul_of_nonneg_left hwhole1 hC1)
    _ = _ := by
      rw [integral_norm_lowKernelArgument hX hbeta heta,
        integral_norm_lowKernelArgument hX hbeta heta]
      unfold C0 C1
      ring

end
end MAPMRTProposition51ProjectionLowBudgets

#print axioms MAPMRTProposition51ProjectionLowBudgets.integral_norm_lowKernelArgument
#print axioms MAPMRTProposition51ProjectionLowBudgets.norm_lowProjectionAmplitude_le_kernel
#print axioms MAPMRTProposition51ProjectionLowBudgets.norm_lowProjectionAmplitudeDeriv_le_kernel
#print axioms MAPMRTProposition51ProjectionLowBudgets.integrable_norm_lowKernelArgument
#print axioms MAPMRTProposition51ProjectionLowBudgets.interval_integral_norm_lowProjectionAmplitude_le
#print axioms MAPMRTProposition51ProjectionLowBudgets.interval_integral_norm_lowProjectionAmplitudeDeriv_le
