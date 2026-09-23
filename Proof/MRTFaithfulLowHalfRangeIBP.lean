import MRTFaithfulLowProjectionIdentity
import MRTFaithfulLowTonelli

/-! The half-range low integral uses x±H/2; the literal faithful cutoff
still has physical radius H/8. The old x±H interval is unsuitable at x=H. -/
namespace MAPMRTFaithfulLowHalfRangeIBP
open MeasureTheory Set
open MAPMRTFaithfulLowTonelli MAPMRTFaithfulLowPage47Geometry
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTProposition51ProjectionLowAmplitude
open MAPFinishP51LowIdentity MAPMRTProposition51ProjectionLowBudgets
open MAPMRTProposition51ProjectionLowIBP
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulSmoothCutoffBudgets
noncomputable section

def halfRangeCutoff (y : ℝ) : ℝ := faithfulCutoff (y / 2)
def halfRangeCutoffDeriv (y : ℝ) : ℝ := faithfulCutoffDeriv (y / 2) / 2

theorem halfRangeCutoff_hasDerivAt (y : ℝ) :
    HasDerivAt halfRangeCutoff (halfRangeCutoffDeriv y) y := by
  convert (faithfulCutoff_hasDerivAt (y / 2)).comp y
    ((hasDerivAt_id y).div_const 2) using 1 <;>
    simp [halfRangeCutoff, halfRangeCutoffDeriv, Function.comp_def, div_eq_mul_inv] <;> ring
  funext x
  simp only [halfRangeCutoff, div_eq_mul_inv, one_mul]

theorem halfRangeCutoff_zero (y : ℝ) (hy : 1 ≤ |y|) :
    halfRangeCutoff y = 0 := by
  apply faithfulCutoff_zero
  rw [abs_div]
  norm_num
  linarith

theorem halfRangeAmplitude_eq (X H beta eta x u w : ℝ) (kernel : ℝ → ℂ) :
    lowProjectionAmplitude X (H / 2) beta eta x u halfRangeCutoff kernel w =
      lowProjectionAmplitude X H beta eta x u faithfulCutoff kernel w := by
  unfold lowProjectionAmplitude halfRangeCutoff
  congr 2
  congr 1
  ring

theorem halfRangeAmplitudeDeriv_eq (X H beta eta x u w : ℝ)
    (kernel kernel' : ℝ → ℂ) :
    lowProjectionAmplitudeDeriv X (H / 2) beta eta x u
      halfRangeCutoff halfRangeCutoffDeriv kernel kernel' w =
    lowProjectionAmplitudeDeriv X H beta eta x u
      faithfulCutoff faithfulCutoffDeriv kernel kernel' w := by
  unfold lowProjectionAmplitudeDeriv halfRangeCutoff halfRangeCutoffDeriv
  have he : (X * Real.exp w - x) / (H / 2) / 2 =
      (X * Real.exp w - x) / H := by ring
  rw [he]
  push_cast
  ring

def faithfulHalfRangeLowIntegral (X H beta eta x u : ℝ) : ℂ :=
  ∫ w : ℝ in (Real.log ((x - H / 2) / X))..(Real.log ((x + H / 2) / X)),
    additivePhase (beta * X * Real.exp w) *
      lowProjectionAmplitude X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff) w

theorem norm_faithfulHalfRangeLowIntegral_le_localized
    {X H beta eta x u : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) :
    ‖faithfulHalfRangeLowIntegral X H beta eta x u‖ ≤
      (1 / (|beta| * X / 4)) *
        (∫ w : ℝ in (Real.log ((x - H / 2) / X))..(Real.log ((x + H / 2) / X)),
          ‖lowProjectionAmplitudeDeriv X H beta eta x u
            faithfulCutoff faithfulCutoffDeriv
            (cutoffFourierKernel faithfulCutoff) faithfulCutoffFourierDeriv w‖) +
      ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
        (∫ w : ℝ in (Real.log ((x - H / 2) / X))..(Real.log ((x + H / 2) / X)),
          ‖lowProjectionAmplitude X H beta eta x u faithfulCutoff
            (cutoffFourierKernel faithfulCutoff) w‖) := by
  have hh : 0 < H / 2 := by positivity
  have hq : H / 2 ≤ X / 4 := by linarith
  have hc : Continuous halfRangeCutoffDeriv := by
    unfold halfRangeCutoffDeriv
    exact (faithfulCutoffDeriv_continuous.comp (by fun_prop)).div_const 2
  have hb := norm_lowOscillatoryIntegral_le_localized
    (eta := eta) (u := u) hX hh hq hxLower hxUpper hbeta
    halfRangeCutoff_zero halfRangeCutoff_hasDerivAt hc
    faithfulCutoffFourierKernel_hasDerivAt faithfulCutoffFourierDeriv_continuous
  simpa only [lowOscillatoryIntegral, halfRangeAmplitude_eq,
    halfRangeAmplitudeDeriv_eq, faithfulHalfRangeLowIntegral] using hb

theorem integral_eq_faithfulHalfRangeLowIntegral
    {X H beta eta x u : ℝ} 
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x)
 :
    (∫ w : ℝ, additivePhase (beta * X * Real.exp w) *
        lowProjectionAmplitude X H beta eta x u faithfulCutoff
          (cutoffFourierKernel faithfulCutoff) w) =
      faithfulHalfRangeLowIntegral X H beta eta x u := by
  let a := Real.log ((x - H / 2) / X)
  let b := Real.log ((x + H / 2) / X)
  let F : ℝ → ℂ := fun w ↦ additivePhase (beta * X * Real.exp w) *
    lowProjectionAmplitude X H beta eta x u faithfulCutoff
      (cutoffFourierKernel faithfulCutoff) w
  have hab : a ≤ b := sourcePacketWindow_order hX (by positivity : 0 < H / 2) (by linarith : H / 2 ≤ X / 4) hxLower
  have hindicator : F = Set.indicator (Set.Ioc a b) F := by
    funext w
    by_cases hw : w ∈ Set.Ioc a b
    · simp [hw]
    · have hz := lowProjectionAmplitude_eq_zero_of_not_mem_Ioc
          (beta := beta) (eta := eta) (u := u)
          (kernel := cutoffFourierKernel faithfulCutoff)
          hX (by positivity : 0 < H / 2) (by linarith : H / 2 ≤ X / 4) hxLower halfRangeCutoff_zero (by simpa [a, b] using hw)
      rw [halfRangeAmplitude_eq] at hz
      simp [F, hw, hz]
  unfold faithfulHalfRangeLowIntegral
  change (∫ w : ℝ, F w) = ∫ w : ℝ in a..b, F w
  calc
    (∫ w : ℝ, F w) = ∫ w : ℝ in Set.Ioc a b, F w := by
      conv_lhs => rw [hindicator]
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ w : ℝ in a..b, F w :=
      (intervalIntegral.integral_of_le hab).symm

theorem faithfulLowFrequencyProjection_half_range_eq
    {X H beta eta u : ℝ}  {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hg : Integrable g) :
    lowFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g) u =
      (((Real.sqrt X * (lowProjectionScale X beta eta /
          (2 * Real.pi)) : ℝ) : ℂ) *
        ∫ x : ℝ, g x *
          faithfulHalfRangeLowIntegral X H beta eta x u) := by
  have hc : Continuous halfRangeCutoff := by
    unfold halfRangeCutoff
    exact faithfulCutoff_continuous.comp (by fun_prop)
  have hFubini : Integrable (Function.uncurry
      (lowProjectionSourceKernel X H beta eta u faithfulCutoff g))
      (volume.prod volume) := by
    have hi := lowProjectionSourceKernel_integrable
      (cutoff := halfRangeCutoff) (kernel := cutoffFourierKernel faithfulCutoff)
      (u := u) hX (by positivity : 0 < H / 2)
      (by linarith : H / 2 ≤ X / 4) hbeta heta hg hgSupport
      halfRangeCutoff_zero (fun y ↦ abs_faithfulCutoff_le_one (y / 2))
      hc faithfulCutoffFourierKernel_integrable faithfulCutoffFourierKernel_continuous
    simpa only [halfRangeAmplitude_eq, lowProjectionSourceKernel] using! hi
  have hscale : 0 < lowProjectionScale X beta eta := by
    unfold lowProjectionScale
    positivity
  rw [show lowFrequencyProjection X beta eta faithfulCutoff
      (logarithmicDualFunction X H beta faithfulCutoff g) u =
      rescaledProjection (cutoffFourierKernel faithfulCutoff)
        (lowProjectionScale X beta eta)
        (logarithmicDualFunction X H beta faithfulCutoff g) u by rfl]
  rw [rescaledProjection_eq_affine_kernel hscale]
  have hswap := MeasureTheory.integral_integral_swap hFubini
  have hopen (w : ℝ) :
      logarithmicDualFunction X H beta faithfulCutoff g w *
          cutoffFourierKernel faithfulCutoff
            (lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)) =
        (Real.sqrt X : ℂ) *
          ∫ x : ℝ, lowProjectionSourceKernel
            X H beta eta u faithfulCutoff g w x := by
    unfold logarithmicDualFunction lowProjectionSourceKernel
    rw [show (∫ x : ℝ, (faithfulCutoff ((X * Real.exp w - x) / H) : ℂ) * g x) =
        ∫ x : ℝ, g x * (faithfulCutoff ((X * Real.exp w - x) / H) : ℂ) by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    rw [show (Real.sqrt X : ℂ) * (Real.exp (w / 2) : ℂ) *
          additivePhase (beta * X * Real.exp w) *
          (∫ x : ℝ, g x * (faithfulCutoff ((X * Real.exp w - x) / H) : ℂ)) *
          cutoffFourierKernel faithfulCutoff
            (lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)) =
        (Real.sqrt X : ℂ) *
          ((Real.exp (w / 2) : ℂ) *
            additivePhase (beta * X * Real.exp w) *
            cutoffFourierKernel faithfulCutoff
              (lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)) *
            (∫ x : ℝ, g x *
              (faithfulCutoff ((X * Real.exp w - x) / H) : ℂ))) by ring]
    rw [← MeasureTheory.integral_const_mul]
    apply congrArg ((Real.sqrt X : ℂ) * ·)
    apply integral_congr_ae
    filter_upwards with x
    unfold lowProjectionAmplitude lowKernelArgument
    ring
  simp_rw [hopen]
  rw [MeasureTheory.integral_const_mul]
  change ((lowProjectionScale X beta eta / (2 * Real.pi) : ℝ) : ℂ) *
      ((Real.sqrt X : ℂ) *
        ∫ w : ℝ, ∫ x : ℝ,
          lowProjectionSourceKernel X H beta eta u faithfulCutoff g w x) = _
  rw [hswap]
  have hinner (x : ℝ) :
      (∫ w : ℝ, lowProjectionSourceKernel
          X H beta eta u faithfulCutoff g w x) =
        g x * faithfulHalfRangeLowIntegral X H beta eta x u := by
    unfold lowProjectionSourceKernel
    rw [MeasureTheory.integral_const_mul]
    by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
    · rw [integral_eq_faithfulHalfRangeLowIntegral hX hH hHquarter hx.1]
    · rw [hgSupport x hx]
      simp
  simp_rw [hinner]
  push_cast
  ring

theorem norm_faithfulLowProjectionAmplitude_le_decay_half_range
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X (H / 2) x) :
    ‖lowProjectionAmplitude X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff) w‖ ≤
      3 * faithfulCutoffFourierDecayConstant 2 /
        (1 + |lowKernelArgument X beta eta u w|) ^ 2 := by
  have hamp := norm_lowProjectionAmplitude_le_kernel
    (beta := beta) (eta := eta) (u := u)
    (kernel := cutoffFourierKernel faithfulCutoff)
    (cutoff := halfRangeCutoff)
    hX (by positivity : 0 ≤ H / 2) (by linarith : H / 2 ≤ X / 4) hxLower hxUpper hw
      (fun y ↦ abs_faithfulCutoff_le_one (y / 2))
  have hk := norm_faithfulCutoffFourierKernel_le_decay
    2 (lowKernelArgument X beta eta u w)
  calc
    _ ≤ 3 * ‖cutoffFourierKernel faithfulCutoff
        (lowKernelArgument X beta eta u w)‖ := by simpa only [halfRangeAmplitude_eq] using hamp
    _ ≤ 3 * (faithfulCutoffFourierDecayConstant 2 /
        (1 + |lowKernelArgument X beta eta u w|) ^ 2) := by
      gcongr
    _ = _ := by ring

/-- Literal quadratic Schwartz envelope for the derivative amplitude. -/
theorem norm_faithfulLowProjectionAmplitudeDeriv_le_decay_half_range
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X (H / 2) x) :
    ‖lowProjectionAmplitudeDeriv X H beta eta x u
        faithfulCutoff faithfulCutoffDeriv
        (cutoffFourierKernel faithfulCutoff)
        faithfulCutoffFourierDeriv w‖ ≤
      ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          faithfulCutoffFourierDecayConstant 2 +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          faithfulCutoffFourierDerivDecayConstant 2) /
        (1 + |lowKernelArgument X beta eta u w|) ^ 2 := by
  have hamp := norm_lowProjectionAmplitudeDeriv_le_kernel
    (beta := beta) (eta := eta) (u := u)
    (kernel := cutoffFourierKernel faithfulCutoff)
    (kernel' := faithfulCutoffFourierDeriv)
    (cutoff := halfRangeCutoff) (cutoff' := halfRangeCutoffDeriv)
    (Bcut := faithfulCutoffDerivBudget / 2)
    hX (by positivity : 0 < H / 2) (by linarith : H / 2 ≤ X / 4) hxLower hxUpper hw
    (fun y ↦ abs_faithfulCutoff_le_one (y / 2))
    (fun y ↦ by
      unfold halfRangeCutoffDeriv
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact div_le_div_of_nonneg_right (abs_faithfulCutoffDeriv_le (y / 2)) (by norm_num))
    (div_nonneg faithfulCutoffDerivBudget_nonneg (by norm_num))
  have hk := norm_faithfulCutoffFourierKernel_le_decay
    2 (lowKernelArgument X beta eta u w)
  have hk' := norm_faithfulCutoffFourierDeriv_le_decay
    2 (lowKernelArgument X beta eta u w)
  have hC0 : 0 ≤ 3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H) := by
    apply add_nonneg (by norm_num)
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num) faithfulCutoffDerivBudget_nonneg) hX.le
    · positivity
  have hC1 : 0 ≤ 3 * |lowProjectionScale X beta eta / (2 * Real.pi)| := by
    positivity
  calc
    _ ≤ (3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          ‖cutoffFourierKernel faithfulCutoff
            (lowKernelArgument X beta eta u w)‖ +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          ‖faithfulCutoffFourierDeriv
            (lowKernelArgument X beta eta u w)‖ := by
      convert hamp using 1
      · rw [halfRangeAmplitudeDeriv_eq]
      · congr 2 <;> ring
    _ ≤ (3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          (faithfulCutoffFourierDecayConstant 2 /
            (1 + |lowKernelArgument X beta eta u w|) ^ 2) +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          (faithfulCutoffFourierDerivDecayConstant 2 /
            (1 + |lowKernelArgument X beta eta u w|) ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hk hC0)
        (mul_le_mul_of_nonneg_left hk' hC1)
    _ = _ := by ring


theorem norm_faithfulLowProjectionAmplitude_le_localizedDecay_half_range
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    ‖lowProjectionAmplitude X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff) w‖ ≤
      3 * faithfulCutoffFourierDecayConstant 2 *
        faithfulLocalizedDecay
          (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w := by
  by_cases hp : |X * Real.exp w - x| ≤ H / 8
  · have hw : w ∈ sourcePacketWindow X (H / 2) x := by
      unfold sourcePacketWindow
      have hp' : |X * Real.exp w - x| ≤ H / 2 := hp.trans (by linarith)
      rw [abs_le] at hp'
      have hxMinus : 0 < x - H / 2 := by nlinarith
      have hxPlus : 0 < x + H / 2 := by nlinarith
      constructor
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxMinus hX)]
        exact (div_le_iff₀ hX).2 (by linarith [hp'.1])
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxPlus hX)]
        exact (le_div_iff₀ hX).2 (by linarith [hp'.2])
    have hb := norm_faithfulLowProjectionAmplitude_le_decay_half_range
      (beta := beta) (eta := eta) (u := u)
      hX hH.le hHquarter hxLower hxUpper hw
    unfold faithfulLocalizedDecay
    rw [if_pos hp]
    simpa [lowKernelArgument, div_eq_mul_inv] using hb
  · have hz := faithfulLowProjectionAmplitude_eq_zero_of_outside
      (X := X) (beta := beta) (eta := eta) (u := u) hH
      (lt_of_not_ge hp)
    rw [hz, norm_zero]
    simp [faithfulLocalizedDecay, hp]

/-- Global pointwise envelope for the differentiated faithful amplitude. -/
theorem norm_faithfulLowProjectionAmplitudeDeriv_le_localizedDecay_half_range
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    ‖lowProjectionAmplitudeDeriv X H beta eta x u
        faithfulCutoff faithfulCutoffDeriv
        (cutoffFourierKernel faithfulCutoff)
        faithfulCutoffFourierDeriv w‖ ≤
      ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          faithfulCutoffFourierDecayConstant 2 +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          faithfulCutoffFourierDerivDecayConstant 2) *
        faithfulLocalizedDecay
          (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w := by
  by_cases hp : |X * Real.exp w - x| ≤ H / 8
  · have hw : w ∈ sourcePacketWindow X (H / 2) x := by
      unfold sourcePacketWindow
      have hp' : |X * Real.exp w - x| ≤ H / 2 := hp.trans (by linarith)
      rw [abs_le] at hp'
      have hxMinus : 0 < x - H / 2 := by nlinarith
      have hxPlus : 0 < x + H / 2 := by nlinarith
      constructor
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxMinus hX)]
        exact (div_le_iff₀ hX).2 (by linarith [hp'.1])
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxPlus hX)]
        exact (le_div_iff₀ hX).2 (by linarith [hp'.2])
    have hb := norm_faithfulLowProjectionAmplitudeDeriv_le_decay_half_range
      (beta := beta) (eta := eta) (u := u)
      hX hH hHquarter hxLower hxUpper hw
    unfold faithfulLocalizedDecay
    rw [if_pos hp]
    simpa [lowKernelArgument, div_eq_mul_inv] using hb
  · have hz := faithfulLowProjectionAmplitudeDeriv_eq_zero_of_outside
      (X := X) (beta := beta) (eta := eta) (u := u) hH
      (lt_of_not_ge hp)
    rw [hz, norm_zero]
    simp [faithfulLocalizedDecay, hp]


theorem interval_nonnegative_majorant_le_global
    {a b C : ℝ} {F K : ℝ → ℝ} (hab : a ≤ b)
    (hF : ∀ w, 0 ≤ F w) (hK : ∀ w, 0 ≤ K w)
    (hC : 0 ≤ C) (hKi : Integrable K) (hbound : ∀ w, F w ≤ C * K w) :
    (∫ w in a..b, F w) ≤ C * ∫ w : ℝ, K w := by
  rw [intervalIntegral.integral_of_le hab]
  calc
    _ ≤ ∫ w in Ioc a b, C * K w := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall hF
      · exact (hKi.const_mul C).integrableOn
      · exact Filter.Eventually.of_forall hbound
    _ ≤ ∫ w : ℝ, C * K w := setIntegral_le_integral (hKi.const_mul C)
      (Filter.Eventually.of_forall fun w ↦ mul_nonneg hC (hK w))
    _ = _ := integral_const_mul _ _

/-- Localized IBP with the original faithful physical mask and translated
Fourier decay retained, valid through H=X/2. -/
theorem norm_faithfulHalfRangeLowIntegral_le_decay_integral
    {X H beta eta x u : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) (heta : 0 < eta) :
    ‖faithfulHalfRangeLowIntegral X H beta eta x u‖ ≤
      ((1 / (|beta| * X / 4)) *
        ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
            faithfulCutoffFourierDecayConstant 2 +
          3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
            faithfulCutoffFourierDerivDecayConstant 2) +
        ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
          (3 * faithfulCutoffFourierDecayConstant 2)) *
        ∫ w : ℝ, faithfulLocalizedDecay
          (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w := by
  have ha : 0 < lowProjectionScale X beta eta / (2 * Real.pi) := by
    unfold lowProjectionScale
    positivity
  have hi := integrable_faithfulLocalizedDecay (X := X) (H := H) (x := x) (u := u) ha
  have hab := sourcePacketWindow_order hX (by positivity : 0 < H / 2)
    (by linarith : H / 2 ≤ X / 4) hxLower
  have hD := faithfulCutoffDerivBudget_nonneg
  have hK := faithfulCutoffFourierDecayConstant_nonneg 2
  have hKd := faithfulCutoffFourierDerivDecayConstant_nonneg 2
  have hfirst := interval_nonnegative_majorant_le_global hab
    (fun w ↦ norm_nonneg _) (faithfulLocalizedDecay_nonneg _ _ _ _ _)
    (by positivity : 0 ≤ (3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
      faithfulCutoffFourierDecayConstant 2 +
      3 * |lowProjectionScale X beta eta / (2 * Real.pi)| * faithfulCutoffFourierDerivDecayConstant 2)
    hi (fun w ↦ norm_faithfulLowProjectionAmplitudeDeriv_le_localizedDecay_half_range
      (w := w) hX hH hHalf hxLower hxUpper)
  have hsecond := interval_nonnegative_majorant_le_global hab
    (fun w ↦ norm_nonneg _) (faithfulLocalizedDecay_nonneg _ _ _ _ _)
    (by positivity : 0 ≤ 3 * faithfulCutoffFourierDecayConstant 2)
    hi (fun w ↦ norm_faithfulLowProjectionAmplitude_le_localizedDecay_half_range
      (w := w) hX hH hHalf hxLower hxUpper)
  have hb := norm_faithfulHalfRangeLowIntegral_le_localized
    (eta := eta) (u := u) hX hH hHalf hxLower hxUpper hbeta
  calc
    _ ≤ _ := hb
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hfirst (by positivity))
      (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = _ := by ring

#print axioms faithfulLowFrequencyProjection_half_range_eq
#print axioms norm_faithfulHalfRangeLowIntegral_le_decay_integral

#print axioms norm_faithfulHalfRangeLowIntegral_le_localized
end
end MAPMRTFaithfulLowHalfRangeIBP
