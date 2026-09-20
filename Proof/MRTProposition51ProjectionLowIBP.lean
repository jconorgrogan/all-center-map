import MRTProposition51ProjectionLowBudgets

/-!
# The source p. 47 low-frequency integration by parts

This is the literal oscillatory `w` integral in (78), on the exact interval
forced by the physical cutoff.  No projection or ordinary-error estimate is
assumed.
-/

namespace MAPMRTProposition51ProjectionLowIBP

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof MAPMRTNonstationaryPhaseInverse
open MAPMRTProposition51ProjectionLowAmplitude
open MAPMRTProposition51ProjectionLowBudgets
open MAPMRTProposition51ProjectionOneIBP

noncomputable section

def lowOscillatoryIntegral
    (X H beta eta x u : ℝ) (cutoff : ℝ → ℝ) (kernel : ℝ → ℂ) : ℂ :=
  ∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
    additivePhase (beta * X * Real.exp w) *
      lowProjectionAmplitude X H beta eta x u cutoff kernel w

theorem lowProjectionAmplitude_left_endpoint
    {X H beta eta x u : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    lowProjectionAmplitude X H beta eta x u cutoff kernel
      (Real.log ((x - H) / X)) = 0 := by
  have hxMinus : 0 < x - H := by
    have : X / 4 ≤ x - H := by linarith
    exact lt_of_lt_of_le (by positivity : 0 < X / 4) this
  apply lowProjectionAmplitude_eq_zero_of_physical_outside hH hcutoffSupport
  rw [Real.exp_log (div_pos hxMinus hX)]
  have hXne := hX.ne'
  field_simp [hXne]
  simp [abs_of_pos hH]

theorem lowProjectionAmplitude_right_endpoint
    {X H beta eta x u : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    lowProjectionAmplitude X H beta eta x u cutoff kernel
      (Real.log ((x + H) / X)) = 0 := by
  have hxPlus : 0 < x + H := by linarith
  apply lowProjectionAmplitude_eq_zero_of_physical_outside hH hcutoffSupport
  rw [Real.exp_log (div_pos hxPlus hX)]
  have hXne := hX.ne'
  field_simp [hXne]
  simp [abs_of_pos hH]

/-- Localized p. 47 one-IBP estimate.  Unlike the global Schwartz-budget
corollary below, this theorem retains the translated kernel inside the exact
physical `w` window; this is the form needed before the source's
`z=w-log n+log X` change of variables. -/
theorem norm_lowOscillatoryIntegral_le_localized
    {X H beta eta x u : ℝ}
    {cutoff cutoff' : ℝ → ℝ} {kernel kernel' : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (hkernelDeriv : ∀ y, HasDerivAt kernel (kernel' y) y)
    (hkernel'Cont : Continuous kernel') :
    ‖lowOscillatoryIntegral X H beta eta x u cutoff kernel‖ ≤
      (1 / (|beta| * X / 4)) *
        (∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
          ‖lowProjectionAmplitudeDeriv X H beta eta x u
            cutoff cutoff' kernel kernel' w‖) +
      ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
        (∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
          ‖lowProjectionAmplitude X H beta eta x u cutoff kernel w‖) := by
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
  let p : ℝ → ℝ := fun w ↦ beta * X * Real.exp w
  let E : ℝ → ℂ := fun w ↦ additivePhase (p w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p
  let amplitude := lowProjectionAmplitude X H beta eta x u cutoff kernel
  let amplitude' := lowProjectionAmplitudeDeriv X H beta eta x u
    cutoff cutoff' kernel kernel'
  have hab : a ≤ b := sourcePacketWindow_order hX hH hHquarter hxLower
  have hp : ∀ w, HasDerivAt p (p w) w := by
    intro w
    unfold p
    convert (Real.hasDerivAt_exp w).const_mul (beta * X) using 1 <;> ring
  have hp0 : ∀ w, p w ≠ 0 := by
    intro w
    unfold p
    exact mul_ne_zero (mul_ne_zero hbeta hX.ne') (Real.exp_ne_zero w)
  have hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w := by
    intro w hw
    exact hasDerivAt_additivePhase_comp (hp w)
  have hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w := by
    intro w hw
    exact hasDerivAt_inversePhaseDerivative (hp0 w) (hp w)
  have ha : ∀ w ∈ Set.Icc a b,
      HasDerivAt amplitude (amplitude' w) w := by
    intro w hw
    exact hasDerivAt_lowProjectionAmplitude hH.ne'
      hcutoffDeriv hkernelDeriv
  have hpCont : Continuous p :=
    continuous_iff_continuousAt.2 fun w ↦ (hp w).continuousAt
  have hEdCont : ContinuousOn Ed (Set.Icc a b) := by
    have hadd : Continuous additivePhase :=
      continuous_iff_continuousAt.2 fun y ↦
        (hasDerivAt_additivePhase y).continuousAt
    have hECont : Continuous E := hadd.comp hpCont
    unfold Ed
    exact ((continuous_const.mul continuous_const).mul
      (Complex.continuous_ofReal.comp hpCont)).mul hECont |>.continuousOn
  have hqdCont : ContinuousOn qd (Set.Icc a b) := by
    have hreal : Continuous (fun w ↦
        p w / (2 * Real.pi * p w ^ 2)) := by
      apply hpCont.div (continuous_const.mul (hpCont.pow 2))
      intro w
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (pow_ne_zero 2 (hp0 w))
    unfold qd inversePhaseDerivativeDeriv
    exact (Complex.continuous_ofReal.comp hreal).mul continuous_const |>.continuousOn
  have ha'Cont : ContinuousOn amplitude' (Set.Icc a b) := by
    unfold amplitude' lowProjectionAmplitudeDeriv lowKernelArgument
    apply Continuous.continuousOn
    have hcutoffCont : Continuous cutoff :=
      continuous_iff_continuousAt.2 fun y ↦ (hcutoffDeriv y).continuousAt
    have hkernelCont : Continuous kernel :=
      continuous_iff_continuousAt.2 fun y ↦ (hkernelDeriv y).continuousAt
    fun_prop
  have hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w := by
    intro w hw
    exact inversePhaseDerivative_mul_phaseDeriv (hp0 w)
  have hleft : amplitude a = 0 :=
    lowProjectionAmplitude_left_endpoint hX hH hHquarter hxLower
      hcutoffSupport
  have hright : amplitude b = 0 :=
    lowProjectionAmplitude_right_endpoint hX hH hxLower hcutoffSupport
  have hd : 0 < |beta| * X / 4 := by positivity
  have hP : 0 ≤ 17 * |beta| * X / 4 := by positivity
  have hpLower : ∀ w ∈ Set.Icc a b, |beta| * X / 4 ≤ |p w| := by
    intro w hw
    exact stationaryPacketPhase_curvature_lower_on_sourceWindow hX
      hHquarter hxLower (by simpa [a, b, sourcePacketWindow] using hw)
  have hpUpper : ∀ w ∈ Set.Icc a b, |p w| ≤ 17 * |beta| * X / 4 := by
    intro w hw
    have hphys := physical_derivative_factor_le hX hH hHquarter hxLower
      hxUpper (by simpa [a, b, sourcePacketWindow] using hw)
    have hXexp : X * Real.exp w ≤ 17 * X / 4 := by
      have ht := mul_le_mul_of_nonneg_right hphys hH.le
      field_simp [hH.ne'] at ht
      nlinarith
    unfold p
    rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
    convert mul_le_mul_of_nonneg_left hXexp (abs_nonneg beta) using 1 <;> ring
  have hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ 1 / (|beta| * X / 4) := by
    intro w hw
    exact norm_inversePhaseDerivative_le hd (hpLower w hw)
  have hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤
      (17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2 := by
    intro w hw
    exact norm_inversePhaseDerivativeDeriv_le hd hP
      (hpLower w hw) (hpUpper w hw)
  have hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1 := by
    intro w hw
    exact norm_additivePhase _
  unfold lowOscillatoryIntegral
  change ‖∫ w : ℝ in a..b, E w * amplitude w‖ ≤ _
  exact norm_integral_le_one_ibp_budgets hab hE hq ha hEdCont hqdCont
    ha'Cont hinverse hleft hright le_rfl le_rfl hQ0 hQ1 hEUnit
    (by positivity) (by positivity)

/-- The exact one-IBP bound for the p. 47 inner oscillatory integral.  The two
kernel `L¹` masses are the fixed Schwartz budgets of `φ̂` and `(φ̂)'`.
-/
theorem norm_lowOscillatoryIntegral_le
    {X H beta eta x u Bcut : ℝ}
    {cutoff cutoff' : ℝ → ℝ} {kernel kernel' : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (hcutoff' : ∀ y, |cutoff' y| ≤ Bcut) (hBcut : 0 ≤ Bcut)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (hkernelDeriv : ∀ y, HasDerivAt kernel (kernel' y) y)
    (hkernel'Cont : Continuous kernel')
    (hkernelInt : Integrable kernel) (hkernel'Int : Integrable kernel') :
    ‖lowOscillatoryIntegral X H beta eta x u cutoff kernel‖ ≤
      (1 / (|beta| * X / 4)) *
        ((3 / 2 + 51 * Bcut * X / (4 * H)) *
            (2 * Real.pi / lowProjectionScale X beta eta) *
              (∫ v : ℝ, ‖kernel v‖) +
          3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
            (2 * Real.pi / lowProjectionScale X beta eta) *
              (∫ v : ℝ, ‖kernel' v‖)) +
      ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
        (3 * (2 * Real.pi / lowProjectionScale X beta eta) *
          ∫ v : ℝ, ‖kernel v‖) := by
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
  let p : ℝ → ℝ := fun w ↦ beta * X * Real.exp w
  let E : ℝ → ℂ := fun w ↦ additivePhase (p w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p
  let amplitude := lowProjectionAmplitude X H beta eta x u cutoff kernel
  let amplitude' := lowProjectionAmplitudeDeriv X H beta eta x u
    cutoff cutoff' kernel kernel'
  have hab : a ≤ b := sourcePacketWindow_order hX hH hHquarter hxLower
  have hp : ∀ w, HasDerivAt p (p w) w := by
    intro w
    unfold p
    convert (Real.hasDerivAt_exp w).const_mul (beta * X) using 1 <;> ring
  have hp0 : ∀ w, p w ≠ 0 := by
    intro w
    unfold p
    exact mul_ne_zero (mul_ne_zero hbeta hX.ne') (Real.exp_ne_zero w)
  have hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w := by
    intro w hw
    exact hasDerivAt_additivePhase_comp (hp w)
  have hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w := by
    intro w hw
    exact hasDerivAt_inversePhaseDerivative (hp0 w) (hp w)
  have ha : ∀ w ∈ Set.Icc a b,
      HasDerivAt amplitude (amplitude' w) w := by
    intro w hw
    exact hasDerivAt_lowProjectionAmplitude hH.ne'
      hcutoffDeriv hkernelDeriv
  have hEdCont : ContinuousOn Ed (Set.Icc a b) := by
    have hpCont : Continuous p :=
      continuous_iff_continuousAt.2 fun w ↦ (hp w).continuousAt
    have hadd : Continuous additivePhase :=
      continuous_iff_continuousAt.2 fun y ↦
        (hasDerivAt_additivePhase y).continuousAt
    have hECont : Continuous E := hadd.comp hpCont
    unfold Ed
    exact ((continuous_const.mul continuous_const).mul
      (Complex.continuous_ofReal.comp hpCont)).mul hECont |>.continuousOn
  have hqdCont : ContinuousOn qd (Set.Icc a b) := by
    have hpCont : Continuous p :=
      continuous_iff_continuousAt.2 fun w ↦ (hp w).continuousAt
    have hreal : Continuous (fun w ↦
        p w / (2 * Real.pi * p w ^ 2)) := by
      apply hpCont.div (continuous_const.mul (hpCont.pow 2))
      intro w
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (pow_ne_zero 2 (hp0 w))
    unfold qd inversePhaseDerivativeDeriv
    exact (Complex.continuous_ofReal.comp hreal).mul continuous_const |>.continuousOn
  have ha'Cont : ContinuousOn amplitude' (Set.Icc a b) := by
    unfold amplitude' lowProjectionAmplitudeDeriv lowKernelArgument
    apply Continuous.continuousOn
    have hcutoffCont : Continuous cutoff :=
      continuous_iff_continuousAt.2 fun y ↦ (hcutoffDeriv y).continuousAt
    have hkernelCont : Continuous kernel :=
      continuous_iff_continuousAt.2 fun y ↦ (hkernelDeriv y).continuousAt
    fun_prop
  have hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w := by
    intro w hw
    exact inversePhaseDerivative_mul_phaseDeriv (hp0 w)
  have hleft : amplitude a = 0 := by
    exact lowProjectionAmplitude_left_endpoint hX hH hHquarter hxLower
      hcutoffSupport
  have hright : amplitude b = 0 := by
    exact lowProjectionAmplitude_right_endpoint hX hH hxLower hcutoffSupport
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.2 fun y ↦ (hcutoffDeriv y).continuousAt
  have hkernelCont : Continuous kernel :=
    continuous_iff_continuousAt.2 fun y ↦ (hkernelDeriv y).continuousAt
  have hA0 := interval_integral_norm_lowProjectionAmplitude_le
    (u := u) hX hH hHquarter hxLower hxUpper hbeta heta hcutoff
    hcutoffCont hkernelCont hkernelInt
  have hA1 := interval_integral_norm_lowProjectionAmplitudeDeriv_le
    (u := u) hX hH hHquarter hxLower hxUpper hbeta heta hcutoff hcutoff' hBcut
    hcutoffCont hcutoff'Cont hkernelCont hkernel'Cont hkernelInt hkernel'Int
  have hd : 0 < |beta| * X / 4 := by positivity
  have hP : 0 ≤ 17 * |beta| * X / 4 := by positivity
  have hpLower : ∀ w ∈ Set.Icc a b, |beta| * X / 4 ≤ |p w| := by
    intro w hw
    exact stationaryPacketPhase_curvature_lower_on_sourceWindow hX
      hHquarter hxLower (by simpa [a, b, sourcePacketWindow] using hw)
  have hpUpper : ∀ w ∈ Set.Icc a b, |p w| ≤ 17 * |beta| * X / 4 := by
    intro w hw
    have hphys := physical_derivative_factor_le hX hH hHquarter hxLower
      hxUpper (by simpa [a, b, sourcePacketWindow] using hw)
    have hXexp : X * Real.exp w ≤ 17 * X / 4 := by
      have := mul_le_mul_of_nonneg_right hphys hH.le
      field_simp [hH.ne'] at this
      nlinarith
    unfold p
    rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
    convert mul_le_mul_of_nonneg_left hXexp (abs_nonneg beta) using 1 <;> ring
  have hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ 1 / (|beta| * X / 4) := by
    intro w hw
    exact norm_inversePhaseDerivative_le hd (hpLower w hw)
  have hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤
      (17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2 := by
    intro w hw
    exact norm_inversePhaseDerivativeDeriv_le hd hP
      (hpLower w hw) (hpUpper w hw)
  have hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1 := by
    intro w hw
    exact norm_additivePhase _
  unfold lowOscillatoryIntegral
  change ‖∫ w : ℝ in a..b, E w * amplitude w‖ ≤ _
  exact norm_integral_le_one_ibp_budgets hab hE hq ha hEdCont hqdCont
    ha'Cont hinverse hleft hright hA0 hA1 hQ0 hQ1 hEUnit
    (by positivity) (by positivity)

end
end MAPMRTProposition51ProjectionLowIBP

#print axioms MAPMRTProposition51ProjectionLowIBP.norm_lowOscillatoryIntegral_le
#print axioms MAPMRTProposition51ProjectionLowIBP.norm_lowOscillatoryIntegral_le_localized
