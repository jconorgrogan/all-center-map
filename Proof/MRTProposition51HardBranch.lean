import MRTProposition51FirstAnalytic

/-!
# MRT Proposition 5.1 hard branch: logarithmic transform and LP identity

This staging-only module formalizes the first exact constructions after equation
(72) in the published proof: the logarithmic `G(u)` change of variables and the
three Littlewood--Paley pieces in equation (76).  It also records the literal
oscillatory packet phase, its first two derivatives, and a proved compact-packet
`L¹` bound.  No analytic estimate is represented by a proposition-valued input.
-/

namespace MAPMRTProposition51HardBranch

open MeasureTheory Set
open scoped BigOperators FourierTransform
open MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPMRTProposition51FirstAnalytic

noncomputable section

/-! ## The exact logarithmic `G(u)` change -/

/-- The function `G` following MRT equation (74).  The cutoff is kept as an
actual function argument; later it will be instantiated by a smooth bump. -/
def logarithmicDualFunction
    (X H beta : ℝ) (cutoff : ℝ → ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
    additivePhase (beta * X * Real.exp u) *
      ∫ x : ℝ, (cutoff ((X * Real.exp u - x) / H) : ℂ) * g x

theorem exp_log_ratio
    {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (Real.log n - Real.log X) = (n : ℝ) / X := by
  rw [Real.exp_sub, Real.exp_log (by exact_mod_cast (Nat.zero_lt_of_lt hn)),
    Real.exp_log hX]

theorem sqrt_mul_exp_half_log_ratio
    {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt X * Real.exp ((Real.log n - Real.log X) / 2) =
      Real.sqrt n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hexp := exp_log_ratio hX hn
  have hexpsq :
      Real.exp ((Real.log n - Real.log X) / 2) ^ 2 = (n : ℝ) / X := by
    calc
      Real.exp ((Real.log n - Real.log X) / 2) ^ 2 =
          Real.exp ((Real.log n - Real.log X) / 2) *
            Real.exp ((Real.log n - Real.log X) / 2) := by ring
      _ = Real.exp ((Real.log n - Real.log X) / 2 +
            (Real.log n - Real.log X) / 2) := (Real.exp_add _ _).symm
      _ = Real.exp (Real.log n - Real.log X) := by ring_nf
      _ = (n : ℝ) / X := hexp
  have hsquare :
      (Real.sqrt X * Real.exp ((Real.log n - Real.log X) / 2)) ^ 2 =
        (n : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hX.le, hexpsq]
    field_simp [ne_of_gt hX]
  have hleft :
      0 ≤ Real.sqrt X * Real.exp ((Real.log n - Real.log X) / 2) := by
    positivity
  have hright := Real.sqrt_nonneg (n : ℝ)
  have hrightSq := Real.sq_sqrt hnpos.le
  nlinarith

/-- Evaluation of the source `G(u)` at `u=log n-log X`. -/
theorem logarithmicDualFunction_at_log_ratio
    {X H beta : ℝ} (hX : 0 < X) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    logarithmicDualFunction X H beta cutoff g
        (Real.log n - Real.log X) =
      (Real.sqrt n : ℂ) * additivePhase (beta * n) *
        ∫ x : ℝ, (cutoff (((n : ℝ) - x) / H) : ℂ) * g x := by
  have hexp := exp_log_ratio hX hn
  have hsqrt := sqrt_mul_exp_half_log_ratio hX hn
  unfold logarithmicDualFunction
  rw [show (Real.sqrt X : ℂ) *
      (Real.exp ((Real.log n - Real.log X) / 2) : ℂ) =
        (Real.sqrt n : ℂ) by exact_mod_cast hsqrt]
  have hXne : X ≠ 0 := ne_of_gt hX
  have hscale : X * ((n : ℝ) / X) = n := by field_simp
  rw [hexp]
  have hphaseScale : beta * X * ((n : ℝ) / X) = beta * n := by
    calc
      beta * X * ((n : ℝ) / X) = beta * (X * ((n : ℝ) / X)) := by ring
      _ = beta * n := by rw [hscale]
  rw [hphaseScale, hscale]

/-- Exact equality (74): the smoothed additive pairing is the critical
Dirichlet coefficient multiplied by `G(log n-log X)`. -/
theorem criticalCoefficient_mul_logarithmicDualFunction
    {X H beta : ℝ} (hX : 0 < X) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    {n : ℕ} (hn : 1 ≤ n) (f : ℕ → ℂ) :
    f n * (Real.sqrt n : ℂ)⁻¹ *
        logarithmicDualFunction X H beta cutoff g
          (Real.log n - Real.log X) =
      f n * additivePhase (beta * n) *
        ∫ x : ℝ, (cutoff (((n : ℝ) - x) / H) : ℂ) * g x := by
  rw [logarithmicDualFunction_at_log_ratio hX cutoff g hn]
  have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by
      exact_mod_cast (Nat.zero_lt_of_lt hn) : (0 : ℝ) < n)))
  field_simp

/-! ## Exact Littlewood--Paley decomposition (76) -/

/-- The rescaled smoothing operator used in all three projections. -/
def rescaledProjection
    (kernel : ℝ → ℂ) (T : ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, G (u - 2 * Real.pi * v / T) * kernel v

/-- The actual Fourier kernel `φ̂` in the paper's convention. -/
def cutoffFourierKernel (cutoff : ℝ → ℝ) (v : ℝ) : ℂ :=
  (𝓕 (fun y : ℝ ↦ (cutoff y : ℂ))) v

/-- Low frequencies in equation (76), at scale `10η|β|X`. -/
def lowFrequencyProjection
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  rescaledProjection (cutoffFourierKernel cutoff)
    (10 * eta * |beta| * X) G u

/-- The larger smooth cutoff, whose frequency scale is `|β|X/η`. -/
def mediumOrLowProjection
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  rescaledProjection (cutoffFourierKernel cutoff)
    (|beta| * X / eta) G u

/-- Medium frequencies in equation (76). -/
def mediumFrequencyProjection
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  mediumOrLowProjection X beta eta cutoff G u -
    lowFrequencyProjection X beta eta cutoff G u

/-- High frequencies in equation (76). -/
def highFrequencyProjection
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  G u - mediumOrLowProjection X beta eta cutoff G u

/-- Exact Littlewood--Paley decomposition (76).  It is a telescoping identity,
so it requires no hidden integrability or normalization assumption. -/
theorem low_add_medium_add_high_eq
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ) (u : ℝ) :
    lowFrequencyProjection X beta eta cutoff G u +
        mediumFrequencyProjection X beta eta cutoff G u +
      highFrequencyProjection X beta eta cutoff G u = G u := by
  unfold mediumFrequencyProjection highFrequencyProjection
  ring

theorem critical_sum_eq_low_add_medium_add_high
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (G : ℝ → ℂ)
    (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ s, f n * (Real.sqrt n : ℂ)⁻¹ * G (Real.log n - Real.log X)) =
      (∑ n ∈ s, f n * (Real.sqrt n : ℂ)⁻¹ *
        lowFrequencyProjection X beta eta cutoff G
          (Real.log n - Real.log X)) +
      (∑ n ∈ s, f n * (Real.sqrt n : ℂ)⁻¹ *
        mediumFrequencyProjection X beta eta cutoff G
          (Real.log n - Real.log X)) +
      (∑ n ∈ s, f n * (Real.sqrt n : ℂ)⁻¹ *
        highFrequencyProjection X beta eta cutoff G
          (Real.log n - Real.log X)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_add, ← mul_add, low_add_medium_add_high_eq]

/-! ## The literal stationary packet and its first proved bound -/

/-- Phase `φ_t(w)=βXe^w+tw/(2π)` in equation (80). -/
def stationaryPacketPhase (X beta t w : ℝ) : ℝ :=
  beta * X * Real.exp w + t * w / (2 * Real.pi)

theorem hasDerivAt_stationaryPacketPhase
    (X beta t w : ℝ) :
    HasDerivAt (stationaryPacketPhase X beta t)
      (beta * X * Real.exp w + t / (2 * Real.pi)) w := by
  have h := ((Real.hasDerivAt_exp w).const_mul (beta * X)).add
    (hasDerivAt_id w |>.const_mul (t / (2 * Real.pi)))
  convert h using 1
  · funext z
    simp only [stationaryPacketPhase, Pi.add_apply, id_eq]
    ring
  · ring

theorem hasDerivAt_stationaryPacketPhase_deriv
    (X beta t w : ℝ) :
    HasDerivAt (fun z ↦ beta * X * Real.exp z + t / (2 * Real.pi))
      (beta * X * Real.exp w) w := by
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    ((Real.hasDerivAt_exp w).const_mul (beta * X)).add_const
      (t / (2 * Real.pi))

/-- Compact interval form of the oscillatory packet in equation (80). -/
def stationaryPacketOn
    (X beta t : ℝ) (amplitude : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ w in a..b, additivePhase (stationaryPacketPhase X beta t w) * amplitude w

/-- The first unconditional packet estimate: phase has unit modulus, so a
uniform amplitude bound gives interval length times that bound.  This is the
proved baseline before van der Corput or integrations by parts. -/
theorem norm_stationaryPacketOn_le
    {X beta t a b C : ℝ} {amplitude : ℝ → ℂ}
    (hamp : ∀ w ∈ Set.uIcc a b, ‖amplitude w‖ ≤ C) :
    ‖stationaryPacketOn X beta t amplitude a b‖ ≤ |b - a| * C := by
  unfold stationaryPacketOn
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun w ↦ additivePhase (stationaryPacketPhase X beta t w) * amplitude w)
    (C := C) (a := a) (b := b) (by
      intro w hw
      rw [norm_mul]
      have hphase : ‖additivePhase (stationaryPacketPhase X beta t w)‖ = 1 := by
        unfold additivePhase
        rw [show 2 * (Real.pi : ℂ) *
            (stationaryPacketPhase X beta t w : ℂ) * Complex.I =
          ((2 * Real.pi * stationaryPacketPhase X beta t w : ℝ) : ℂ) *
            Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [hphase, one_mul]
      exact hamp w (Set.uIoc_subset_uIcc hw))
  simpa [mul_comm] using h

/-! ### The literal packet amplitude and its small-support estimate -/

/-- The amplitude `aₓ(w)` in equation (80).  The two cutoff arguments are
separated only so that their hypotheses can be stated independently. -/
def sourcePacketAmplitude
    (X H x : ℝ) (cutoff outerCutoff : ℝ → ℝ) (w : ℝ) : ℂ :=
  (Real.exp (w / 2) : ℂ) *
    (cutoff ((X * Real.exp w - x) / H) : ℂ) *
      (outerCutoff (w / 100) : ℂ)

/-- The logarithmic window forced by the compact support of
`cutoff ((X exp w - x) / H)`. -/
def sourcePacketWindow (X H x : ℝ) : Set ℝ :=
  Set.Icc (Real.log ((x - H) / X)) (Real.log ((x + H) / X))

/-- The full oscillatory integral `Jₓ(t)` from equation (80). -/
def sourceStationaryPacket
    (X H x beta t : ℝ) (cutoff outerCutoff : ℝ → ℝ) : ℂ :=
  ∫ w : ℝ, additivePhase (stationaryPacketPhase X beta t w) *
    sourcePacketAmplitude X H x cutoff outerCutoff w

/-- The literal source amplitude vanishes outside its logarithmic cutoff
window.  We state endpoint vanishing as well; it follows for the paper's smooth
function supported on `[-1,1]`. -/
theorem sourcePacketAmplitude_eq_zero_of_not_mem_Ioc
    {X H x w : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : w ∉ Set.Ioc (Real.log ((x - H) / X))
      (Real.log ((x + H) / X))) :
    sourcePacketAmplitude X H x cutoff outerCutoff w = 0 := by
  have hxMinusLower : X / 4 ≤ x - H := by linarith
  have hxMinus : 0 < x - H := lt_of_lt_of_le (by positivity : 0 < X / 4) hxMinusLower
  have hxPlus : 0 < x + H := by linarith
  have ha : 0 < (x - H) / X := div_pos hxMinus hX
  have hb : 0 < (x + H) / X := div_pos hxPlus hX
  simp only [Set.mem_Ioc, not_and_or, not_le] at hw
  have hzero : cutoff ((X * Real.exp w - x) / H) = 0 := by
    apply hcutoffSupport
    rcases hw with hwLeft | hwRight
    · have hexp : Real.exp w ≤ (x - H) / X := by
        rw [← Real.exp_log ha]
        exact Real.exp_le_exp.mpr (le_of_not_gt hwLeft)
      have hnum : X * Real.exp w - x ≤ -H := by
        have := (le_div_iff₀ hX).mp hexp
        nlinarith
      have hquot : (X * Real.exp w - x) / H ≤ -1 := by
        rw [div_le_iff₀ hH]
        nlinarith
      rw [abs_of_nonpos (hquot.trans (by norm_num))]
      linarith
    · have hexp : (x + H) / X < Real.exp w := by
        rw [← Real.exp_log hb]
        exact Real.exp_lt_exp.mpr hwRight
      have hnum : H < X * Real.exp w - x := by
        have := (div_lt_iff₀ hX).mp hexp
        nlinarith
      have hquot : 1 < (X * Real.exp w - x) / H := by
        rw [lt_div_iff₀ hH]
        nlinarith
      rw [abs_of_pos (lt_trans (by norm_num) hquot)]
      exact hquot.le
  unfold sourcePacketAmplitude
  rw [hzero]
  simp

/-- Equation (80)'s full real-line integral is exactly its interval integral on
the cutoff-forced logarithmic window. -/
theorem sourceStationaryPacket_eq_onCutoffWindow
    {X H x beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    sourceStationaryPacket X H x beta t cutoff outerCutoff =
      stationaryPacketOn X beta t
        (sourcePacketAmplitude X H x cutoff outerCutoff)
        (Real.log ((x - H) / X)) (Real.log ((x + H) / X)) := by
  have hxMinus : 0 < x - H := by
    have : X / 4 ≤ x - H := by linarith
    exact lt_of_lt_of_le (by positivity : 0 < X / 4) this
  have hxPlus : 0 < x + H := by linarith
  have hwindowOrder : Real.log ((x - H) / X) ≤ Real.log ((x + H) / X) := by
    apply Real.log_le_log (div_pos hxMinus hX)
    apply div_le_div_of_nonneg_right _ hX.le
    linarith
  let integrand : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x cutoff outerCutoff w
  have hindicator : integrand = Set.indicator
      (Set.Ioc (Real.log ((x - H) / X)) (Real.log ((x + H) / X))) integrand := by
    funext w
    by_cases hw : w ∈ Set.Ioc (Real.log ((x - H) / X))
        (Real.log ((x + H) / X))
    · simp [hw]
    · have hz := sourcePacketAmplitude_eq_zero_of_not_mem_Ioc (outerCutoff := outerCutoff)
          hX hH hHquarter hxLower hcutoffSupport hw
      simp [integrand, hw, hz]
  unfold sourceStationaryPacket stationaryPacketOn
  change (∫ w : ℝ, integrand w) = _
  rw [hindicator, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hwindowOrder]

/-- Under the MAP range `x ≥ X/2`, `H ≤ X/4`, the exact logarithmic support
window has length at most `8H/X`.  This is the quantitative change-of-variables
fact behind the paper's trivial `Jₓ(t) ≪ H/X` estimate. -/
theorem sourcePacketWindow_length_le
    {X H x : ℝ} (hX : 0 < X) (hH : 0 ≤ H)
    (hHquarter : H ≤ X / 4) (hxLower : X / 2 ≤ x) :
    |Real.log ((x + H) / X) - Real.log ((x - H) / X)| ≤ 8 * H / X := by
  have hxMinusLower : X / 4 ≤ x - H := by linarith
  have hxMinus : 0 < x - H := lt_of_lt_of_le (by positivity : 0 < X / 4) hxMinusLower
  have hxPlus : 0 < x + H := by linarith
  have ha : 0 < (x - H) / X := div_pos hxMinus hX
  have hb : 0 < (x + H) / X := div_pos hxPlus hX
  have hlogNonneg :
      0 ≤ Real.log ((x + H) / X) - Real.log ((x - H) / X) := by
    exact sub_nonneg.mpr (Real.log_le_log ha (by
      apply div_le_div_of_nonneg_right _ hX.le
      linarith))
  rw [abs_of_nonneg hlogNonneg, ← Real.log_div hb.ne' ha.ne']
  calc
    Real.log (((x + H) / X) / ((x - H) / X)) ≤
        ((x + H) / X) / ((x - H) / X) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hb ha)
    _ = 2 * H / (x - H) := by
      field_simp [ne_of_gt hX, ne_of_gt hxMinus]
      ring
    _ ≤ 8 * H / X := by
      rw [div_le_div_iff₀ hxMinus hX]
      have hmul := mul_le_mul_of_nonneg_left hxMinusLower hH
      nlinarith

/-- On its exact cutoff window, the literal amplitude in (80) has norm at
most `3` when both cutoffs have absolute value at most one.  The numerical
constant comes only from `x ≤ 4X` and `H ≤ X/4`. -/
theorem norm_sourcePacketAmplitude_le_three
    {X H x w : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X H x)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (houter : ∀ y, |outerCutoff y| ≤ 1) :
    ‖sourcePacketAmplitude X H x cutoff outerCutoff w‖ ≤ 3 := by
  have hxPlus : 0 < x + H := by
    linarith
  have hratioPos : 0 < (x + H) / X := div_pos hxPlus hX
  have hexpUpper : Real.exp w ≤ (x + H) / X := by
    rw [← Real.exp_log hratioPos]
    exact Real.exp_le_exp.mpr hw.2
  have hratioFive : (x + H) / X ≤ 5 := by
    rw [div_le_iff₀ hX]
    nlinarith
  have hexpFive : Real.exp w ≤ 5 := hexpUpper.trans hratioFive
  have hexpHalfSquare : Real.exp (w / 2) ^ 2 = Real.exp w := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hexpHalfThree : Real.exp (w / 2) ≤ 3 := by
    nlinarith [Real.exp_pos (w / 2)]
  unfold sourcePacketAmplitude
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          |outerCutoff (w / 100)| ≤ 3 * 1 * 1 := by
      gcongr
      · exact hcutoff _
      · exact houter _
    _ = 3 := by norm_num

/-- Explicit small-support packet bound for the literal amplitude in (80).
This compiles the paper's triangle-inequality estimate `Jₓ(t) ≪ H/X` on the
cutoff-forced logarithmic window, with constant `24`. -/
theorem norm_sourcePacketOnCutoffWindow_le
    {X H x beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (houter : ∀ y, |outerCutoff y| ≤ 1) :
    ‖stationaryPacketOn X beta t
        (sourcePacketAmplitude X H x cutoff outerCutoff)
        (Real.log ((x - H) / X)) (Real.log ((x + H) / X))‖ ≤
      24 * H / X := by
  have hxMinus : 0 < x - H := by
    have : X / 4 ≤ x - H := by linarith
    exact lt_of_lt_of_le (by positivity : 0 < X / 4) this
  have hxPlus : 0 < x + H := by linarith
  have hwindowOrder : Real.log ((x - H) / X) ≤ Real.log ((x + H) / X) := by
    apply Real.log_le_log (div_pos hxMinus hX)
    apply div_le_div_of_nonneg_right _ hX.le
    linarith
  have hamp : ∀ w ∈ Set.uIcc (Real.log ((x - H) / X))
      (Real.log ((x + H) / X)),
      ‖sourcePacketAmplitude X H x cutoff outerCutoff w‖ ≤ 3 := by
    intro w hw
    have hw' : w ∈ sourcePacketWindow X H x := by
      simpa [sourcePacketWindow, Set.uIcc_of_le hwindowOrder] using hw
    exact norm_sourcePacketAmplitude_le_three hX hH hHquarter hxLower hxUpper
      hw' hcutoff houter
  refine (norm_stationaryPacketOn_le hamp).trans ?_
  have hlength := sourcePacketWindow_length_le hX hH hHquarter hxLower
  calc
    |Real.log ((x + H) / X) - Real.log ((x - H) / X)| * 3 ≤
        (8 * H / X) * 3 := mul_le_mul_of_nonneg_right hlength (by norm_num)
    _ = 24 * H / X := by ring

/-- Literal whole-line version of the small-support packet estimate from the
second case below (83): `|Jₓ(t)| ≤ 24 H/X`. -/
theorem norm_sourceStationaryPacket_le
    {X H x beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff : ∀ y, |cutoff y| ≤ 1)
    (houter : ∀ y, |outerCutoff y| ≤ 1) :
    ‖sourceStationaryPacket X H x beta t cutoff outerCutoff‖ ≤ 24 * H / X := by
  rw [sourceStationaryPacket_eq_onCutoffWindow hX hH hHquarter hxLower
    hcutoffSupport]
  exact norm_sourcePacketOnCutoffWindow_le hX hH.le hHquarter hxLower hxUpper
    hcutoff houter

/-- On the literal source support the second derivative of the phase has the
lower bound used by the van der Corput step in the first case below (83). -/
theorem stationaryPacketPhase_curvature_lower_on_sourceWindow
    {X H x beta w : ℝ} (hX : 0 < X)
    (hHquarter : H ≤ X / 4) (hxLower : X / 2 ≤ x)
    (hw : w ∈ sourcePacketWindow X H x) :
    |beta| * X / 4 ≤ |beta * X * Real.exp w| := by
  have hxMinusLower : X / 4 ≤ x - H := by linarith
  have hxMinus : 0 < x - H := lt_of_lt_of_le (by positivity : 0 < X / 4) hxMinusLower
  have ha : 0 < (x - H) / X := div_pos hxMinus hX
  have hexpLower : (x - H) / X ≤ Real.exp w := by
    rw [← Real.exp_log ha]
    exact Real.exp_le_exp.mpr hw.1
  have hquarterExp : 1 / 4 ≤ Real.exp w := by
    have hratio : 1 / 4 ≤ (x - H) / X := by
      rw [le_div_iff₀ hX]
      nlinarith
    exact hratio.trans hexpLower
  rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
  have hmul := mul_le_mul_of_nonneg_left hquarterExp (abs_nonneg beta)
  nlinarith [mul_nonneg (abs_nonneg beta) hX.le]

end

end MAPMRTProposition51HardBranch
