import MRTNonstationaryPhaseInverse
import MRTVanDerCorput

/-! The literal second derivative of the amplitude in MRT equation (80). -/

namespace MAPMRTSourcePacketAmplitudeC2

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTVanDerCorput

noncomputable section

def sourcePacketAmplitudeSecond
    (X H x : ℝ)
    (cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ)
    (w : ℝ) : ℂ :=
  ((Real.exp (w / 2) / 4 : ℝ) : ℂ) *
      (cutoff ((X * Real.exp w - x) / H) : ℂ) * (outer (w / 100) : ℂ) +
    2 * (Real.exp (w / 2) : ℂ) *
      ((cutoff' ((X * Real.exp w - x) / H) *
        (X * Real.exp w / H) : ℝ) : ℂ) * (outer (w / 100) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      ((cutoff'' ((X * Real.exp w - x) / H) *
        (X * Real.exp w / H) ^ 2 : ℝ) : ℂ) * (outer (w / 100) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      (cutoff ((X * Real.exp w - x) / H) : ℂ) *
        ((outer' (w / 100) / 100 : ℝ) : ℂ) +
    2 * (Real.exp (w / 2) : ℂ) *
      ((cutoff' ((X * Real.exp w - x) / H) *
        (X * Real.exp w / H) : ℝ) : ℂ) *
          ((outer' (w / 100) / 100 : ℝ) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      (cutoff ((X * Real.exp w - x) / H) : ℂ) *
        ((outer'' (w / 100) / 10000 : ℝ) : ℂ)

theorem hasDerivAt_sourcePacketAmplitudeDeriv
    {X H x w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hcutoff : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoff' : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houter : ∀ y, HasDerivAt outer (outer' y) y)
    (houter' : ∀ y, HasDerivAt outer' (outer'' y) y) :
    HasDerivAt (sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer')
      (sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff''
        outer outer' outer'' w) w := by
  have he : HasDerivAt (fun y : ℝ ↦ Real.exp (y / 2))
      (Real.exp (w / 2) / 2) w := by
    convert Real.hasDerivAt_exp (w / 2) |>.scomp w
      ((hasDerivAt_id w).div_const 2) using 1 <;> ring
  have hz : HasDerivAt (fun y : ℝ ↦ (X * Real.exp y - x) / H)
      (X * Real.exp w / H) w := by
    convert ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H
      using 1 <;> ring
  have hr : HasDerivAt (fun y : ℝ ↦ X * Real.exp y / H)
      (X * Real.exp w / H) w := by
    convert (Real.hasDerivAt_exp w).const_mul X |>.div_const H using 1 <;> ring
  have hoarg : HasDerivAt (fun y : ℝ ↦ y / 100) (1 / 100) w := by
    convert (hasDerivAt_id w).div_const 100 using 1 <;> ring
  have hc := (hcutoff _).scomp w hz
  have hc' := (hcutoff' _).scomp w hz
  have ho := (houter _).scomp w hoarg
  have ho' := (houter' _).scomp w hoarg
  unfold sourcePacketAmplitudeDeriv sourcePacketAmplitudeSecond
  convert (((he.div_const 2).ofReal_comp.mul hc.ofReal_comp).mul ho.ofReal_comp).add
      (((he.ofReal_comp.mul (hc'.mul hr).ofReal_comp).mul ho.ofReal_comp).add
        ((he.ofReal_comp.mul hc.ofReal_comp).mul
          (ho'.div_const 100).ofReal_comp)) using 1
  · funext z
    simp only [Function.comp_def, Function.comp_apply, Pi.add_apply, Pi.mul_apply, one_div,
      smul_eq_mul]
    push_cast
    ring
  · simp only [Function.comp_def, one_div, smul_eq_mul]
    push_cast
    simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, Function.comp_def,
      smul_eq_mul]
    push_cast
    ring

/-- On the exact logarithmic cutoff window, the first phase derivative stays
at least three quarters of its value at the packet center.  This is the
literal geometric input following (84). -/
theorem stationaryPacketPhase_deriv_lower_on_cutoffWindow
    {X H x beta t D w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hD : 0 ≤ D)
    (hcenter : D ≤ |t / (2 * Real.pi) + beta * x|)
    (hscale : 4 * |beta| * H ≤ D)
    (hw : w ∈ sourcePacketWindow X H x) :
    3 * D / 4 ≤ |beta * X * Real.exp w + t / (2 * Real.pi)| := by
  have hxMinus : 0 < x - H := by linarith
  have hxPlus : 0 < x + H := by linarith
  have hlow : x - H ≤ X * Real.exp w := by
    have hr : (x - H) / X ≤ Real.exp w := by
      rw [← Real.exp_log (div_pos hxMinus hX)]
      exact Real.exp_le_exp.mpr hw.1
    simpa [mul_comm] using (div_le_iff₀ hX).mp hr
  have hupp : X * Real.exp w ≤ x + H := by
    have hr : Real.exp w ≤ (x + H) / X := by
      rw [← Real.exp_log (div_pos hxPlus hX)]
      exact Real.exp_le_exp.mpr hw.2
    simpa [mul_comm] using (le_div_iff₀ hX).mp hr
  have hclose : |X * Real.exp w - x| ≤ H := by
    rw [abs_le]
    constructor <;> linarith
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
  have : |t / (2 * Real.pi) + beta * x| - D / 4 ≤
      |t / (2 * Real.pi) + beta * X * Real.exp w| := by linarith
  rw [show beta * X * Real.exp w + t / (2 * Real.pi) =
      t / (2 * Real.pi) + beta * X * Real.exp w by ring]
  linarith

/-- Both the amplitude and its first derivative vanish at each endpoint of
the exact cutoff window when the cutoff and its derivative vanish at `±1`. -/
theorem sourcePacketAmplitude_cutoffWindow_endpoints
    {X H x : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutNeg : cutoff (-1) = 0) (hcutPos : cutoff 1 = 0)
    (hcut'Neg : cutoff' (-1) = 0) (hcut'Pos : cutoff' 1 = 0) :
    let a := Real.log ((x - H) / X)
    let b := Real.log ((x + H) / X)
    sourcePacketAmplitude X H x cutoff outer a = 0 ∧
      sourcePacketAmplitude X H x cutoff outer b = 0 ∧
      sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' a = 0 ∧
      sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' b = 0 := by
  dsimp
  have hxMinus : 0 < x - H := by linarith
  have hxPlus : 0 < x + H := by linarith
  have hza : (X * Real.exp (Real.log ((x - H) / X)) - x) / H = -1 := by
    rw [Real.exp_log (div_pos hxMinus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  have hzb : (X * Real.exp (Real.log ((x + H) / X)) - x) / H = 1 := by
    rw [Real.exp_log (div_pos hxPlus hX)]
    field_simp [ne_of_gt hX, ne_of_gt hH]
    ring
  constructor
  · simp [sourcePacketAmplitude, hza, hcutNeg]
  constructor
  · simp [sourcePacketAmplitude, hzb, hcutPos]
  constructor
  · simp [sourcePacketAmplitudeDeriv, hza, hcutNeg, hcut'Neg]
  · simp [sourcePacketAmplitudeDeriv, hzb, hcutPos, hcut'Pos]

#print axioms hasDerivAt_sourcePacketAmplitudeDeriv
#print axioms stationaryPacketPhase_deriv_lower_on_cutoffWindow
#print axioms sourcePacketAmplitude_cutoffWindow_endpoints

end
end MAPMRTSourcePacketAmplitudeC2
