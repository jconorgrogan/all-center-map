import MRTProposition51HardBranch

/-!
# MRT Proposition 5.1: the literal low-frequency amplitude

This module isolates equation (78) on pp. 46--47 of Matomäki--Radziwiłł--Tao.
The frequency scale and every chain-rule coefficient are kept literal.  The
Fourier kernel is an argument because the later source specialization is
`cutoffFourierKernel cutoff`.
-/

namespace MAPMRTProposition51ProjectionLowAmplitude

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch

noncomputable section

/-- The exact low-frequency scale `10 η |β| X` in (76). -/
def lowProjectionScale (X beta eta : ℝ) : ℝ :=
  10 * eta * |beta| * X

/-- The affine Fourier-kernel argument after
`w = u - 2πv/(10η|β|X)`. -/
def lowKernelArgument (X beta eta u w : ℝ) : ℝ :=
  lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)

/-- The amplitude `ψ_{x,u}` in equation (78), with the paper's physical
cutoff and Fourier kernel kept separate. -/
def lowProjectionAmplitude
    (X H beta eta x u : ℝ) (cutoff : ℝ → ℝ) (kernel : ℝ → ℂ)
    (w : ℝ) : ℂ :=
  (Real.exp (w / 2) : ℂ) *
    kernel (lowKernelArgument X beta eta u w) *
      (cutoff ((X * Real.exp w - x) / H) : ℂ)

/-- The literal derivative obtained from (78). -/
def lowProjectionAmplitudeDeriv
    (X H beta eta x u : ℝ)
    (cutoff cutoff' : ℝ → ℝ) (kernel kernel' : ℝ → ℂ)
    (w : ℝ) : ℂ :=
  ((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
      kernel (lowKernelArgument X beta eta u w) *
        (cutoff ((X * Real.exp w - x) / H) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      ((-(lowProjectionScale X beta eta / (2 * Real.pi)) : ℝ) : ℂ) *
        kernel' (lowKernelArgument X beta eta u w) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) +
    (Real.exp (w / 2) : ℂ) *
      kernel (lowKernelArgument X beta eta u w) *
        (cutoff' ((X * Real.exp w - x) / H) : ℂ) *
          (((X * Real.exp w) / H : ℝ) : ℂ)

theorem hasDerivAt_lowKernelArgument
    (X beta eta u w : ℝ) :
    HasDerivAt (lowKernelArgument X beta eta u)
      (-(lowProjectionScale X beta eta / (2 * Real.pi))) w := by
  unfold lowKernelArgument
  convert ((hasDerivAt_const w u).sub (hasDerivAt_id w)).const_mul
    (lowProjectionScale X beta eta / (2 * Real.pi)) using 1 <;> ring

theorem hasDerivAt_physicalCutoffArgument
    {X H x w : ℝ} (hH : H ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ (X * Real.exp z - x) / H)
      ((X * Real.exp w) / H) w := by
  convert (((Real.hasDerivAt_exp w).const_mul X).sub_const x).div_const H
    using 1 <;> field_simp [hH]

/-- Exact chain-rule identity behind the derivative estimate immediately
after (78). -/
theorem hasDerivAt_lowProjectionAmplitude
    {X H beta eta x u w : ℝ}
    {cutoff cutoff' : ℝ → ℝ} {kernel kernel' : ℝ → ℂ}
    (hH : H ≠ 0)
    (hcutoff : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hkernel : ∀ y, HasDerivAt kernel (kernel' y) y) :
    HasDerivAt
      (lowProjectionAmplitude X H beta eta x u cutoff kernel)
      (lowProjectionAmplitudeDeriv X H beta eta x u
        cutoff cutoff' kernel kernel' w) w := by
  have hexp : HasDerivAt (fun z : ℝ ↦ (Real.exp (z / 2) : ℂ))
      (((Real.exp (w / 2) / 2 : ℝ) : ℂ)) w := by
    have hr := (Real.hasDerivAt_exp (w / 2)).comp w
      ((hasDerivAt_id w).div_const 2)
    convert hr.ofReal_comp using 1 <;> push_cast <;> ring
  have hkarg := hasDerivAt_lowKernelArgument X beta eta u w
  have hk : HasDerivAt
      (fun z ↦ kernel (lowKernelArgument X beta eta u z))
      (((-(lowProjectionScale X beta eta / (2 * Real.pi)) : ℝ) : ℂ) *
        kernel' (lowKernelArgument X beta eta u w)) w := by
    convert HasDerivAt.scomp w (hkernel _) hkarg using 1 <;> push_cast <;> ring
  have hcarg := hasDerivAt_physicalCutoffArgument (X := X) (x := x)
    (w := w) hH
  have hcReal := (hcutoff _).comp w hcarg
  have hc : HasDerivAt
      (fun z ↦ (cutoff ((X * Real.exp z - x) / H) : ℂ))
      ((cutoff' ((X * Real.exp w - x) / H) : ℂ) *
        (((X * Real.exp w) / H : ℝ) : ℂ)) w := by
    simpa only [Function.comp_apply, Complex.ofReal_mul] using hcReal.ofReal_comp
  unfold lowProjectionAmplitude lowProjectionAmplitudeDeriv
  have hprod := (hexp.mul hk).mul hc
  convert hprod using 1
  simp only [Pi.mul_apply]
  ring

/-- The physical cutoff forces the exact source condition
`|Xe^w-x| < H`; endpoint vanishing is included. -/
theorem lowProjectionAmplitude_eq_zero_of_physical_outside
    {X H beta eta x u w : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hH : 0 < H) (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houtside : H ≤ |X * Real.exp w - x|) :
    lowProjectionAmplitude X H beta eta x u cutoff kernel w = 0 := by
  have hquot : 1 ≤ |(X * Real.exp w - x) / H| := by
    rw [abs_div, abs_of_pos hH]
    exact (le_div_iff₀ hH).2 (by simpa [mul_comm] using houtside)
  unfold lowProjectionAmplitude
  rw [hcutoffSupport _ hquot]
  simp

/-- On the MAP quarter-range support, the exponential half-density in (78)
is bounded by `3`. -/
theorem exp_half_le_three_of_physical_inside
    {X H x w : ℝ} (hX : 0 < X) (hH : 0 ≤ H)
    (hHquarter : H ≤ X / 4) (hxUpper : x ≤ 4 * X)
    (hinside : |X * Real.exp w - x| ≤ H) :
    Real.exp (w / 2) ≤ 3 := by
  have hupper : X * Real.exp w ≤ x + H := by
    have := (abs_le.mp hinside).2
    linarith
  have hexp : Real.exp w ≤ 17 / 4 := by
    nlinarith [Real.exp_pos w]
  have hsquare : Real.exp (w / 2) ^ 2 = Real.exp w := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.exp_pos (w / 2)]

end
end MAPMRTProposition51ProjectionLowAmplitude

#print axioms MAPMRTProposition51ProjectionLowAmplitude.hasDerivAt_lowProjectionAmplitude
#print axioms MAPMRTProposition51ProjectionLowAmplitude.lowProjectionAmplitude_eq_zero_of_physical_outside
#print axioms MAPMRTProposition51ProjectionLowAmplitude.exp_half_le_three_of_physical_inside
