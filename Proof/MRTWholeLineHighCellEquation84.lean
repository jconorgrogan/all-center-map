import MRTSourcePacketEquation84Bound
import MRTWholeLinePacketMemLp

/-!
# Whole-line high-cell form of MRT equation (84)

After the legal pre-Cauchy extension in MRT Proposition 5.1, the spatial
variable is no longer confined to `[X/2,4X]`.  On the high cell `x ≥ 4H` we
recenter the logarithmic variable at `x`, apply the already certified sharp
equation-(84) theorem at base scale `x`, and use the fixed outer cutoff to
compare `x` back with `X`.  No frequency-band hypothesis on `t` is needed.
-/

namespace MAPMRTWholeLineHighCellEquation84

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTSourcePacketEquation84Bound MAPMRTWholeLinePacketMemLp
open MAPMRTVanDerCorputProof

noncomputable section

/-- Translation of the fixed outer cutoff after recentering
`w = v + log(x/X)`. -/
def shiftedOuter (outer : ℝ → ℝ) (r z : ℝ) : ℝ :=
  outer (z + r / 100)

private theorem additivePhase_add (a b : ℝ) :
    additivePhase (a + b) = additivePhase a * additivePhase b := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact recentering identity for the unrestricted source packet. -/
theorem sourceStationaryPacket_recenter
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hx : 0 < x) :
    let r := Real.log (x / X)
    sourceStationaryPacket X H x beta t cutoff outer =
      additivePhase (t * r / (2 * Real.pi)) *
        (Real.exp (r / 2) : ℂ) *
          sourceStationaryPacket x H x beta t cutoff (shiftedOuter outer r) := by
  dsimp
  let r : ℝ := Real.log (x / X)
  let f : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x cutoff outer w
  have hratio : 0 < x / X := div_pos hx hX
  have hexpr : Real.exp r = x / X := by
    unfold r
    exact Real.exp_log hratio
  have hXexp : X * Real.exp r = x := by
    rw [hexpr]
    field_simp [hX.ne']
  have hshift : (∫ w : ℝ, f w) = ∫ v : ℝ, f (r + v) := by
    symm
    exact (measurePreserving_add_left volume r).integral_comp
      (Homeomorph.addLeft r).measurableEmbedding f
  unfold sourceStationaryPacket
  change (∫ w : ℝ, f w) = _
  rw [hshift]
  have hpoint : ∀ v : ℝ,
      f (r + v) =
        (additivePhase (t * r / (2 * Real.pi)) *
          (Real.exp (r / 2) : ℂ)) *
        (additivePhase (stationaryPacketPhase x beta t v) *
          sourcePacketAmplitude x H x cutoff (shiftedOuter outer r) v) := by
    intro v
    have hphase : stationaryPacketPhase X beta t (r + v) =
        t * r / (2 * Real.pi) + stationaryPacketPhase x beta t v := by
      unfold stationaryPacketPhase
      rw [Real.exp_add]
      have hbetaexp : beta * X * (Real.exp r * Real.exp v) =
          beta * x * Real.exp v := by
        calc
          beta * X * (Real.exp r * Real.exp v) =
              beta * (X * Real.exp r) * Real.exp v := by ring
          _ = beta * x * Real.exp v := by rw [hXexp]
      rw [hbetaexp]
      ring
    have hamp : sourcePacketAmplitude X H x cutoff outer (r + v) =
        (Real.exp (r / 2) : ℂ) *
          sourcePacketAmplitude x H x cutoff (shiftedOuter outer r) v := by
      unfold sourcePacketAmplitude shiftedOuter
      rw [show (r + v) / 2 = r / 2 + v / 2 by ring, Real.exp_add]
      rw [Real.exp_add]
      rw [show X * (Real.exp r * Real.exp v) = x * Real.exp v by
        rw [← mul_assoc, hXexp]]
      rw [show (r + v) / 100 = v / 100 + r / 100 by ring]
      push_cast
      ring
    unfold f
    rw [hphase, additivePhase_add, hamp]
    ring
  rw [show (∫ v : ℝ, f (r + v)) =
      ∫ v : ℝ,
        (additivePhase (t * r / (2 * Real.pi)) *
          (Real.exp (r / 2) : ℂ)) *
        (additivePhase (stationaryPacketPhase x beta t v) *
          sourcePacketAmplitude x H x cutoff (shiftedOuter outer r) v) by
    apply integral_congr_ae
    filter_upwards with v
    exact hpoint v]
  rw [integral_const_mul]

/-- Derivatives of the outer cutoff transport without loss under recentering. -/
theorem hasDerivAt_shiftedOuter
    {outer outer' : ℝ → ℝ} (r z : ℝ)
    (houter : ∀ y, HasDerivAt outer (outer' y) y) :
    HasDerivAt (shiftedOuter outer r) (shiftedOuter outer' r z) z := by
  unfold shiftedOuter
  have harg : HasDerivAt (fun y : ℝ ↦ y + r / 100) 1 z := by
    simpa using (hasDerivAt_id z).add_const (r / 100)
  simpa using (houter (z + r / 100)).scomp z harg

theorem continuous_shiftedOuter
    {outer : ℝ → ℝ} (r : ℝ) (houter : Continuous outer) :
    Continuous (shiftedOuter outer r) := by
  unfold shiftedOuter
  fun_prop

theorem abs_shiftedOuter_le
    {outer : ℝ → ℝ} {B r z : ℝ}
    (houter : ∀ y, |outer y| ≤ B) :
    |shiftedOuter outer r z| ≤ B := by
  exact houter _

/-- A nonzero high-cell packet lies at a fixed constant multiple of the base
scale.  This is the only place the outer support is used in the recentering
argument. -/
theorem highCell_x_le_four_thirds_exp100_mul_X_of_ne_zero
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hxHigh : 4 * H ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hne : sourceStationaryPacket X H x beta t cutoff outer ≠ 0) :
    x ≤ (4 / 3 : ℝ) * Real.exp 100 * X := by
  have hHle : H ≤ x / 4 := by linarith
  have hxCompact : x ∈ Set.Icc (-(X * Real.exp 100 + H))
      (X * Real.exp 100 + H) := by
    by_contra hnot
    exact hne (sourceStationaryPacket_eq_zero_outside_compact
      (beta := beta) (t := t) hX hH hcutoffSupport houterSupport hnot)
  have hxUpper := hxCompact.2
  calc
    x ≤ X * Real.exp 100 + H := hxUpper
    _ ≤ X * Real.exp 100 + x / 4 := by linarith
    _ ≤ (4 / 3 : ℝ) * Real.exp 100 * X := by
      have hxe : 0 ≤ X * Real.exp 100 := by positivity
      nlinarith

/-- The literal sharp equation-(84) coefficient already certified on the
base-scale cell. -/
def highCellEquation84BaseConstant (D1 D2 B1 B2 : ℝ) : ℝ :=
  1500 + 24 * (10 * (1 + B1) * (1 + D1)) +
    4 * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)

/-- Equation (84) for the unrestricted packet on `x ≥ 4H`.  The far threshold
is inflated only by the fixed outer-window factor `(4/3)e^100`; the output is
again at the original scale `X/H`. -/
theorem norm_sourceStationaryPacket_equation84_highCell
    {X H x beta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hxHigh : 4 * H ≤ x)
    (hcenter : 4 * max (|beta| * H)
      (((4 / 3 : ℝ) * Real.exp 100) * (X / H)) ≤
        |t / (2 * Real.pi) + beta * x|)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
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
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      (4 * Real.exp 200 * highCellEquation84BaseConstant D1 D2 B1 B2) *
        (X / H) / |t / (2 * Real.pi) + beta * x| ^ 2 := by
  let C := highCellEquation84BaseConstant D1 D2 B1 B2
  let K : ℝ := (4 / 3 : ℝ) * Real.exp 100
  let D : ℝ := |t / (2 * Real.pi) + beta * x|
  have hx : 0 < x := lt_of_lt_of_le (by positivity : 0 < 4 * H) hxHigh
  have hxQuarter : H ≤ x / 4 := by linarith
  have hB1 : 0 ≤ B1 := (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hB2 : 0 ≤ B2 := (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hD1n : 0 ≤ D1 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff' y))).trans hD1
  have hD2n : 0 ≤ D2 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff'' y))).trans hD2
  have hC : 0 ≤ C := by unfold C highCellEquation84BaseConstant; positivity
  have hK : 1 ≤ K := by
    unfold K
    have he : 1 ≤ Real.exp 100 := Real.one_le_exp (by norm_num)
    nlinarith
  by_cases hzero : sourceStationaryPacket X H x beta t cutoff outer = 0
  · rw [hzero, norm_zero]
    positivity
  · have hxBound := highCell_x_le_four_thirds_exp100_mul_X_of_ne_zero
        hX hH hxHigh hcutoffSupport houterSupport hzero
    have hxK : x ≤ K * X := by
      simpa [K, mul_assoc, mul_comm, mul_left_comm] using hxBound
    have hxRatio : x / H ≤ K * (X / H) := by
      simpa [mul_div_assoc] using div_le_div_of_nonneg_right hxK hH.le
    have hcenter' : 4 * max (|beta| * H) (x / H) ≤ D := by
      have hm : max (|beta| * H) (x / H) ≤
          max (|beta| * H) (K * (X / H)) :=
        max_le_max_left _ hxRatio
      exact (mul_le_mul_of_nonneg_left hm (by norm_num)).trans (by
        simpa [K, D] using hcenter)
    let r : ℝ := Real.log (x / X)
    let out0 : ℝ → ℝ := shiftedOuter outer r
    let out1 : ℝ → ℝ := shiftedOuter outer' r
    let out2 : ℝ → ℝ := shiftedOuter outer'' r
    have hout0 : ∀ y, |out0 y| ≤ 1 := fun y ↦ houterBound _
    have hout1 : ∀ y, |out1 y| ≤ B1 := fun y ↦ houter'Bound _
    have hout2 : ∀ y, |out2 y| ≤ B2 := fun y ↦ houter''Bound _
    have houtDeriv : ∀ y, HasDerivAt out0 (out1 y) y := by
      intro y
      exact hasDerivAt_shiftedOuter r y houterDeriv
    have houtSecond : ∀ y, HasDerivAt out1 (out2 y) y := by
      intro y
      exact hasDerivAt_shiftedOuter r y houterSecond
    have hout2Cont : Continuous out2 :=
      continuous_shiftedOuter r houter''Cont
    have hsharp := norm_sourceStationaryPacket_equation84_sharp
      (X := x) (H := H) (x := x) (beta := beta) (t := t)
      (D1 := D1) (D2 := D2) (B1 := B1) (B2 := B2)
      (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
      (outer := out0) (outer' := out1) (outer'' := out2)
      hx hH hxQuarter (by linarith) (by linarith) hcenter'
      hcutoffSupport hcutoff'Support hcutoffBound hout0 hout1 hout2
      hcutoffDeriv hcutoffSecond houtDeriv houtSecond
      hcutoff''Cont hout2Cont hcutoff'Int hcutoff''Int hD1 hD2
    have hratio : 0 < x / X := div_pos hx hX
    have hexpr : Real.exp r = x / X := by
      unfold r
      exact Real.exp_log hratio
    have hexpHalf : Real.exp (r / 2) ≤ K := by
      by_cases hr : r ≤ 0
      · exact (Real.exp_le_one_iff.mpr (by linarith)).trans hK
      · have hr0 : 0 ≤ r := le_of_not_ge hr
        have hh : r / 2 ≤ r := by linarith
        calc
          Real.exp (r / 2) ≤ Real.exp r := Real.exp_le_exp.mpr hh
          _ = x / X := hexpr
          _ ≤ K := by
            rw [div_le_iff₀ hX]
            simpa [mul_comm] using hxK
    have hxScale : x / H ≤ K * (X / H) := hxRatio
    have hKsq : K ^ 2 ≤ 4 * Real.exp 200 := by
      unfold K
      rw [show Real.exp 200 = Real.exp 100 * Real.exp 100 by
        rw [← Real.exp_add]
        norm_num]
      nlinarith [sq_nonneg (Real.exp 100)]
    have hscale : Real.exp (r / 2) * (x / H) ≤
        4 * Real.exp 200 * (X / H) := by
      calc
        Real.exp (r / 2) * (x / H) ≤ K * (K * (X / H)) := by
          gcongr
        _ = K ^ 2 * (X / H) := by ring
        _ ≤ 4 * Real.exp 200 * (X / H) := by
          gcongr
    have hrecenter := sourceStationaryPacket_recenter
      (X := X) (H := H) (x := x) (beta := beta) (t := t)
      (cutoff := cutoff) (outer := outer) hX hx
    have hnorm :
        ‖sourceStationaryPacket X H x beta t cutoff outer‖ =
          Real.exp (r / 2) *
            ‖sourceStationaryPacket x H x beta t cutoff out0‖ := by
      calc
        ‖sourceStationaryPacket X H x beta t cutoff outer‖ =
            ‖additivePhase (t * r / (2 * Real.pi))‖ *
              ‖(Real.exp (r / 2) : ℂ)‖ *
                ‖sourceStationaryPacket x H x beta t cutoff out0‖ := by
          rw [hrecenter, norm_mul, norm_mul]
        _ = Real.exp (r / 2) *
              ‖sourceStationaryPacket x H x beta t cutoff out0‖ := by
          rw [norm_additivePhase, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    have hDnonneg : 0 ≤ D ^ 2 := sq_nonneg D
    calc
      Real.exp (r / 2) *
          ‖sourceStationaryPacket x H x beta t cutoff out0‖ ≤
          Real.exp (r / 2) * (C * (x / H) / D ^ 2) := by
        gcongr
        simpa [C, D, out0, highCellEquation84BaseConstant] using hsharp
      _ = (C * (Real.exp (r / 2) * (x / H))) / D ^ 2 := by ring
      _ ≤ (C * (4 * Real.exp 200 * (X / H))) / D ^ 2 := by
        gcongr
      _ = (4 * Real.exp 200 * C) * (X / H) / D ^ 2 := by ring
      _ = _ := by rfl

#print axioms sourceStationaryPacket_recenter
#print axioms hasDerivAt_shiftedOuter
#print axioms highCell_x_le_four_thirds_exp100_mul_X_of_ne_zero
#print axioms norm_sourceStationaryPacket_equation84_highCell

end
end MAPMRTWholeLineHighCellEquation84
