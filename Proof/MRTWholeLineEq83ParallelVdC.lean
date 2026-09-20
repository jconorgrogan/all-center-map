import MRTVanDerCorput

/-!
# Whole-line van der Corput bound for the MRT source packet

The proof already used for the restricted equation-(83) packet only depends
on the fixed outer window `[-100,100]`; its printed `x`-range hypotheses are
logically unused.  This module records the source-faithful unrestricted form.
-/

namespace MAPMRTWholeLineEq83ParallelVdC

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTVanDerCorput

noncomputable section

/-- Uniform second-derivative estimate on the literal whole-line packet.
The curvature floor is supplied by the fixed outer cutoff, not by a sharp
restriction on the arithmetic center `x`. -/
theorem norm_sourceStationaryPacket_le_vdc_wholeLine
    {X H x beta t Dcut Dout : ℝ}
    {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hbeta : beta ≠ 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outer')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (houter'Int : Integrable (fun y ↦ |outer' y|))
    (hDcut : (∫ y : ℝ, |cutoff' y|) ≤ Dcut)
    (hDout : (∫ y : ℝ, |outer' y|) ≤ Dout) :
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      10 * Real.exp 50 * (101 + Dcut + Dout) /
        Real.sqrt (|beta| * X * Real.exp (-100)) := by
  let lambda : ℝ := |beta| * X * Real.exp (-100)
  let m : ℝ := Real.sqrt lambda
  have hlambda : 0 < lambda := by
    unfold lambda
    positivity
  have hm : 0 < m := by
    unfold m
    positivity
  have hmSq : m ^ 2 = lambda := by
    unfold m
    exact Real.sq_sqrt hlambda.le
  have hphaseSign :
      (∀ w ∈ Set.Icc (-100 : ℝ) 100, 0 ≤ beta * X * Real.exp w) ∨
      (∀ w ∈ Set.Icc (-100 : ℝ) 100, beta * X * Real.exp w ≤ 0) := by
    rcases le_total 0 beta with hbetaNonneg | hbetaNonpos
    · left
      intro w hw
      positivity
    · right
      intro w hw
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hbetaNonpos hX.le)
        (Real.exp_pos w).le
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (houterDeriv y).continuousAt)
  have hampDerivCont : Continuous
      (sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer') := by
    unfold sourcePacketAmplitudeDeriv
    fun_prop
  have hampBound : ∀ w ∈ Set.Icc (-100 : ℝ) 100,
      ‖sourcePacketAmplitude X H x cutoff outer w‖ ≤ Real.exp 50 := by
    intro w hw
    unfold sourcePacketAmplitude
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (w / 2) ≤ Real.exp 50 := by
      apply Real.exp_le_exp.mpr
      linarith [hw.2]
    calc
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          |outer (w / 100)| ≤ Real.exp 50 * 1 * 1 := by
        gcongr
        · exact hcutoffBound _
        · exact houterBound _
      _ = Real.exp 50 := by ring
  have hvdc := MAPMRTVanDerCorputProof.weightedSecondDerivativeVanDerCorputC1
    (a := (-100 : ℝ)) (b := 100) (m := m) (M := Real.exp 50)
    (phase := stationaryPacketPhase X beta t)
    (phase' := fun w ↦ beta * X * Real.exp w + t / (2 * Real.pi))
    (phase'' := fun w ↦ beta * X * Real.exp w)
    (amplitude := sourcePacketAmplitude X H x cutoff outer)
    (amplitude' := sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer')
    (by norm_num) hm (Real.exp_pos 50).le
    (fun w _hw ↦ hasDerivAt_stationaryPacketPhase X beta t w)
    (fun w _hw ↦ hasDerivAt_stationaryPacketPhase_firstDerivative X beta t w)
    (fun w hw ↦ by
      rw [hmSq]
      exact stationaryPacketPhase_curvature_lower_on_outerWindow hX.le hw)
    hphaseSign
    (fun w _hw ↦ hasDerivAt_sourcePacketAmplitude hcutoffDeriv houterDeriv)
    (by fun_prop) hampDerivCont.continuousOn hampBound
  have hvariation := integral_norm_sourcePacketAmplitudeDeriv_le
    (X := X) (H := H) (x := x) (Dcut := Dcut) (Dout := Dout)
    (cutoff := cutoff) (cutoff' := cutoff')
    (outerCutoff := outer) (outerCutoff' := outer')
    hX hH hcutoffBound houterBound hcutoffDeriv houterDeriv
    hcutoff'Cont houter'Cont hcutoff'Int houter'Int hDcut hDout
  rw [sourceStationaryPacket_eq_onOuterWindow houterSupport]
  unfold stationaryPacketOn
  refine hvdc.trans ?_
  rw [show m = Real.sqrt (|beta| * X * Real.exp (-100)) by rfl]
  apply div_le_div_of_nonneg_right _ hm.le
  calc
    10 * (Real.exp 50 +
        ∫ w : ℝ in (-100)..100,
          ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖) ≤
        10 * (Real.exp 50 + Real.exp 50 * (100 + Dcut + Dout)) := by
      gcongr
    _ = 10 * Real.exp 50 * (101 + Dcut + Dout) := by ring

#print axioms norm_sourceStationaryPacket_le_vdc_wholeLine

end
end MAPMRTWholeLineEq83ParallelVdC
