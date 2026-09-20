import MRTVanDerCorput

/-!
# Whole-line stationary-packet van der Corput bound

The MRT weighted second-derivative argument is uniform in the arithmetic
center `x`.  The earlier public specialization carried two unused sharp-cell
hypotheses; this source-facing version records the literal whole-line estimate
needed after the legal pre-Cauchy extension.
-/

namespace MAPMRTWholeLineVanDerCorput

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTProposition51Source
open MAPMRTCorollary53Source
open MAPMRTVanDerCorput

noncomputable section

theorem norm_sourceStationaryPacket_le_wholeLine_vdc
    {X H x beta eta t Dcut Dout : ℝ}
    {cutoff cutoff' outerCutoff outerCutoff' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (_hetaPos : 0 < eta) (_hetaHard : eta < 1 / 100)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outerCutoff y| ≤ 1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outerCutoff (outerCutoff' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outerCutoff')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (houter'Int : Integrable (fun y ↦ |outerCutoff' y|))
    (hDcut : (∫ y : ℝ, |cutoff' y|) ≤ Dcut)
    (hDout : (∫ y : ℝ, |outerCutoff' y|) ≤ Dout) :
    ‖sourceStationaryPacket X H x beta t cutoff outerCutoff‖ ≤
      10 * Real.exp 50 * (101 + Dcut + Dout) /
        Real.sqrt (|beta| * X * Real.exp (-100)) := by
  have hX : 0 < X := by linarith
  have hbeta : beta ≠ 0 := by
    intro hb
    subst beta
    norm_num at hhard
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
        (mul_nonpos_of_nonpos_of_nonneg hbetaNonpos hX.le) (Real.exp_pos w).le
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outerCutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hampDerivCont : Continuous
      (sourcePacketAmplitudeDeriv X H x cutoff cutoff'
        outerCutoff outerCutoff') := by
    unfold sourcePacketAmplitudeDeriv
    fun_prop
  have hampBound : ∀ w ∈ Set.Icc (-100 : ℝ) 100,
      ‖sourcePacketAmplitude X H x cutoff outerCutoff w‖ ≤ Real.exp 50 := by
    intro w hw
    unfold sourcePacketAmplitude
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (w / 2) ≤ Real.exp 50 := by
      apply Real.exp_le_exp.mpr
      have hwUpper := hw.2
      linarith
    calc
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          |outerCutoff (w / 100)| ≤ Real.exp 50 * 1 * 1 := by
        gcongr
        · exact hcutoffBound _
        · exact houterBound _
      _ = Real.exp 50 := by ring
  have hvdc := MAPMRTVanDerCorputProof.weightedSecondDerivativeVanDerCorputC1
    (a := (-100 : ℝ)) (b := 100) (m := m) (M := Real.exp 50)
    (phase := stationaryPacketPhase X beta t)
    (phase' := fun w ↦ beta * X * Real.exp w + t / (2 * Real.pi))
    (phase'' := fun w ↦ beta * X * Real.exp w)
    (amplitude := sourcePacketAmplitude X H x cutoff outerCutoff)
    (amplitude' := sourcePacketAmplitudeDeriv X H x cutoff cutoff'
      outerCutoff outerCutoff')
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
    (outerCutoff := outerCutoff) (outerCutoff' := outerCutoff')
    hX (lt_of_lt_of_le zero_lt_one hH) hcutoffBound houterBound
    hcutoffDeriv houterDeriv hcutoff'Cont houter'Cont
    hcutoff'Int houter'Int hDcut hDout
  rw [sourceStationaryPacket_eq_onOuterWindow houterSupport]
  unfold stationaryPacketOn
  refine hvdc.trans ?_
  rw [show m = Real.sqrt (|beta| * X * Real.exp (-100)) by rfl]
  apply div_le_div_of_nonneg_right _ hm.le
  calc
    10 * (Real.exp 50 +
        ∫ w : ℝ in (-100)..100,
          ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff'
            outerCutoff outerCutoff' w‖) ≤
        10 * (Real.exp 50 + Real.exp 50 * (100 + Dcut + Dout)) := by
      gcongr
    _ = 10 * Real.exp 50 * (101 + Dcut + Dout) := by ring


#print axioms norm_sourceStationaryPacket_le_wholeLine_vdc

end
end MAPMRTWholeLineVanDerCorput
