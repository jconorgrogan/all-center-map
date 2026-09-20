import MRTSourceLowerCollarPhaseTwoIBP

/-! # Literal endpoint budgets on a lower-collar off-resonance cell -/

namespace MAPMRTSourceLowerCollarOffResonanceCell

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTVanDerCorput
open MAPMRTCorollary53Source MAPMRTSourcePacketAmplitudeC2
open MAPMRTSourceLowerCollarVdC MAPMRTSourceLowerCollarOffResonance
open MAPMRTSourceLowerCollarOffResonanceBudget
open MAPMRTSourceLowerCollarAmplitudeGain
open MAPMRTSourceLowerCollarPhaseTwoIBP

noncomputable section

/-- Pointwise `C⁰` budget at either artificial off-resonance endpoint. -/
theorem norm_sourceLowerCollarAmplitudeDifference_le_exp_half_budget
    {X x w U B1 : ℝ} {cutoff cutoff' outer : ℝ → ℝ}
    (hX : 0 < X) (hxLower : X / 2 ≤ x)
    (hU : 0 < U) (hwUpper : Real.exp w ≤ U) (hB1 : 0 ≤ B1)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (houterBound : ∀ z, |outer z| ≤ 1) :
    ‖sourceLowerCollarAmplitudeDifference
        X (X / 2) x cutoff outer w‖ ≤
      Real.exp (w / 2) * (4 * B1 * U) := by
  have h := norm_sourcePacketAmplitude_difference_on_resonanceCell_le
    (X := X) (x := x) (q := U / 2) (w := w) (B := B1)
    hX (by positivity) hxLower (by nlinarith) hB1
    hcutoffSupport hcutoffDeriv hcutoff'Bound houterBound
  change ‖sourcePacketAmplitude X (X / 2) x cutoff (fun _ ↦ 1) w -
      sourcePacketAmplitude X (X / 2) x cutoff outer w‖ ≤ _
  exact h.trans_eq (by ring)

/-- Pointwise `C¹` budget at either artificial off-resonance endpoint. -/
theorem norm_sourceLowerCollarAmplitudeDifferenceDeriv_le_exp_half_budget
    {X x w U B1 B2 Bo1 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hxLower : X / 2 ≤ x)
    (hU : 0 < U) (hwUpper : Real.exp w ≤ U)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bo1) :
    ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖ ≤
      Real.exp (w / 2) *
        (2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50) := by
  have h := norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
    (X := X) (x := x) (q := U / 2) (w := w)
    (B1 := B1) (B2 := B2) (Bout := Bo1)
    hX (by positivity) hxLower (by nlinarith) hB1 hB2
    hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
    hcutoff'Bound hcutoff''Bound houterBound houter'Bound
  convert h using 1 <;> ring

/-- The amplitude integrals and all four artificial endpoint terms are
inserted into the boundary-aware two-IBP identity on an arbitrary compact
off-resonance cell. -/
theorem norm_sourceLowerCollarIntegral_le_offResonanceCellBudget
    {X x beta t a b d P U B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hab : a ≤ b) (hX : 0 < X) (hxLower : X / 2 ≤ x)
    (hd : 0 < d) (hP : 0 ≤ P) (hU : 0 < U)
    (hexpb : Real.exp b ≤ U)
    (hpLower : ∀ w ∈ Set.Icc a b,
      d ≤ |beta * X * Real.exp w + t / (2 * Real.pi)|)
    (hpUpper : ∀ w ∈ Set.Icc a b, |beta * X * Real.exp w| ≤ P)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z)
    (houterSecond : ∀ z, HasDerivAt outer' (outer'' z) z)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bo1)
    (houter''Bound : ∀ z, |outer'' z| ≤ Bo2)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'') :
    let C0 := 4 * B1 * U
    let C1 := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
    let C2 := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
      2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
    ‖∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w‖ ≤
      (C0 * Real.exp (a / 2) + C0 * Real.exp (b / 2)) * (1 / d) +
      (((C1 * Real.exp (a / 2) + C1 * Real.exp (b / 2)) * (1 / d) +
        (C0 * Real.exp (a / 2) + C0 * Real.exp (b / 2)) *
          (P / d ^ 2)) * (1 / d)) +
      ((1 / d) ^ 2 * (2 * C2 * Real.exp (b / 2)) +
        3 * (1 / d) * (P / d ^ 2) *
          (2 * C1 * Real.exp (b / 2)) +
        ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) * (2 * C0 * Real.exp (b / 2))) := by
  dsimp
  let amp := sourceLowerCollarAmplitudeDifference
    X (X / 2) x cutoff outer
  let amp' := sourceLowerCollarAmplitudeDifferenceDeriv
    X (X / 2) x cutoff cutoff' outer outer'
  let amp'' := sourceLowerCollarAmplitudeDifferenceSecond
    X (X / 2) x cutoff cutoff' cutoff'' outer outer' outer''
  let C0 : ℝ := 4 * B1 * U
  let C1 : ℝ := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
  let C2 : ℝ := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
    2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
  have hBo1 : 0 ≤ Bo1 := (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBo2 : 0 ≤ Bo2 := (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hexpa : Real.exp a ≤ U :=
    (Real.exp_le_exp.mpr hab).trans hexpb
  have hampDeriv : ∀ w ∈ Set.Icc a b, HasDerivAt amp (amp' w) w := by
    intro w hw
    exact hasDerivAt_sourceLowerCollarAmplitudeDifference
      hcutoffDeriv houterDeriv
  have hampSecond : ∀ w ∈ Set.Icc a b, HasDerivAt amp' (amp'' w) w := by
    intro w hw
    exact hasDerivAt_sourceLowerCollarAmplitudeDifferenceDeriv
      hcutoffDeriv hcutoffSecond houterDeriv houterSecond
  have hampSecondCont : ContinuousOn amp'' (Set.Icc a b) := by
    apply Continuous.continuousOn
    unfold amp'' sourceLowerCollarAmplitudeDifferenceSecond sourcePacketAmplitudeSecond
    have hcutoffCont : Continuous cutoff :=
      continuous_iff_continuousAt.mpr
        (fun z ↦ (hcutoffDeriv z).continuousAt)
    have hcutoff'Cont : Continuous cutoff' :=
      continuous_iff_continuousAt.mpr
        (fun z ↦ (hcutoffSecond z).continuousAt)
    have houterCont : Continuous outer :=
      continuous_iff_continuousAt.mpr
        (fun z ↦ (houterDeriv z).continuousAt)
    have houter'Cont : Continuous outer' :=
      continuous_iff_continuousAt.mpr
        (fun z ↦ (houterSecond z).continuousAt)
    fun_prop
  have hbudgets := sourceLowerCollarAmplitudeDifference_budgets_on_tailInterval
    hab hX hxLower hU hexpb hB1 hB2 hcutoffSupport hcutoff'Support
    hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
    houterDeriv houterSecond houterBound houter'Bound houter''Bound
    hcutoff''Cont houter''Cont
  have hLa := norm_sourceLowerCollarAmplitudeDifference_le_exp_half_budget
    hX hxLower hU hexpa hB1 hcutoffSupport hcutoffDeriv
    hcutoff'Bound houterBound
  have hRb := norm_sourceLowerCollarAmplitudeDifference_le_exp_half_budget
    hX hxLower hU hexpb hB1 hcutoffSupport hcutoffDeriv
    hcutoff'Bound houterBound
  have hL1 := norm_sourceLowerCollarAmplitudeDifferenceDeriv_le_exp_half_budget
    hX hxLower hU hexpa hB1 hB2 hcutoffSupport hcutoff'Support
    hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
    houterBound houter'Bound
  have hR1 := norm_sourceLowerCollarAmplitudeDifferenceDeriv_le_exp_half_budget
    hX hxLower hU hexpb hB1 hB2 hcutoffSupport hcutoff'Support
    hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
    houterBound houter'Bound
  have hmain := norm_stationaryPhaseIntegral_le_two_ibp_endpoint_budgets
    hab hd hP hpLower hpUpper hampDeriv hampSecond hampSecondCont
    hbudgets.1 hbudgets.2.1 hbudgets.2.2 hLa hRb hL1 hR1
  dsimp [amp, amp', amp'', C0, C1, C2] at hmain ⊢
  convert hmain using 1 <;> ring

end
end MAPMRTSourceLowerCollarOffResonanceCell

#print axioms MAPMRTSourceLowerCollarOffResonanceCell.norm_sourceLowerCollarAmplitudeDifference_le_exp_half_budget
#print axioms MAPMRTSourceLowerCollarOffResonanceCell.norm_sourceLowerCollarAmplitudeDifferenceDeriv_le_exp_half_budget
#print axioms MAPMRTSourceLowerCollarOffResonanceCell.norm_sourceLowerCollarIntegral_le_offResonanceCellBudget
