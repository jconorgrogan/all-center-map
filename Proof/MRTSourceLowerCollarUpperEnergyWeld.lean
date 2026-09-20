import MRTSourceLowerCollarResonantEnergyWeld
import MRTSourceLowerCollarOffResonanceCells

/-!
# Upper off-resonance energy on the literal MRT lower collar

The upper phase cell has fixed logarithmic endpoints
`[log (2*q), -10]`.  Its two-integration-by-parts budget is therefore uniform
in the spatial collar variable.  This module integrates that exact pointwise
budget over the literal collar of width `X*exp(-10)`.
-/

namespace MAPMRTSourceLowerCollarUpperEnergyWeld

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof
open MAPMRTSourceOuterCutoffEndpoint MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarResonance
open MAPMRTSourceLowerCollarOffResonanceCells

noncomputable section

/-- The fixed upper off-resonance part of the lower-collar correction. -/
def sourceLowerCollarUpperPacket
    (X beta t q : ℝ) (cutoff outer : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ w : ℝ in Real.log (2 * q)..(-10),
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w

theorem continuous_sourceLowerCollarUpperPacket
    {X beta t q : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outer) :
    Continuous (sourceLowerCollarUpperPacket X beta t q cutoff outer) := by
  unfold sourceLowerCollarUpperPacket
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold sourceLowerCollarAmplitudeDifference sourcePacketAmplitude
  have hadd : Continuous additivePhase :=
    continuous_iff_continuousAt.mpr (fun z ↦
      (hasDerivAt_additivePhase z).continuousAt)
  have hphase : Continuous (stationaryPacketPhase X beta t) :=
    continuous_iff_continuousAt.mpr (fun w ↦
      (hasDerivAt_stationaryPacketPhase X beta t w).continuousAt)
  exact (hadd.comp (hphase.comp continuous_snd)).mul (by fun_prop)

/-- The upper-cell two-IBP budget integrated over the exact fixed outer
collar.  The multiplier is its literal width `X*exp(-10)`. -/
theorem integral_norm_sq_sourceLowerCollarUpperPacket_le
    {X beta t q B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0) (hqPos : 0 < q)
    (hqEq : q = lowerCollarResonanceRatio X beta t)
    (hqTail : 2 * q ≤ Real.exp (-10))
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
    let a := Real.log (2 * q)
    let b := -10
    let U := Real.exp (-10)
    let d := |beta| * X * q
    let P := |beta| * X * U
    let C0 := 4 * B1 * U
    let C1 := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
    let C2 := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
      2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
    let K := offResonanceCellBudget a b d P C0 C1 C2
    (∫ x : ℝ in lowerOuterCollar X,
      ‖sourceLowerCollarUpperPacket X beta t q cutoff outer x‖ ^ 2) ≤
        X * Real.exp (-10) * K ^ 2 := by
  dsimp
  let a : ℝ := Real.log (2 * q)
  let b : ℝ := -10
  let U : ℝ := Real.exp (-10)
  let d : ℝ := |beta| * X * q
  let P : ℝ := |beta| * X * U
  let C0 : ℝ := 4 * B1 * U
  let C1 : ℝ := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
  let C2 : ℝ := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
    2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
  let K : ℝ := offResonanceCellBudget a b d P C0 C1 C2
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have hpacketCont : Continuous
      (sourceLowerCollarUpperPacket X beta t q cutoff outer) :=
    continuous_sourceLowerCollarUpperPacket hcutoffCont houterCont
  have henergyInt : IntegrableOn
      (fun x : ℝ ↦
        ‖sourceLowerCollarUpperPacket X beta t q cutoff outer x‖ ^ 2)
      (lowerOuterCollar X) := by
    have hIcc : IntegrableOn
        (fun x : ℝ ↦
          ‖sourceLowerCollarUpperPacket X beta t q cutoff outer x‖ ^ 2)
        (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) :=
      (hpacketCont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hIcc.mono_set Set.Ico_subset_Icc_self
  have hKnonneg : 0 ≤ K := by
    unfold K offResonanceCellBudget C0 C1 C2 d P U a b
    have hBo1 : 0 ≤ Bo1 :=
      (abs_nonneg (outer' 0)).trans (houter'Bound 0)
    have hBo2 : 0 ≤ Bo2 :=
      (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
    positivity
  have hpoint : ∀ x ∈ lowerOuterCollar X,
      ‖sourceLowerCollarUpperPacket X beta t q cutoff outer x‖ ^ 2 ≤ K ^ 2 := by
    intro x hx
    have hmain := norm_sourceLowerCollarIntegral_le_upperCellBudget
      hX hx.1 hbeta hqPos hqEq hqTail hB1 hB2
      hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
      hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
      houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
    have hnorm :
        ‖sourceLowerCollarUpperPacket X beta t q cutoff outer x‖ ≤ K := by
      simpa [sourceLowerCollarUpperPacket, K, a, b, U, d, P, C0, C1, C2]
        using hmain
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    (∫ x : ℝ in lowerOuterCollar X,
        ‖sourceLowerCollarUpperPacket X beta t q cutoff outer x‖ ^ 2) ≤
        ∫ _x : ℝ in lowerOuterCollar X, K ^ 2 := by
      apply MeasureTheory.integral_mono_ae henergyInt
        (MeasureTheory.integrableOn_const (by
          unfold lowerOuterCollar
          rw [Real.volume_Ico]
          exact ENNReal.ofReal_ne_top))
      filter_upwards [self_mem_ae_restrict (show MeasurableSet
          (lowerOuterCollar X) by exact measurableSet_Ico)] with x hx
      exact hpoint x hx
    _ = X * Real.exp (-10) * K ^ 2 := by
      rw [MeasureTheory.setIntegral_const]
      simp only [Measure.real, lowerOuterCollar, Real.volume_Ico]
      have hwidth : 0 ≤ X / 2 + X * Real.exp (-10) - X / 2 := by
        nlinarith [mul_pos hX (Real.exp_pos (-10))]
      rw [ENNReal.toReal_ofReal hwidth]
      ring

end
end MAPMRTSourceLowerCollarUpperEnergyWeld

#print axioms MAPMRTSourceLowerCollarUpperEnergyWeld.continuous_sourceLowerCollarUpperPacket
#print axioms MAPMRTSourceLowerCollarUpperEnergyWeld.integral_norm_sq_sourceLowerCollarUpperPacket_le
