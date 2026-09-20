import MRTSourceLowerCollarThreeCellEnergyWeld

/-!
# Automatic L2 domain closure for the literal lower-collar packet difference

The endpoint Cauchy--Schwarz constructor was stated with a `MemLp` premise for
the packet difference.  In the tail-resonance regime that premise follows
from the concrete three-cell regularity and bounds, so it is discharged here.
-/

namespace MAPMRTSourceLowerCollarMemLpWeld

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof
open MAPMRTSourceOuterCutoffEndpoint MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarResonance
open MAPMRTSourceLowerCollarPacketIdentity
open MAPMRTSourceLowerCollarUpperEnergyWeld
open MAPMRTSourceLowerCollarLowerEnergyWeld
open MAPMRTSourceLowerCollarThreeCellEnergyWeld
open MAPMRTSourceLowerCollarOffResonanceCells

noncomputable section

/-- Concrete regularity implies the `L²` domain condition required by the
endpoint pairing constructor. -/
theorem memLp_two_lowerOuterCollarPacketDifference_of_threeCellRegularity
    {X beta t q B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0) (hqPos : 0 < q)
    (hqEq : q = lowerCollarResonanceRatio X beta t)
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
    (houter''Cont : Continuous outer'')
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    MemLp (lowerOuterCollarPacketDifference
      X (X / 2) beta t cutoff outer) 2 := by
  let blo : ℝ := Real.log (q / 2)
  let Ulo : ℝ := q / 2
  let dlo : ℝ := |beta| * X * (q / 2)
  let Plo : ℝ := |beta| * X * (q / 2)
  let C0lo : ℝ := 4 * B1 * Ulo
  let C1lo : ℝ := 2 * B1 * Ulo + 8 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50
  let C2lo : ℝ := B1 * Ulo + 24 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50 +
    2 * B2 * Bo1 * Ulo ^ 2 / 25 + B1 * Bo2 * Ulo / 5000
  let Klo : ℝ := offResonanceCellBudget blo blo dlo Plo C0lo C1lo C2lo
  let L : ℝ → ℂ := sourceLowerCollarLowerPacket X beta t q cutoff outer
  let R : ℝ → ℂ := sourceLowerCollarResonantPacket X beta t cutoff outer
  let U : ℝ → ℂ := sourceLowerCollarUpperPacket X beta t q cutoff outer
  let T : ℝ → ℂ := fun x ↦
    ∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
      additivePhase (stationaryPacketPhase X beta t w) *
        sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w
  let D : ℝ → ℂ :=
    lowerOuterCollarPacketDifference X (X / 2) beta t cutoff outer
  let collar : Set ℝ := lowerOuterCollar X
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have hLmeas : Measurable L :=
    measurable_sourceLowerCollarLowerPacket hcutoffCont houterCont
  have hRcont : Continuous R :=
    continuous_sourceLowerCollarResonantPacket hcutoffCont houterCont
  have hUcont : Continuous U :=
    continuous_sourceLowerCollarUpperPacket hcutoffCont houterCont
  have hcollarMeas : MeasurableSet collar := measurableSet_Ico
  have hcompact : IsCompact
      (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) := isCompact_Icc
  have hRenergyInt : Integrable (fun x ↦ ‖R x‖ ^ 2)
      (volume.restrict collar) := by
    have hIcc : IntegrableOn (fun x ↦ ‖R x‖ ^ 2)
        (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) :=
      (hRcont.norm.pow 2).continuousOn.integrableOn_compact hcompact
    exact hIcc.mono_set Set.Ico_subset_Icc_self
  have hUenergyInt : Integrable (fun x ↦ ‖U x‖ ^ 2)
      (volume.restrict collar) := by
    have hIcc : IntegrableOn (fun x ↦ ‖U x‖ ^ 2)
        (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) :=
      (hUcont.norm.pow 2).continuousOn.integrableOn_compact hcompact
    exact hIcc.mono_set Set.Ico_subset_Icc_self
  have hBo1 : 0 ≤ Bo1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBo2 : 0 ≤ Bo2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hKlo : 0 ≤ Klo := by
    unfold Klo offResonanceCellBudget C0lo C1lo C2lo dlo Plo Ulo blo
    positivity
  have hconst : Integrable (fun _x : ℝ ↦ Klo ^ 2)
      (volume.restrict collar) := by
    exact MeasureTheory.integrableOn_const (by
      unfold collar lowerOuterCollar
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top)
  have hneRestrict : ∀ᵐ x : ℝ ∂volume.restrict collar, x ≠ X / 2 := by
    rw [ae_restrict_iff' hcollarMeas]
    have hne : ∀ᵐ x : ℝ, x ≠ X / 2 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx _
    exact hx
  have hLpoint : ∀ᵐ x : ℝ ∂volume.restrict collar, ‖L x‖ ^ 2 ≤ Klo ^ 2 := by
    filter_upwards [self_mem_ae_restrict hcollarMeas, hneRestrict] with x hx hxne
    have hxStrict : X / 2 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
    by_cases hxCell : x - X / 2 ≤ X * (q / 2)
    · have hnorm := norm_sourceLowerCollarLowerPacket_le_uniform
        hX hxStrict hbeta hqPos hqEq hxCell hB1 hB2
        hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
        hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
        houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
      have hnorm' : ‖L x‖ ≤ Klo := by
        simpa [L, Klo, blo, Ulo, dlo, Plo, C0lo, C1lo, C2lo] using hnorm
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
    · have hxUpper : X / 2 + X * (q / 2) ≤ x := by linarith
      have hz := sourceLowerCollarLowerPacket_eq_zero_of_upper
        (beta := beta) (t := t) (outer := outer)
        hX hqPos hxUpper hcutoffSupport
      simp [L, hz, sq_nonneg Klo]
  have hLenergyInt : Integrable (fun x ↦ ‖L x‖ ^ 2)
      (volume.restrict collar) := by
    apply Integrable.mono' hconst
      ((hLmeas.norm.pow measurable_const).aestronglyMeasurable)
    filter_upwards [hLpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hT_eq : T = fun x ↦ L x + R x + U x := by
    funext x
    exact lowerCollarIntegral_eq_threeCells hqEq hcutoffCont houterCont
  have hTmeas : Measurable T := by
    rw [hT_eq]
    exact (hLmeas.add hRcont.measurable).add hUcont.measurable
  have hmajorInt : Integrable
      (fun x ↦ 3 * (‖L x‖ ^ 2 + ‖R x‖ ^ 2 + ‖U x‖ ^ 2))
      (volume.restrict collar) :=
    (hLenergyInt.add hRenergyInt |>.add hUenergyInt).const_mul 3
  have hTpoint : ∀ᵐ x : ℝ ∂volume.restrict collar,
      ‖T x‖ ^ 2 ≤ 3 * (‖L x‖ ^ 2 + ‖R x‖ ^ 2 + ‖U x‖ ^ 2) := by
    filter_upwards with x
    rw [hT_eq]
    exact norm_sq_add_add_le_three_sum_norm_sq _ _ _
  have hTenergyInt : Integrable (fun x ↦ ‖T x‖ ^ 2)
      (volume.restrict collar) := by
    apply Integrable.mono' hmajorInt
      ((hTmeas.norm.pow measurable_const).aestronglyMeasurable)
    filter_upwards [hTpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hne : ∀ᵐ x : ℝ, x ≠ X / 2 := by
    simp [ae_iff, measure_singleton]
  have hDT : D =ᵐ[volume] collar.indicator T := by
    filter_upwards [hne] with x hxne
    by_cases hx : x ∈ collar
    · have hxStrict : X / 2 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
      have heq := lowerOuterCollarPacketDifference_eq_lowerCollarIntegral
        (beta := beta) (t := t)
        hX hx hxStrict hcutoffCont houterCont hcutoffSupport houterOne
      simpa [D, T, Set.indicator_of_mem hx] using heq
    · have hx' : x ∉ lowerOuterCollar X := by simpa [collar] using hx
      simp [D, lowerOuterCollarPacketDifference, hx, hx']
  have hDmeas : AEStronglyMeasurable D :=
    (hTmeas.indicator hcollarMeas).aestronglyMeasurable.congr hDT.symm
  have hindicatorEnergy : Integrable
      (fun x ↦ ‖collar.indicator T x‖ ^ 2) := by
    have hi : Integrable (collar.indicator fun x ↦ ‖T x‖ ^ 2) :=
      (integrable_indicator_iff hcollarMeas).2 hTenergyInt
    convert hi using 1
    funext x
    by_cases hx : x ∈ collar <;> simp [hx]
  have hDenergy : Integrable (fun x ↦ ‖D x‖ ^ 2) := by
    apply hindicatorEnergy.congr
    filter_upwards [hDT] with x hx
    rw [hx]
  exact (memLp_two_iff_integrable_sq_norm hDmeas).2 hDenergy

/-- Endpoint pairing closure with the packet-difference `MemLp` premise fully
discharged from concrete cutoff and outer-cutoff regularity. -/
theorem norm_sq_lowerOuterCollarPairingError_le_threeCellBudget_of_regularity
    {X beta t q B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    {g : ℝ → ℂ}
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
    (houter''Cont : Continuous outer'')
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hg : MemLp g 2)
    (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) = 1) :
    ‖lowerOuterCollarPairingError
        X (X / 2) beta t cutoff outer g‖ ^ 2 ≤
      lowerCollarThreeCellBudget X beta q B1 B2 Bo1 Bo2 := by
  have hDiff :=
    memLp_two_lowerOuterCollarPacketDifference_of_threeCellRegularity
      hX hbeta hqPos hqEq hB1 hB2
      hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
      hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
      houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
      houterOne
  exact norm_sq_lowerOuterCollarPairingError_le_threeCellBudget
    hX hbeta hqPos hqEq hqTail hB1 hB2
    hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
    hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
    houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
    houterOne hg hDiff hgNorm

end
end MAPMRTSourceLowerCollarMemLpWeld

#print axioms MAPMRTSourceLowerCollarMemLpWeld.memLp_two_lowerOuterCollarPacketDifference_of_threeCellRegularity
#print axioms MAPMRTSourceLowerCollarMemLpWeld.norm_sq_lowerOuterCollarPairingError_le_threeCellBudget_of_regularity
