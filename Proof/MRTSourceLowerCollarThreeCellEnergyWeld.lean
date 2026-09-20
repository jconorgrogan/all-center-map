import MRTSourceLowerCollarLowerEnergyWeld

/-!
# Three-cell closure of the literal MRT lower-collar energy

This module welds the lower off-resonance, resonant, and upper off-resonance
packets back into the exact finite collar integral.  The split is an identity
of oriented interval integrals, so it does not assume that the moving spatial
endpoint lies to the left of the resonance cells.
-/

namespace MAPMRTSourceLowerCollarThreeCellEnergyWeld

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof
open MAPMRTSourceOuterCutoffEndpoint MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarResonance
open MAPMRTSourceLowerCollarPacketIdentity
open MAPMRTSourceLowerCollarResonantEnergyWeld
open MAPMRTSourceLowerCollarUpperEnergyWeld
open MAPMRTSourceLowerCollarLowerEnergyWeld
open MAPMRTSourceLowerCollarOffResonanceCells

noncomputable section

/-- The exact three-cell partition of the finite lower-collar correction.
All intervals retain their literal endpoints and orientation. -/
theorem lowerCollarIntegral_eq_threeCells
    {X x beta t q : ℝ} {cutoff outer : ℝ → ℝ}
    (hqEq : q = lowerCollarResonanceRatio X beta t)
    (hcutoff : Continuous cutoff) (houter : Continuous outer) :
    (∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w) =
      sourceLowerCollarLowerPacket X beta t q cutoff outer x +
        sourceLowerCollarResonantPacket X beta t cutoff outer x +
        sourceLowerCollarUpperPacket X beta t q cutoff outer x := by
  let f : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w
  have hf : Continuous f := by
    unfold f sourceLowerCollarAmplitudeDifference sourcePacketAmplitude
    have hadd : Continuous additivePhase :=
      continuous_iff_continuousAt.mpr (fun z ↦
        (hasDerivAt_additivePhase z).continuousAt)
    have hphase : Continuous (stationaryPacketPhase X beta t) :=
      continuous_iff_continuousAt.mpr (fun w ↦
        (hasDerivAt_stationaryPacketPhase X beta t w).continuousAt)
    exact (hadd.comp hphase).mul (by fun_prop)
  let a0 : ℝ := Real.log ((x - X / 2) / X)
  let a1 : ℝ := Real.log (q / 2)
  let a2 : ℝ := Real.log (2 * q)
  let a3 : ℝ := -10
  have h01 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hf.intervalIntegrable a0 a1) (hf.intervalIntegrable a1 a2)
  have h02 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hf.intervalIntegrable a0 a2) (hf.intervalIntegrable a2 a3)
  unfold sourceLowerCollarLowerPacket sourceLowerCollarResonantPacket
    sourceLowerCollarUpperPacket
  rw [← hqEq]
  change (∫ w : ℝ in a0..a3, f w) =
    (∫ w : ℝ in a0..a1, f w) + (∫ w : ℝ in a1..a2, f w) +
      ∫ w : ℝ in a2..a3, f w
  rw [← h02, ← h01]

/-- Three-term Hilbert-space Cauchy inequality in the exact normalization
used below. -/
theorem norm_sq_add_add_le_three_sum_norm_sq (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hn : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hsq : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := hsq
    _ ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
      nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
        sq_nonneg (‖b‖ - ‖c‖)]

/-- Complete quantitative closure of the finite lower-collar correction in
the tail-resonance regime `2*q ≤ exp(-10)`.  Every displayed constant is the
literal constant from one of the three cell estimates. -/
theorem integral_norm_sq_lowerCollarIntegral_le_threeCellBudget
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
    let blo := Real.log (q / 2)
    let Ulo := q / 2
    let dlo := |beta| * X * (q / 2)
    let Plo := |beta| * X * (q / 2)
    let C0lo := 4 * B1 * Ulo
    let C1lo := 2 * B1 * Ulo + 8 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50
    let C2lo := B1 * Ulo + 24 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50 +
      2 * B2 * Bo1 * Ulo ^ 2 / 25 + B1 * Bo2 * Ulo / 5000
    let Klo := offResonanceCellBudget blo blo dlo Plo C0lo C1lo C2lo
    let ares := Real.log (q / 2)
    let bres := Real.log (2 * q)
    let Kres := 10 *
      (8 * B1 * q * Real.exp (bres / 2) +
        (bres - ares) * (Real.exp (bres / 2) *
          (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bo1 * q / 25))) /
        Real.sqrt (|beta| * X * (q / 2))
    let aup := Real.log (2 * q)
    let bup := -10
    let Uup := Real.exp (-10)
    let dup := |beta| * X * q
    let Pup := |beta| * X * Uup
    let C0up := 4 * B1 * Uup
    let C1up := 2 * B1 * Uup + 8 * B2 * Uup ^ 2 + B1 * Bo1 * Uup / 50
    let C2up := B1 * Uup + 24 * B2 * Uup ^ 2 + B1 * Bo1 * Uup / 50 +
      2 * B2 * Bo1 * Uup ^ 2 / 25 + B1 * Bo2 * Uup / 5000
    let Kup := offResonanceCellBudget aup bup dup Pup C0up C1up C2up
    (∫ x : ℝ in lowerOuterCollar X,
      ‖∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w‖ ^ 2) ≤
      3 * (X * (q / 2) * Klo ^ 2 + 2 * q * X * Kres ^ 2 +
        X * Real.exp (-10) * Kup ^ 2) := by
  dsimp
  let blo : ℝ := Real.log (q / 2)
  let Ulo : ℝ := q / 2
  let dlo : ℝ := |beta| * X * (q / 2)
  let Plo : ℝ := |beta| * X * (q / 2)
  let C0lo : ℝ := 4 * B1 * Ulo
  let C1lo : ℝ := 2 * B1 * Ulo + 8 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50
  let C2lo : ℝ := B1 * Ulo + 24 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50 +
    2 * B2 * Bo1 * Ulo ^ 2 / 25 + B1 * Bo2 * Ulo / 5000
  let Klo : ℝ := offResonanceCellBudget blo blo dlo Plo C0lo C1lo C2lo
  let ares : ℝ := Real.log (q / 2)
  let bres : ℝ := Real.log (2 * q)
  let Kres : ℝ := 10 *
    (8 * B1 * q * Real.exp (bres / 2) +
      (bres - ares) * (Real.exp (bres / 2) *
        (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bo1 * q / 25))) /
      Real.sqrt (|beta| * X * (q / 2))
  let aup : ℝ := Real.log (2 * q)
  let bup : ℝ := -10
  let Uup : ℝ := Real.exp (-10)
  let dup : ℝ := |beta| * X * q
  let Pup : ℝ := |beta| * X * Uup
  let C0up : ℝ := 4 * B1 * Uup
  let C1up : ℝ := 2 * B1 * Uup + 8 * B2 * Uup ^ 2 + B1 * Bo1 * Uup / 50
  let C2up : ℝ := B1 * Uup + 24 * B2 * Uup ^ 2 + B1 * Bo1 * Uup / 50 +
    2 * B2 * Bo1 * Uup ^ 2 / 25 + B1 * Bo2 * Uup / 5000
  let Kup : ℝ := offResonanceCellBudget aup bup dup Pup C0up C1up C2up
  let L : ℝ → ℂ := sourceLowerCollarLowerPacket X beta t q cutoff outer
  let R : ℝ → ℂ := sourceLowerCollarResonantPacket X beta t cutoff outer
  let U : ℝ → ℂ := sourceLowerCollarUpperPacket X beta t q cutoff outer
  let T : ℝ → ℂ := fun x ↦
    ∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
      additivePhase (stationaryPacketPhase X beta t w) *
        sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w
  let collar : Set ℝ := lowerOuterCollar X
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterSecond z).continuousAt)
  have hLmeas : Measurable L :=
    measurable_sourceLowerCollarLowerPacket hcutoffCont houterCont
  have hRcont : Continuous R :=
    continuous_sourceLowerCollarResonantPacket hcutoffCont houterCont
  have hUcont : Continuous U :=
    continuous_sourceLowerCollarUpperPacket hcutoffCont houterCont
  have hcollarMeas : MeasurableSet collar := measurableSet_Ico
  have hcollarCompact : IsCompact
      (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) := isCompact_Icc
  have hRenergyInt : Integrable (fun x ↦ ‖R x‖ ^ 2)
      (volume.restrict collar) := by
    have hIcc : IntegrableOn (fun x ↦ ‖R x‖ ^ 2)
        (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) :=
      (hRcont.norm.pow 2).continuousOn.integrableOn_compact hcollarCompact
    exact hIcc.mono_set Set.Ico_subset_Icc_self
  have hUenergyInt : Integrable (fun x ↦ ‖U x‖ ^ 2)
      (volume.restrict collar) := by
    have hIcc : IntegrableOn (fun x ↦ ‖U x‖ ^ 2)
        (Set.Icc (X / 2) (X / 2 + X * Real.exp (-10))) :=
      (hUcont.norm.pow 2).continuousOn.integrableOn_compact hcollarCompact
    exact hIcc.mono_set Set.Ico_subset_Icc_self
  have hBo1 : 0 ≤ Bo1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBo2 : 0 ≤ Bo2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hKloNonneg : 0 ≤ Klo := by
    unfold Klo offResonanceCellBudget C0lo C1lo C2lo dlo Plo Ulo blo
    positivity
  have hconstL : Integrable (fun _x : ℝ ↦ Klo ^ 2)
      (volume.restrict collar) := by
    exact MeasureTheory.integrableOn_const (by
      unfold collar lowerOuterCollar
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top)
  have hne : ∀ᵐ x : ℝ ∂volume.restrict collar, x ≠ X / 2 := by
    rw [ae_restrict_iff' hcollarMeas]
    have hneGlobal : ∀ᵐ x : ℝ, x ≠ X / 2 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hneGlobal] with x hx _
    exact hx
  have hLpoint : ∀ᵐ x : ℝ ∂volume.restrict collar, ‖L x‖ ^ 2 ≤ Klo ^ 2 := by
    filter_upwards [self_mem_ae_restrict hcollarMeas, hne] with x hx hxne
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
  have hLenergyMeas : AEStronglyMeasurable (fun x ↦ ‖L x‖ ^ 2)
      (volume.restrict collar) :=
    (hLmeas.norm.pow measurable_const).aestronglyMeasurable
  have hLenergyInt : Integrable (fun x ↦ ‖L x‖ ^ 2)
      (volume.restrict collar) := by
    apply Integrable.mono' hconstL hLenergyMeas
    filter_upwards [hLpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hT_eq : T = fun x ↦ L x + R x + U x := by
    funext x
    exact lowerCollarIntegral_eq_threeCells hqEq hcutoffCont houterCont
  have hTmeas : Measurable T := by
    rw [hT_eq]
    exact (hLmeas.add hRcont.measurable).add hUcont.measurable
  have hsumInt : Integrable
      (fun x ↦ ‖L x‖ ^ 2 + ‖R x‖ ^ 2 + ‖U x‖ ^ 2)
      (volume.restrict collar) :=
    hLenergyInt.add hRenergyInt |>.add hUenergyInt
  have hmajorInt : Integrable
      (fun x ↦ 3 * (‖L x‖ ^ 2 + ‖R x‖ ^ 2 + ‖U x‖ ^ 2))
      (volume.restrict collar) := hsumInt.const_mul 3
  have hpoint : ∀ᵐ x : ℝ ∂volume.restrict collar,
      ‖T x‖ ^ 2 ≤ 3 * (‖L x‖ ^ 2 + ‖R x‖ ^ 2 + ‖U x‖ ^ 2) := by
    filter_upwards with x
    rw [hT_eq]
    exact norm_sq_add_add_le_three_sum_norm_sq _ _ _
  have hTenergyInt : Integrable (fun x ↦ ‖T x‖ ^ 2)
      (volume.restrict collar) := by
    apply Integrable.mono' hmajorInt
      ((hTmeas.norm.pow measurable_const).aestronglyMeasurable)
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hLbound : (∫ x : ℝ in lowerOuterCollar X, ‖L x‖ ^ 2) ≤
      X * (q / 2) * Klo ^ 2 := by
    simpa [L, Klo, blo, Ulo, dlo, Plo, C0lo, C1lo, C2lo] using
      integral_norm_sq_sourceLowerCollarLowerPacket_le
        hX hbeta hqPos hqEq hqTail hB1 hB2
        hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
        hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
        houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
  have hRbound : (∫ x : ℝ in lowerOuterCollar X, ‖R x‖ ^ 2) ≤
      2 * q * X * Kres ^ 2 := by
    have hmain :=
      integral_norm_sq_sourceLowerCollarResonantPacket_on_lowerOuterCollar_le
        hX hbeta (hqEq ▸ hqPos) (by simpa [← hqEq] using hqTail)
        hB1 hB2 hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
        hcutoff'Bound hcutoff''Bound houterDeriv houterBound
        houter'Bound houter'Cont
    simpa [R, Kres, ares, bres, ← hqEq] using hmain
  have hUbound : (∫ x : ℝ in lowerOuterCollar X, ‖U x‖ ^ 2) ≤
      X * Real.exp (-10) * Kup ^ 2 := by
    simpa [U, Kup, aup, bup, Uup, dup, Pup, C0up, C1up, C2up] using
      integral_norm_sq_sourceLowerCollarUpperPacket_le
        hX hbeta hqPos hqEq hqTail hB1 hB2
        hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
        hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
        houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
  have hLRintegral :
      (∫ x : ℝ in collar, ‖L x‖ ^ 2 + ‖R x‖ ^ 2) =
        (∫ x : ℝ in collar, ‖L x‖ ^ 2) +
          ∫ x : ℝ in collar, ‖R x‖ ^ 2 := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add hLenergyInt hRenergyInt
  have hLRUintegral :
      (∫ x : ℝ in collar, (‖L x‖ ^ 2 + ‖R x‖ ^ 2) + ‖U x‖ ^ 2) =
        (∫ x : ℝ in collar, ‖L x‖ ^ 2 + ‖R x‖ ^ 2) +
          ∫ x : ℝ in collar, ‖U x‖ ^ 2 := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add (hLenergyInt.add hRenergyInt) hUenergyInt
  change (∫ x : ℝ in collar, ‖T x‖ ^ 2) ≤ _
  calc
    (∫ x : ℝ in collar, ‖T x‖ ^ 2) ≤
        ∫ x : ℝ in collar,
          3 * (‖L x‖ ^ 2 + ‖R x‖ ^ 2 + ‖U x‖ ^ 2) :=
      MeasureTheory.integral_mono_ae hTenergyInt hmajorInt hpoint
    _ = 3 * ((∫ x : ℝ in collar, ‖L x‖ ^ 2) +
        (∫ x : ℝ in collar, ‖R x‖ ^ 2) +
        ∫ x : ℝ in collar, ‖U x‖ ^ 2) := by
      rw [MeasureTheory.integral_const_mul, hLRUintegral, hLRintegral]
    _ ≤ 3 * (X * (q / 2) * Klo ^ 2 + 2 * q * X * Kres ^ 2 +
        X * Real.exp (-10) * Kup ^ 2) := by
      gcongr

/-- Transparent name for the exact quantitative expression proved above. -/
def lowerCollarThreeCellBudget
    (X beta q B1 B2 Bo1 Bo2 : ℝ) : ℝ :=
  let blo := Real.log (q / 2)
  let Ulo := q / 2
  let dlo := |beta| * X * (q / 2)
  let Plo := |beta| * X * (q / 2)
  let C0lo := 4 * B1 * Ulo
  let C1lo := 2 * B1 * Ulo + 8 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50
  let C2lo := B1 * Ulo + 24 * B2 * Ulo ^ 2 + B1 * Bo1 * Ulo / 50 +
    2 * B2 * Bo1 * Ulo ^ 2 / 25 + B1 * Bo2 * Ulo / 5000
  let Klo := offResonanceCellBudget blo blo dlo Plo C0lo C1lo C2lo
  let ares := Real.log (q / 2)
  let bres := Real.log (2 * q)
  let Kres := 10 *
    (8 * B1 * q * Real.exp (bres / 2) +
      (bres - ares) * (Real.exp (bres / 2) *
        (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bo1 * q / 25))) /
      Real.sqrt (|beta| * X * (q / 2))
  let aup := Real.log (2 * q)
  let bup := -10
  let Uup := Real.exp (-10)
  let dup := |beta| * X * q
  let Pup := |beta| * X * Uup
  let C0up := 4 * B1 * Uup
  let C1up := 2 * B1 * Uup + 8 * B2 * Uup ^ 2 + B1 * Bo1 * Uup / 50
  let C2up := B1 * Uup + 24 * B2 * Uup ^ 2 + B1 * Bo1 * Uup / 50 +
    2 * B2 * Bo1 * Uup ^ 2 / 25 + B1 * Bo2 * Uup / 5000
  let Kup := offResonanceCellBudget aup bup dup Pup C0up C1up C2up
  3 * (X * (q / 2) * Klo ^ 2 + 2 * q * X * Kres ^ 2 +
    X * Real.exp (-10) * Kup ^ 2)

/-- Deterministic bridge to the existing endpoint pairing constructor.  The
only retained `MemLp` hypothesis is the constructor's functional-analytic
domain premise; the formerly open collar-energy estimate is discharged by
the literal three-cell proof above. -/
theorem norm_sq_lowerOuterCollarPairingError_le_threeCellBudget
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
    (hDiff : MemLp
      (lowerOuterCollarPacketDifference
        X (X / 2) beta t cutoff outer) 2)
    (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) = 1) :
    ‖lowerOuterCollarPairingError
        X (X / 2) beta t cutoff outer g‖ ^ 2 ≤
      lowerCollarThreeCellBudget X beta q B1 B2 Bo1 Bo2 := by
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have hpair := norm_sq_lowerOuterCollarPairingError_le_finiteIntegralEnergy
    hX hcutoffCont houterCont hcutoffSupport houterOne hg hDiff hgNorm
  have henergy := integral_norm_sq_lowerCollarIntegral_le_threeCellBudget
    hX hbeta hqPos hqEq hqTail hB1 hB2
    hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
    hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
    houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
  exact hpair.trans (by
    simpa [lowerCollarThreeCellBudget] using henergy)

end
end MAPMRTSourceLowerCollarThreeCellEnergyWeld

#print axioms MAPMRTSourceLowerCollarThreeCellEnergyWeld.lowerCollarIntegral_eq_threeCells
#print axioms MAPMRTSourceLowerCollarThreeCellEnergyWeld.norm_sq_add_add_le_three_sum_norm_sq
#print axioms MAPMRTSourceLowerCollarThreeCellEnergyWeld.integral_norm_sq_lowerCollarIntegral_le_threeCellBudget
#print axioms MAPMRTSourceLowerCollarThreeCellEnergyWeld.norm_sq_lowerOuterCollarPairingError_le_threeCellBudget
