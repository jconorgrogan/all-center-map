import MRTSourceLowerCollarUpperEnergyWeld

/-!
# Lower off-resonance energy on the literal MRT lower collar

The lower phase cell has the moving logarithmic endpoint
`log ((x-X/2)/X)`.  This module keeps that endpoint literal, proves the
resulting packet measurable, and replaces its endpoint-aware two-IBP budget
by its value at the right endpoint `log (q/2)`.  The packet is then integrated
only on its exact spatial support and transported back to the full fixed
outer collar.
-/

namespace MAPMRTSourceLowerCollarLowerEnergyWeld

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof
open MAPMRTSourceOuterCutoffEndpoint MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarResonance
open MAPMRTSourceLowerCollarOffResonanceCells

noncomputable section

/-- The moving-endpoint lower off-resonance part of the collar correction. -/
def sourceLowerCollarLowerPacket
    (X beta t q : ℝ) (cutoff outer : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ w : ℝ in Real.log ((x - X / 2) / X)..Real.log (q / 2),
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w

/-- The moving logarithmic endpoint is harmless measurably, including its
conventionally defined value at `x=X/2`. -/
theorem measurable_sourceLowerCollarLowerPacket
    {X beta t q : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outer) :
    Measurable (sourceLowerCollarLowerPacket X beta t q cutoff outer) := by
  let f : ℝ → ℝ → ℂ := fun x w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w
  have hf : Continuous f.uncurry := by
    unfold f sourceLowerCollarAmplitudeDifference sourcePacketAmplitude
    have hadd : Continuous additivePhase :=
      continuous_iff_continuousAt.mpr (fun z ↦
        (hasDerivAt_additivePhase z).continuousAt)
    have hphase : Continuous (stationaryPacketPhase X beta t) :=
      continuous_iff_continuousAt.mpr (fun w ↦
        (hasDerivAt_stationaryPacketPhase X beta t w).continuousAt)
    exact (hadd.comp (hphase.comp continuous_snd)).mul (by fun_prop)
  let b : ℝ := Real.log (q / 2)
  let F : ℝ × ℝ → ℂ := fun p ↦ ∫ w : ℝ in b..p.2, f p.1 w
  have hF : Continuous F := by
    exact intervalIntegral.continuous_parametric_primitive_of_continuous hf
  have ha : Measurable (fun x : ℝ ↦ Real.log ((x - X / 2) / X)) := by
    fun_prop
  have hpair : Measurable
      (fun x : ℝ ↦ (x, Real.log ((x - X / 2) / X))) :=
    Measurable.prod measurable_id ha
  have hcomp : Measurable
      (fun x : ℝ ↦ F (x, Real.log ((x - X / 2) / X))) :=
    hF.measurable.comp hpair
  change Measurable (fun x : ℝ ↦
    ∫ w : ℝ in Real.log ((x - X / 2) / X)..b, f x w)
  have heq : (fun x : ℝ ↦
      ∫ w : ℝ in Real.log ((x - X / 2) / X)..b, f x w) =
      fun x : ℝ ↦ -F (x, Real.log ((x - X / 2) / X)) := by
    funext x
    exact intervalIntegral.integral_symm b (Real.log ((x - X / 2) / X))
  rw [heq]
  exact hcomp.neg

/-- Beyond the natural spatial width `X*(q/2)`, every point of the oriented
lower cell sees the inner cutoff outside `[-1,1]`. -/
theorem sourceLowerCollarLowerPacket_eq_zero_of_upper
    {X beta t q x : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q)
    (hx : X / 2 + X * (q / 2) ≤ x)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0) :
    sourceLowerCollarLowerPacket X beta t q cutoff outer x = 0 := by
  unfold sourceLowerCollarLowerPacket
  let a : ℝ := Real.log ((x - X / 2) / X)
  let b : ℝ := Real.log (q / 2)
  have hratio : 0 < (x - X / 2) / X := by
    have : 0 < x - X / 2 := by nlinarith
    positivity
  have hba : b ≤ a := by
    unfold a b
    apply Real.log_le_log (by positivity)
    apply (le_div_iff₀ hX).2
    nlinarith
  change (∫ w : ℝ in a..b,
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference
        X (X / 2) x cutoff outer w) = 0
  calc
    (∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w) =
        ∫ _w : ℝ in a..b, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hw' : w ∈ Set.Icc b a := by
        simpa [Set.uIcc_of_ge hba] using hw
      have hexp : Real.exp w ≤ (x - X / 2) / X := by
        rw [← Real.exp_log hratio]
        exact Real.exp_le_exp.mpr hw'.2
      have hnum : X * Real.exp w - x ≤ -(X / 2) := by
        have hmul := (le_div_iff₀ hX).mp hexp
        linarith
      have hquot : (X * Real.exp w - x) / (X / 2) ≤ -1 := by
        rw [div_le_iff₀ (by positivity : 0 < X / 2)]
        linarith
      have hcut : cutoff ((X * Real.exp w - x) / (X / 2)) = 0 := by
        apply hcutoffSupport
        rw [abs_of_nonpos (hquot.trans (by norm_num))]
        linarith
      simp [sourceLowerCollarAmplitudeDifference, sourcePacketAmplitude, hcut]
    _ = 0 := by simp

/-- Only the two left-endpoint exponential terms vary in the lower-cell IBP
budget.  They are maximized by moving that endpoint to the right endpoint. -/
theorem offResonanceCellBudget_le_rightEndpoint
    {a b d P C0 C1 C2 : ℝ}
    (hab : a ≤ b) (hd : 0 < d) (hP : 0 ≤ P)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    offResonanceCellBudget a b d P C0 C1 C2 ≤
      offResonanceCellBudget b b d P C0 C1 C2 := by
  have he : Real.exp (a / 2) ≤ Real.exp (b / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  unfold offResonanceCellBudget
  gcongr

/-- Uniform lower-cell pointwise estimate on its strict natural spatial
window.  The constant retains every endpoint and derivative contribution
from the two integrations by parts. -/
theorem norm_sourceLowerCollarLowerPacket_le_uniform
    {X x beta t q B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hxStrict : X / 2 < x)
    (hbeta : beta ≠ 0) (hqPos : 0 < q)
    (hqEq : q = lowerCollarResonanceRatio X beta t)
    (hxCell : x - X / 2 ≤ X * (q / 2))
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
    let b := Real.log (q / 2)
    let U := q / 2
    let d := |beta| * X * (q / 2)
    let P := |beta| * X * (q / 2)
    let C0 := 4 * B1 * U
    let C1 := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
    let C2 := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
      2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
    ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ≤
      offResonanceCellBudget b b d P C0 C1 C2 := by
  dsimp
  let a : ℝ := Real.log ((x - X / 2) / X)
  let b : ℝ := Real.log (q / 2)
  let U : ℝ := q / 2
  let d : ℝ := |beta| * X * (q / 2)
  let P : ℝ := |beta| * X * (q / 2)
  let C0 : ℝ := 4 * B1 * U
  let C1 : ℝ := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
  let C2 : ℝ := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
    2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
  have hratio : 0 < (x - X / 2) / X := by positivity
  have hratioU : (x - X / 2) / X ≤ U := by
    unfold U
    rw [div_le_iff₀ hX]
    simpa [mul_comm] using hxCell
  have hab : a ≤ b := by
    unfold a b U at *
    exact Real.log_le_log hratio hratioU
  have hd : 0 < d := by
    unfold d
    have : 0 < |beta| := abs_pos.mpr hbeta
    positivity
  have hP : 0 ≤ P := by unfold P; positivity
  have hBo1 : 0 ≤ Bo1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBo2 : 0 ≤ Bo2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hC0 : 0 ≤ C0 := by unfold C0 U; positivity
  have hC1 : 0 ≤ C1 := by unfold C1 U; positivity
  have hmain := norm_sourceLowerCollarIntegral_le_lowerCellBudget
    hX hxStrict hbeta hqPos hqEq hxCell hB1 hB2
    hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
    hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
    houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
  have hbudget :
      offResonanceCellBudget a b d P C0 C1 C2 ≤
        offResonanceCellBudget b b d P C0 C1 C2 :=
    offResonanceCellBudget_le_rightEndpoint
      (C2 := C2) hab hd hP hC0 hC1
  have hnorm :
      ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ≤
        offResonanceCellBudget a b d P C0 C1 C2 := by
    simpa [sourceLowerCollarLowerPacket, a, b, U, d, P, C0, C1, C2]
      using hmain
  exact hnorm.trans hbudget

/-- The lower-cell energy on the fixed outer collar is exactly its energy on
the moving cell's natural spatial support. -/
theorem integral_norm_sq_lowerPacket_lowerOuterCollar_eq_endpointWindow
    {X beta t q : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q)
    (hqTail : 2 * q ≤ Real.exp (-10))
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0) :
    (∫ x : ℝ in lowerOuterCollar X,
        ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2) =
      ∫ x : ℝ in Set.Ico (X / 2) (X / 2 + X * (q / 2)),
        ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2 := by
  let small : Set ℝ := Set.Ico (X / 2) (X / 2 + X * (q / 2))
  change (∫ x : ℝ in lowerOuterCollar X,
      ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2) =
    ∫ x : ℝ in small,
      ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2
  have hsmallMeas : MeasurableSet small := measurableSet_Ico
  have hcollarMeas : MeasurableSet (lowerOuterCollar X) := measurableSet_Ico
  have hqWidth : q / 2 ≤ Real.exp (-10) := by
    have hexp : 0 < Real.exp (-10) := Real.exp_pos _
    nlinarith
  have hsubset : small ⊆ lowerOuterCollar X := by
    intro x hx
    constructor
    · exact hx.1
    · have hmul := mul_le_mul_of_nonneg_left hqWidth hX.le
      exact hx.2.trans_le (by nlinarith)
  rw [← MeasureTheory.integral_indicator hcollarMeas,
    ← MeasureTheory.integral_indicator hsmallMeas]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxs : x ∈ small
  · have hxc : x ∈ lowerOuterCollar X := hsubset hxs
    simp [hxs, hxc]
  · by_cases hxc : x ∈ lowerOuterCollar X
    · have hxUpper : X / 2 + X * (q / 2) ≤ x := by
        by_contra h
        exact hxs ⟨hxc.1, lt_of_not_ge h⟩
      have hz := sourceLowerCollarLowerPacket_eq_zero_of_upper
        (beta := beta) (t := t) (outer := outer)
        hX hqPos hxUpper hcutoffSupport
      simp [hxs, hxc, hz]
    · simp [hxs, hxc]

/-- The lower-cell two-IBP budget integrated over its exact spatial support,
then transported to the full literal collar.  Its multiplier is the natural
width `X*(q/2)`, rather than the coarser outer-collar width. -/
theorem integral_norm_sq_sourceLowerCollarLowerPacket_le
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
    let b := Real.log (q / 2)
    let U := q / 2
    let d := |beta| * X * (q / 2)
    let P := |beta| * X * (q / 2)
    let C0 := 4 * B1 * U
    let C1 := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
    let C2 := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
      2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
    let K := offResonanceCellBudget b b d P C0 C1 C2
    (∫ x : ℝ in lowerOuterCollar X,
      ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2) ≤
        X * (q / 2) * K ^ 2 := by
  dsimp
  let b : ℝ := Real.log (q / 2)
  let U : ℝ := q / 2
  let d : ℝ := |beta| * X * (q / 2)
  let P : ℝ := |beta| * X * (q / 2)
  let C0 : ℝ := 4 * B1 * U
  let C1 : ℝ := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
  let C2 : ℝ := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
    2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
  let K : ℝ := offResonanceCellBudget b b d P C0 C1 C2
  let small : Set ℝ := Set.Ico (X / 2) (X / 2 + X * (q / 2))
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have hpacketMeas : Measurable
      (sourceLowerCollarLowerPacket X beta t q cutoff outer) :=
    measurable_sourceLowerCollarLowerPacket hcutoffCont houterCont
  have hBo1 : 0 ≤ Bo1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBo2 : 0 ≤ Bo2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hKnonneg : 0 ≤ K := by
    unfold K offResonanceCellBudget C0 C1 C2 d P U b
    positivity
  have hsmallMeas : MeasurableSet small := measurableSet_Ico
  have henergyMeas : AEStronglyMeasurable
      (fun x : ℝ ↦
        ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2)
      (volume.restrict small) :=
    (hpacketMeas.norm.pow measurable_const).aestronglyMeasurable
  have hconstInt : Integrable (fun _x : ℝ ↦ K ^ 2)
      (volume.restrict small) := by
    exact MeasureTheory.integrableOn_const (by
      unfold small
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top)
  have hne : ∀ᵐ x : ℝ ∂volume.restrict small, x ≠ X / 2 := by
    rw [ae_restrict_iff' hsmallMeas]
    have hneGlobal : ∀ᵐ x : ℝ, x ≠ X / 2 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hneGlobal] with x hx _
    exact hx
  have hpoint : ∀ᵐ x : ℝ ∂volume.restrict small,
      ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2 ≤
        K ^ 2 := by
    filter_upwards [self_mem_ae_restrict hsmallMeas, hne] with x hx hxne
    have hxStrict : X / 2 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
    have hxCell : x - X / 2 ≤ X * (q / 2) := by linarith [hx.2]
    have hnorm := norm_sourceLowerCollarLowerPacket_le_uniform
      hX hxStrict hbeta hqPos hqEq hxCell hB1 hB2
      hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
      hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
      houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
    have hnorm' :
        ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ≤ K := by
      simpa [K, b, U, d, P, C0, C1, C2] using hnorm
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
  have henergyInt : Integrable
      (fun x : ℝ ↦
        ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2)
      (volume.restrict small) := by
    apply Integrable.mono' hconstInt henergyMeas
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  rw [integral_norm_sq_lowerPacket_lowerOuterCollar_eq_endpointWindow
    hX hqPos hqTail hcutoffSupport]
  change (∫ x : ℝ in small,
      ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2) ≤ _
  calc
    (∫ x : ℝ in small,
        ‖sourceLowerCollarLowerPacket X beta t q cutoff outer x‖ ^ 2) ≤
        ∫ _x : ℝ in small, K ^ 2 := by
      exact MeasureTheory.integral_mono_ae henergyInt hconstInt hpoint
    _ = X * (q / 2) * K ^ 2 := by
      rw [MeasureTheory.setIntegral_const]
      simp only [Measure.real, small, Real.volume_Ico]
      have hmul : 0 ≤ X * (q / 2) := by positivity
      have hwidth : 0 ≤ X / 2 + X * (q / 2) - X / 2 := by linarith
      rw [ENNReal.toReal_ofReal hwidth]
      ring

end
end MAPMRTSourceLowerCollarLowerEnergyWeld

#print axioms MAPMRTSourceLowerCollarLowerEnergyWeld.measurable_sourceLowerCollarLowerPacket
#print axioms MAPMRTSourceLowerCollarLowerEnergyWeld.sourceLowerCollarLowerPacket_eq_zero_of_upper
#print axioms MAPMRTSourceLowerCollarLowerEnergyWeld.offResonanceCellBudget_le_rightEndpoint
#print axioms MAPMRTSourceLowerCollarLowerEnergyWeld.norm_sourceLowerCollarLowerPacket_le_uniform
#print axioms MAPMRTSourceLowerCollarLowerEnergyWeld.integral_norm_sq_lowerPacket_lowerOuterCollar_eq_endpointWindow
#print axioms MAPMRTSourceLowerCollarLowerEnergyWeld.integral_norm_sq_sourceLowerCollarLowerPacket_le
