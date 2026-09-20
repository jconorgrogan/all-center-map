import MRTSourceOuterCutoffEndpoint

/-!
# The stationary resonance inside the endpoint lower collar

The collar packet difference cannot be treated uniformly by the
first-derivative or two-integration-by-parts branches.  This module identifies
the exact resonance and exhibits it at the lower endpoint of the source
frequency interval while retaining `H = X/2`, `1 < |β|H`, and `η < 1/100`.
-/

namespace MAPMRTSourceLowerCollarResonance

open Set
open MAPMRTProposition51HardBranch
open MAPMRTSourceOuterCutoffEndpoint

noncomputable section

/-- The dimensionless `u/X` coordinate of a stationary point of the equation
(80) phase. -/
def lowerCollarResonanceRatio (X beta t : ℝ) : ℝ :=
  -t / (2 * Real.pi * beta * X)

/-- The logarithmic coordinate of that stationary point. -/
def lowerCollarResonanceLog (X beta t : ℝ) : ℝ :=
  Real.log (lowerCollarResonanceRatio X beta t)

/-- Exact resonance criterion: when the positive stationary ratio is below
`exp(-10)`, the phase derivative vanishes strictly inside the omitted lower
outer tail. -/
theorem hasDerivAt_stationaryPacketPhase_zero_at_lowerCollarResonance
    {X beta t : ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hqTail : lowerCollarResonanceRatio X beta t < Real.exp (-10)) :
    HasDerivAt (stationaryPacketPhase X beta t) 0
        (lowerCollarResonanceLog X beta t) ∧
      lowerCollarResonanceLog X beta t < -10 := by
  have hexp : Real.exp (lowerCollarResonanceLog X beta t) =
      lowerCollarResonanceRatio X beta t := by
    exact Real.exp_log hqPos
  have hzero : beta * X *
      Real.exp (lowerCollarResonanceLog X beta t) +
        t / (2 * Real.pi) = 0 := by
    rw [hexp]
    unfold lowerCollarResonanceRatio
    field_simp [hbeta, ne_of_gt hX, ne_of_gt Real.pi_pos]
    ring
  constructor
  · simpa [hzero] using hasDerivAt_stationaryPacketPhase
      X beta t (lowerCollarResonanceLog X beta t)
  · exact (Real.log_lt_iff_lt_exp hqPos).mpr hqTail

/-- At the literal endpoint `x=H=X/2`, a positive lower-tail resonance lies
inside the open inner-cutoff window.  Thus support geometry does not remove the
stationary point. -/
theorem lowerCollarResonance_innerCoordinate_mem_Ioo_at_endpoint
    {X beta t : ℝ}
    (hX : 0 < X)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hqTail : lowerCollarResonanceRatio X beta t < Real.exp (-10)) :
    (X * Real.exp (lowerCollarResonanceLog X beta t) - X / 2) / (X / 2) ∈
      Set.Ioo (-1 : ℝ) 1 := by
  have hexp : Real.exp (lowerCollarResonanceLog X beta t) =
      lowerCollarResonanceRatio X beta t := Real.exp_log hqPos
  have heOne : Real.exp (-10 : ℝ) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  rw [hexp]
  constructor
  · rw [lt_div_iff₀ (by positivity : 0 < X / 2)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity : 0 < X / 2)]
    have hqOne := hqTail.trans heOne
    nlinarith

/-- The resonance occurs on an allowed hard-regime packet.  Taking the lower
frequency endpoint `t=-ηβX`, it lies below `w=-10` whenever
`η < 2π exp(-10)`, a range permitted by the literal hypothesis `η<1/100`.
The returned frequency inequalities are exactly equation (69). -/
theorem hard_regime_lower_frequency_endpoint_has_lowerCollarResonance
    {X H beta eta : ℝ}
    (hX : 0 < X) (hEndpoint : H = X / 2)
    (hbeta : 0 < beta) (hhard : 1 < |beta| * H)
    (hetaPos : 0 < eta) (hetaHard : eta < 1 / 100)
    (hetaResonant : eta < 2 * Real.pi * Real.exp (-10)) :
    let t := -eta * beta * X
    let w := Real.log (eta / (2 * Real.pi))
    H = X / 2 ∧
      1 < |beta| * H ∧
      HasDerivAt (stationaryPacketPhase X beta t) 0 w ∧
      w < -10 ∧
      eta * |beta| * X ≤ |t| ∧
      |t| ≤ |beta| * X / eta ∧
      (X * Real.exp w - X / 2) / (X / 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  dsimp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hetaPi : 0 < eta / (2 * Real.pi) := by positivity
  have hetaTail : eta / (2 * Real.pi) < Real.exp (-10) := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hetaResonant
  have hexp : Real.exp (Real.log (eta / (2 * Real.pi))) =
      eta / (2 * Real.pi) := Real.exp_log hetaPi
  have hzero : beta * X * Real.exp (Real.log (eta / (2 * Real.pi))) +
      (-eta * beta * X) / (2 * Real.pi) = 0 := by
    rw [hexp]
    field_simp [ne_of_gt hpi]
    ring
  have htAbs : |-eta * beta * X| = eta * |beta| * X := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hetaPos, abs_of_pos hX]
  have hetaOne : eta ≤ 1 := by linarith
  have hetaSq : eta ^ 2 ≤ 1 := by nlinarith
  refine ⟨hEndpoint, hhard, ?_,
    (Real.log_lt_iff_lt_exp hetaPi).mpr hetaTail, ?_, ?_, ?_⟩
  · have hd := hasDerivAt_stationaryPacketPhase
      X beta (-eta * beta * X) (Real.log (eta / (2 * Real.pi)))
    rw [hzero] at hd
    exact hd
  · rw [htAbs]
  · rw [htAbs]
    have hbetaAbs : |beta| = beta := abs_of_pos hbeta
    rw [hbetaAbs]
    have hden : 0 < eta := hetaPos
    rw [le_div_iff₀ hden]
    nlinarith [mul_pos hbeta hX]
  · rw [hexp]
    constructor
    · rw [lt_div_iff₀ (by positivity : 0 < X / 2)]
      nlinarith
    · rw [div_lt_iff₀ (by positivity : 0 < X / 2)]
      have hetaPiOne : eta / (2 * Real.pi) < 1 :=
        hetaTail.trans (Real.exp_lt_one_iff.mpr (by norm_num))
      nlinarith

end

end MAPMRTSourceLowerCollarResonance

#print axioms MAPMRTSourceLowerCollarResonance.hasDerivAt_stationaryPacketPhase_zero_at_lowerCollarResonance
#print axioms MAPMRTSourceLowerCollarResonance.lowerCollarResonance_innerCoordinate_mem_Ioo_at_endpoint
#print axioms MAPMRTSourceLowerCollarResonance.hard_regime_lower_frequency_endpoint_has_lowerCollarResonance
