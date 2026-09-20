import MRTSourceLowerCollarOffResonanceCell

/-! # The two literal off-resonance cells for the lower collar -/

namespace MAPMRTSourceLowerCollarOffResonanceCells

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTCorollary53Source
open MAPMRTVanDerCorput MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarResonance MAPMRTSourceLowerCollarPhasePartition
open MAPMRTSourceLowerCollarOffResonanceCell

noncomputable section

/-- The explicit endpoint-aware two-IBP expression. -/
def offResonanceCellBudget
    (a b d P C0 C1 C2 : ℝ) : ℝ :=
  (C0 * Real.exp (a / 2) + C0 * Real.exp (b / 2)) * (1 / d) +
  (((C1 * Real.exp (a / 2) + C1 * Real.exp (b / 2)) * (1 / d) +
    (C0 * Real.exp (a / 2) + C0 * Real.exp (b / 2)) *
      (P / d ^ 2)) * (1 / d)) +
  ((1 / d) ^ 2 * (2 * C2 * Real.exp (b / 2)) +
    3 * (1 / d) * (P / d ^ 2) *
      (2 * C1 * Real.exp (b / 2)) +
    ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
      (P / d ^ 2) ^ 2) * (2 * C0 * Real.exp (b / 2)))

/-- Two integrations by parts on the actual lower cell, from the left inner
cutoff boundary to half the stationary scale.  The strict spatial inequality
only removes the single endpoint `x=X/2`; that null endpoint is handled when
the cell bounds are integrated in `x`. -/
theorem norm_sourceLowerCollarIntegral_le_lowerCellBudget
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
    let a := Real.log ((x - X / 2) / X)
    let b := Real.log (q / 2)
    let U := q / 2
    let d := |beta| * X * (q / 2)
    let P := |beta| * X * (q / 2)
    let C0 := 4 * B1 * U
    let C1 := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
    let C2 := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
      2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
    ‖∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w‖ ≤
      offResonanceCellBudget a b d P C0 C1 C2 := by
  dsimp
  let a : ℝ := Real.log ((x - X / 2) / X)
  let b : ℝ := Real.log (q / 2)
  let U : ℝ := q / 2
  let d : ℝ := |beta| * X * (q / 2)
  let P : ℝ := |beta| * X * (q / 2)
  have hratio : 0 < (x - X / 2) / X := by positivity
  have hU : 0 < U := by unfold U; positivity
  have hratioU : (x - X / 2) / X ≤ U := by
    unfold U
    rw [div_le_iff₀ hX]
    simpa [mul_comm] using hxCell
  have hab : a ≤ b := by
    unfold a b U at *
    exact Real.log_le_log hratio hratioU
  have hexpb : Real.exp b = U := by
    unfold b U
    exact Real.exp_log (by positivity)
  have hd : 0 < d := by
    unfold d
    have : 0 < |beta| := abs_pos.mpr hbeta
    positivity
  have hP : 0 ≤ P := by unfold P; positivity
  have hpLower : ∀ w ∈ Set.Icc a b,
      d ≤ |beta * X * Real.exp w + t / (2 * Real.pi)| := by
    intro w hw
    have hwU : Real.exp w ≤ q / 2 := by
      rw [← Real.exp_log (by positivity : 0 < q / 2)]
      exact Real.exp_le_exp.mpr hw.2
    unfold d
    rw [hqEq]
    exact stationaryPacketPhase_deriv_lower_below_resonanceCell
      hX hbeta (hqEq ▸ hqPos) (by simpa [← hqEq] using hwU)
  have hpUpper : ∀ w ∈ Set.Icc a b,
      |beta * X * Real.exp w| ≤ P := by
    intro w hw
    have hwU : Real.exp w ≤ q / 2 := by
      rw [← Real.exp_log (by positivity : 0 < q / 2)]
      exact Real.exp_le_exp.mpr hw.2
    unfold P
    rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
    exact mul_le_mul_of_nonneg_left hwU
      (mul_nonneg (abs_nonneg beta) hX.le)
  have hmain := norm_sourceLowerCollarIntegral_le_offResonanceCellBudget
    hab hX hxStrict.le hd hP hU hexpb.le hpLower hpUpper hB1 hB2
    hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
    hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
    houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
  simpa [offResonanceCellBudget, a, b, U, d, P] using hmain

/-- Two integrations by parts on the actual upper cell, from twice the
stationary scale to the outer-cutoff transition point `w=-10`.  Both
artificial endpoint values are retained in `offResonanceCellBudget`. -/
theorem norm_sourceLowerCollarIntegral_le_upperCellBudget
    {X x beta t q B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hxLower : X / 2 ≤ x)
    (hbeta : beta ≠ 0) (hqPos : 0 < q)
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
    ‖∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w‖ ≤
      offResonanceCellBudget a b d P C0 C1 C2 := by
  dsimp
  let a : ℝ := Real.log (2 * q)
  let b : ℝ := -10
  let U : ℝ := Real.exp (-10)
  let d : ℝ := |beta| * X * q
  let P : ℝ := |beta| * X * U
  have htwoq : 0 < 2 * q := by positivity
  have hab : a ≤ b := by
    unfold a b
    rw [← Real.log_exp (-10)]
    exact Real.log_le_log htwoq hqTail
  have hU : 0 < U := by unfold U; positivity
  have hexpb : Real.exp b = U := by rfl
  have hd : 0 < d := by
    unfold d
    have : 0 < |beta| := abs_pos.mpr hbeta
    positivity
  have hP : 0 ≤ P := by unfold P; positivity
  have hpLower : ∀ w ∈ Set.Icc a b,
      d ≤ |beta * X * Real.exp w + t / (2 * Real.pi)| := by
    intro w hw
    have hwq : 2 * q ≤ Real.exp w := by
      rw [← Real.exp_log htwoq]
      exact Real.exp_le_exp.mpr hw.1
    unfold d
    rw [hqEq]
    exact stationaryPacketPhase_deriv_lower_above_resonanceCell
      hX hbeta (hqEq ▸ hqPos) (by simpa [← hqEq] using hwq)
  have hpUpper : ∀ w ∈ Set.Icc a b,
      |beta * X * Real.exp w| ≤ P := by
    intro w hw
    have hwU : Real.exp w ≤ U := by
      unfold U b at *
      exact Real.exp_le_exp.mpr hw.2
    unfold P
    rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
    exact mul_le_mul_of_nonneg_left hwU
      (mul_nonneg (abs_nonneg beta) hX.le)
  have hmain := norm_sourceLowerCollarIntegral_le_offResonanceCellBudget
    hab hX hxLower hd hP hU hexpb.le hpLower hpUpper hB1 hB2
    hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
    hcutoff'Bound hcutoff''Bound houterDeriv houterSecond
    houterBound houter'Bound houter''Bound hcutoff''Cont houter''Cont
  simpa [offResonanceCellBudget, a, b, U, d, P] using hmain

end
end MAPMRTSourceLowerCollarOffResonanceCells

#print axioms MAPMRTSourceLowerCollarOffResonanceCells.norm_sourceLowerCollarIntegral_le_lowerCellBudget
#print axioms MAPMRTSourceLowerCollarOffResonanceCells.norm_sourceLowerCollarIntegral_le_upperCellBudget
