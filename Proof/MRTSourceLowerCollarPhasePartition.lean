import MRTSourceLowerCollarResonance

/-!
# Stationary/nonstationary phase partition for the endpoint collar

Writing `q=-t/(2πβX)`, the first derivative factors as
`βX(exp(w)-q)`.  The cell `q/2 < exp(w) < 2q` has second derivative bounded
below by `|β|Xq/2`; both complementary cells have a uniform first-derivative
gap.  These are the exact inputs for second-derivative van der Corput on the
resonant cell and two integrations by parts outside it.
-/

namespace MAPMRTSourceLowerCollarPhasePartition

open MAPMRTProposition51HardBranch
open MAPMRTSourceLowerCollarResonance

noncomputable section

/-- Exact factorization of the equation-(80) phase derivative around its
stationary ratio. -/
theorem stationaryPacketPhase_deriv_eq_betaX_mul_exp_sub_resonanceRatio
    {X beta t w : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0) :
    beta * X * Real.exp w + t / (2 * Real.pi) =
      beta * X * (Real.exp w - lowerCollarResonanceRatio X beta t) := by
  unfold lowerCollarResonanceRatio
  field_simp [ne_of_gt hX, hbeta, ne_of_gt Real.pi_pos]
  ring

/-- Absolute-value form of the same factorization. -/
theorem abs_stationaryPacketPhase_deriv_eq
    {X beta t w : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0) :
    |beta * X * Real.exp w + t / (2 * Real.pi)| =
      |beta| * X *
        |Real.exp w - lowerCollarResonanceRatio X beta t| := by
  rw [stationaryPacketPhase_deriv_eq_betaX_mul_exp_sub_resonanceRatio hX hbeta]
  simp [abs_mul, abs_of_pos hX, mul_assoc]

/-- First-derivative gap on the cell below half the stationary scale. -/
theorem stationaryPacketPhase_deriv_lower_below_resonanceCell
    {X beta t w : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hw : Real.exp w ≤ lowerCollarResonanceRatio X beta t / 2) :
    |beta| * X * (lowerCollarResonanceRatio X beta t / 2) ≤
      |beta * X * Real.exp w + t / (2 * Real.pi)| := by
  rw [abs_stationaryPacketPhase_deriv_eq hX hbeta]
  have hdist : lowerCollarResonanceRatio X beta t / 2 ≤
      |Real.exp w - lowerCollarResonanceRatio X beta t| := by
    rw [abs_of_nonpos]
    · linarith
    · linarith
  exact mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (abs_nonneg beta) hX.le)

/-- First-derivative gap on the cell above twice the stationary scale. -/
theorem stationaryPacketPhase_deriv_lower_above_resonanceCell
    {X beta t w : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hw : 2 * lowerCollarResonanceRatio X beta t ≤ Real.exp w) :
    |beta| * X * lowerCollarResonanceRatio X beta t ≤
      |beta * X * Real.exp w + t / (2 * Real.pi)| := by
  rw [abs_stationaryPacketPhase_deriv_eq hX hbeta]
  have hdist : lowerCollarResonanceRatio X beta t ≤
      |Real.exp w - lowerCollarResonanceRatio X beta t| := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  exact mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (abs_nonneg beta) hX.le)

/-- Second-derivative curvature on the resonant cell. -/
theorem stationaryPacketPhase_secondDeriv_lower_on_resonanceCell
    {X beta t w : ℝ} (hX : 0 < X)
    (hw : lowerCollarResonanceRatio X beta t / 2 ≤ Real.exp w) :
    |beta| * X * (lowerCollarResonanceRatio X beta t / 2) ≤
      |beta * X * Real.exp w| := by
  rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
  exact mul_le_mul_of_nonneg_left hw
    (mul_nonneg (abs_nonneg beta) hX.le)

/-- Exhaustive scale partition used by the collar proof. -/
theorem resonance_scale_trichotomy (q w : ℝ) :
    Real.exp w ≤ q / 2 ∨
      (q / 2 < Real.exp w ∧ Real.exp w < 2 * q) ∨
      2 * q ≤ Real.exp w := by
  by_cases hlow : Real.exp w ≤ q / 2
  · exact Or.inl hlow
  by_cases hhigh : 2 * q ≤ Real.exp w
  · exact Or.inr (Or.inr hhigh)
  · exact Or.inr (Or.inl ⟨lt_of_not_ge hlow, lt_of_not_ge hhigh⟩)

end

end MAPMRTSourceLowerCollarPhasePartition

#print axioms MAPMRTSourceLowerCollarPhasePartition.stationaryPacketPhase_deriv_eq_betaX_mul_exp_sub_resonanceRatio
#print axioms MAPMRTSourceLowerCollarPhasePartition.abs_stationaryPacketPhase_deriv_eq
#print axioms MAPMRTSourceLowerCollarPhasePartition.stationaryPacketPhase_deriv_lower_below_resonanceCell
#print axioms MAPMRTSourceLowerCollarPhasePartition.stationaryPacketPhase_deriv_lower_above_resonanceCell
#print axioms MAPMRTSourceLowerCollarPhasePartition.stationaryPacketPhase_secondDeriv_lower_on_resonanceCell
#print axioms MAPMRTSourceLowerCollarPhasePartition.resonance_scale_trichotomy
