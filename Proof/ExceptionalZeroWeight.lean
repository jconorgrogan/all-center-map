import ZeroFreeSiegelBorelBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polylogarithmic decay of an exceptional-real-zero weight

This staging module isolates the exact real-analysis implication needed by the
simultaneous AP route.  It does not assert the existence, uniqueness, or gap of
an exceptional zero.
-/

namespace MAPZeroFreeSiegelSpine

open Filter Asymptotics

noncomputable section

/-- A Siegel-shaped gap at a polylogarithmic conductor turns the exceptional
weight into a prescribed logarithmic saving once the explicit exponent trade
has been reached. -/
theorem exceptionalWeight_le_logSaving_of_gap
    {A K ε c X β : ℝ} {q : ℕ} [NeZero q]
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hc : 0 < c)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (hgap : c * Real.rpow (q : ℝ) (-ε) ≤ 1 - β)
    (htrade : A * Real.log (Real.log X) ≤
      2 * c * Real.rpow (Real.log X) (1 - K * ε)) :
    Real.rpow X (2 * (β - 1)) ≤
      Real.rpow (Real.log X) (-A) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlogone : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlogone
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hqpowpos : 0 < Real.rpow (q : ℝ) ε :=
    Real.rpow_pos_of_pos hqpos ε
  have hlogKnonneg : 0 ≤ Real.rpow (Real.log X) K :=
    Real.rpow_nonneg hlogpos.le K
  have hqpow : Real.rpow (q : ℝ) ε ≤
      Real.rpow (Real.log X) (K * ε) := by
    calc
      Real.rpow (q : ℝ) ε ≤
          Real.rpow (Real.rpow (Real.log X) K) ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg q) hq hε
      _ = Real.rpow (Real.log X) (K * ε) := by
        exact (Real.rpow_mul hlogpos.le K ε).symm
  have hinv : Real.rpow (Real.log X) (-K * ε) ≤
      Real.rpow (q : ℝ) (-ε) := by
    calc
      Real.rpow (Real.log X) (-K * ε) =
          (Real.rpow (Real.log X) (K * ε))⁻¹ := by
        rw [show -K * ε = -(K * ε) by ring]
        exact Real.rpow_neg hlogpos.le (K * ε)
      _ ≤ (Real.rpow (q : ℝ) ε)⁻¹ :=
        (inv_le_inv₀
          (Real.rpow_pos_of_pos hlogpos (K * ε)) hqpowpos).2 hqpow
      _ = Real.rpow (q : ℝ) (-ε) :=
        (Real.rpow_neg hqpos.le ε).symm
  have hgap' : c * Real.rpow (Real.log X) (-K * ε) ≤ 1 - β :=
    (mul_le_mul_of_nonneg_left hinv hc.le).trans hgap
  have hpowmerge : Real.rpow (Real.log X) (1 - K * ε) =
      Real.log X * Real.rpow (Real.log X) (-K * ε) := by
    calc
      Real.rpow (Real.log X) (1 - K * ε) =
          Real.rpow (Real.log X) (1 + (-K * ε)) := by ring_nf
      _ = Real.rpow (Real.log X) 1 *
          Real.rpow (Real.log X) (-K * ε) :=
        Real.rpow_add hlogpos 1 (-K * ε)
      _ = Real.log X * Real.rpow (Real.log X) (-K * ε) := by simp
  have hexponent : Real.log X * (2 * (β - 1)) ≤
      Real.log (Real.log X) * (-A) := by
    rw [hpowmerge] at htrade
    have hfac : 0 ≤ 2 * Real.log X := mul_nonneg (by norm_num) hlogpos.le
    have hmul := mul_le_mul_of_nonneg_left hgap' hfac
    nlinarith
  calc
    Real.rpow X (2 * (β - 1)) =
        Real.exp (Real.log X * (2 * (β - 1))) :=
      Real.rpow_def_of_pos hXpos _
    _ ≤ Real.exp (Real.log (Real.log X) * (-A)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.rpow (Real.log X) (-A) :=
      (Real.rpow_def_of_pos hlogpos _).symm

/-- Direct composition with the already certified mean-value bridge from a
Siegel lower bound at `1` to a gap at a real zero.  The derivative majorant is
kept as a literal premise, so this theorem does not claim the remaining
near-one derivative estimate. -/
theorem exceptionalWeight_le_logSaving_of_siegel_and_deriv
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A K ε c M X β : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hc : 0 < c) (hM : 0 < M)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (hβ : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hderiv : ∀ x ∈ Set.Ico β 1,
      ‖deriv (DirichletCharacter.LFunction χ) x‖ ≤ M)
    (hSiegel : c * Real.rpow (q : ℝ) (-ε) ≤
      ‖DirichletCharacter.LFunction χ 1‖)
    (htrade : A * Real.log (Real.log X) ≤
      2 * (c / M) * Real.rpow (Real.log X) (1 - K * ε)) :
    Real.rpow X (2 * (β - 1)) ≤
      Real.rpow (Real.log X) (-A) := by
  have hgap := zero_gap_lower_of_siegel_power_bound
    χ hχ hβ hM hzero hderiv hSiegel
  apply exceptionalWeight_le_logSaving_of_gap hX hε (div_pos hc hM) hq
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgap
  · exact htrade

end
end MAPZeroFreeSiegelSpine

#print axioms MAPZeroFreeSiegelSpine.exceptionalWeight_le_logSaving_of_gap
#print axioms MAPZeroFreeSiegelSpine.exceptionalWeight_le_logSaving_of_siegel_and_deriv
