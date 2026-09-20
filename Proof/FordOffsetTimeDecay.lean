import FordOffsetLogSumDecay
import FordDegreeScaleBounds

open scoped BigOperators
noncomputable section

namespace FordOffsetTimeDecay

open FordWEnvelopeScalar FordOffsetLogTransfer FordDecayExponent

/-- Time-parameter wrapper for the offset logarithmic sum decay estimate. -/
theorem offset_time_decay
    {N H k : ℕ} {t lam u : ℝ}
    (ht : 0 < t) (hN : 2 ≤ N) (hH : H ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hLam : lam = Real.log t / Real.log (N : ℝ))
    (hdegree : k = Nat.floor (lam / b) + 1)
    (hlam : 2000 * b ≤ lam)
    (hNlarge : 1024 * (k + 1) ^ 2 ≤ N)
    (hlog : 256000000000000 * lam ^ 4 ≤ Real.log (N : ℝ)) :
    ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
      4 * (N : ℝ) ^
        (1 - (1 : ℝ) / (10000000000 * lam ^ 2)) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hNgt
  have hlogNne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogNpos
  have htime : (N : ℝ) ^ lam = t := by
    rw [Real.rpow_def_of_pos hNpos, hLam]
    rw [show Real.log (N : ℝ) * (Real.log t / Real.log (N : ℝ)) = Real.log t by
      field_simp]
    exact Real.exp_log ht
  have hquartic := FordDegreeScaleBounds.quartic_degree_bound hlam
  have hlogold :
      1000000000000 * (k : ℝ) ^ 4 ≤ Real.log (N : ℝ) := by
    have hq : 1000000000000 * (k : ℝ) ^ 4 ≤
        256000000000000 * lam ^ 4 := by
      simpa only [hdegree] using hquartic
    exact hq.trans hlog
  have hdec := FordOffsetLogSumDecay.offset_log_sum_decay
    (N := N) (H := H) (k := k) (lam := lam) (u := u)
    hu hu1 hN1 hH hlam hdegree hNlarge hlogold
  have hdl := FordDegreeScaleBounds.decay_lower_bound hlam
  have hdl' :
      (1 : ℝ) / (10000000000 * lam ^ 2) ≤ FordDecayExponent.decay k := by
    simpa only [hdegree] using hdl
  have hexp :
      1 - FordDecayExponent.decay k ≤
        1 - (1 : ℝ) / (10000000000 * lam ^ 2) := by
    linarith
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexp
  have hdec' := hdec.trans
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4))
  simpa [htime] using hdec'

end FordOffsetTimeDecay

#print axioms FordOffsetTimeDecay.offset_time_decay
