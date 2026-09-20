import FordThresholdTimeDecay
import FordDegreeSizeFromLog

open scoped BigOperators
noncomputable section
namespace FordOffsetThresholdBound

/-- Actual offset logarithmic exponential sum, with no auxiliary degree or
moment-size hypotheses. This theorem covers only the displayed lambda range. -/
theorem offset_threshold_bound
    {N H : ℕ} {t u : ℝ}
    (ht : 1 < t) (hN : 2 ≤ N) (hH : H ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hlam : 2000 * FordWEnvelopeScalar.b ≤ Real.log t / Real.log (N : ℝ))
    (hthreshold : (1000 : ℝ) * (Real.log t) ^ ((4 : ℝ) / 5) ≤ Real.log (N : ℝ)) :
    ‖∑ n ∈ Finset.range H,
        FordOffsetLogTransfer.offsetPhase t u (N + n)‖ ≤
      4 * (N : ℝ) ^ (1 - (1 : ℝ) /
        (10000000000 * (Real.log t / Real.log (N : ℝ)) ^ 2)) := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog := FordLogScaleThreshold.ratio_fourth_of_threshold
    hlogN (Real.log_pos ht) hthreshold
  have hsize := FordDegreeSizeFromLog.degree_size_from_log hN rfl hlam hlog
  exact FordThresholdTimeDecay.threshold_time_decay
    ht hN hH hu hu1 rfl rfl hlam hsize hthreshold

end FordOffsetThresholdBound
#print axioms FordOffsetThresholdBound.offset_threshold_bound
