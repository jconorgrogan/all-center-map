import FordOffsetTimeDecay
import FordLogScaleThreshold

open scoped BigOperators
noncomputable section

namespace FordThresholdTimeDecay

open FordWEnvelopeScalar FordOffsetTimeDecay FordLogScaleThreshold

/-- Compose the logarithmic threshold with the offset time-decay estimate.
The scale hypotheses are kept explicit here; a later wrapper can discharge
`hNlarge` from the selected degree scale. -/
theorem threshold_time_decay
    {N H k : ℕ} {t lam u : ℝ}
    (ht : 1 < t) (hN : 2 ≤ N) (hH : H ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hLam : lam = Real.log t / Real.log (N : ℝ))
    (hdegree : k = Nat.floor (lam / b) + 1)
    (hlam : 2000 * b ≤ lam)
    (hNlarge : 1024 * (k + 1) ^ 2 ≤ N)
    (hthreshold : (1000 : ℝ) * (Real.log t) ^ ((4 : ℝ) / 5) ≤ Real.log (N : ℝ)) :
    ‖∑ n ∈ Finset.range H,
        FordOffsetLogTransfer.offsetPhase t u (N + n)‖ ≤
      4 * (N : ℝ) ^
        (1 - (1 : ℝ) / (10000000000 * lam ^ 2)) := by
  have htpos : 0 < t := by linarith
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hNgt
  have hlogtpos : 0 < Real.log t := Real.log_pos ht
  have hlog := ratio_fourth_of_threshold hlogNpos hlogtpos hthreshold
  have hlog' :
      (256000000000000 : ℝ) * lam ^ 4 ≤ Real.log (N : ℝ) := by
    simpa [hLam] using hlog
  exact FordOffsetTimeDecay.offset_time_decay
    htpos hN hH hu hu1 hLam hdegree hlam hNlarge hlog'

end FordThresholdTimeDecay

#print axioms FordThresholdTimeDecay.threshold_time_decay
