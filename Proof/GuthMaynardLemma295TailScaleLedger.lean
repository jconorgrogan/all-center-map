import GuthMaynardLemma295FloorTruncation

/-!
# Scale ledger for the discarded dual tail in Lemma 29.5

After replacing `floor M + 1` by `M`, both tail powers combine with `N^sigma`
into `(MN)^sigma`.  Since `sigma < 0`, the source lower bound `Q <= MN`
then produces the required negative power of `Q`.
-/

namespace GuthMaynardLemma295TailScaleLedger

noncomputable section

theorem dualTail_scale_le
    {M N Q sigma : ℝ}
    (hM : 1 ≤ M) (hN : 0 < N) (hQ : 0 < Q)
    (hQMN : Q ≤ M * N) (hsigma : sigma < 0) :
    (Real.rpow M (sigma - 1) +
        Real.rpow M sigma / (-sigma)) * Real.rpow N sigma ≤
      (1 + 1 / (-sigma)) * Real.rpow Q sigma := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMNpos : 0 < M * N := mul_pos hMpos hN
  have hNpow : 0 ≤ Real.rpow N sigma := Real.rpow_nonneg hN.le _
  have hMpow : 0 ≤ Real.rpow M sigma := Real.rpow_nonneg hMpos.le _
  have hsigden : 0 < -sigma := by linarith
  have hfirst : Real.rpow M (sigma - 1) ≤ Real.rpow M sigma :=
    Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have hcombine :
      Real.rpow M sigma * Real.rpow N sigma =
        Real.rpow (M * N) sigma :=
    (Real.mul_rpow hMpos.le hN.le).symm
  have hnegative : Real.rpow (M * N) sigma ≤ Real.rpow Q sigma :=
    Real.rpow_le_rpow_of_nonpos hQ hQMN hsigma.le
  calc
    (Real.rpow M (sigma - 1) + Real.rpow M sigma / (-sigma)) *
        Real.rpow N sigma ≤
      (Real.rpow M sigma + Real.rpow M sigma / (-sigma)) *
        Real.rpow N sigma := by gcongr
    _ = (1 + 1 / (-sigma)) *
        (Real.rpow M sigma * Real.rpow N sigma) := by ring
    _ = (1 + 1 / (-sigma)) * Real.rpow (M * N) sigma := by rw [hcombine]
    _ ≤ (1 + 1 / (-sigma)) * Real.rpow Q sigma := by
      exact mul_le_mul_of_nonneg_left hnegative (by positivity)

end

end GuthMaynardLemma295TailScaleLedger

#print axioms GuthMaynardLemma295TailScaleLedger.dualTail_scale_le
