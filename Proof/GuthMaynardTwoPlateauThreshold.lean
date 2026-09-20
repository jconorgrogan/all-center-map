import GuthMaynardTwoPlateauSmoothingBridge

/-!
# Critical threshold transfer for the two local scales

The source critical range is `4 N^(7/10) ≤ V ≤ N^(8/10)`.  Each local scale
`M ∈ [N/2,2N]` therefore sees the split threshold `V/2` in its own critical
range.  This is the numerical bridge needed after the exact two-plateau
decomposition.
-/

namespace GuthMaynardTwoPlateauThreshold

open GuthMaynardTwoPlateauSmoothingBridge

noncomputable section

theorem half_threshold_transfer {N M V : ℝ}
    (hN : 1 ≤ N) (hMlow : N / 2 ≤ M) (hMhigh : M ≤ 2 * N)
    (hVlow : 4 * Real.rpow N (7 / 10 : ℝ) ≤ V)
    (hVhigh : V ≤ Real.rpow N (8 / 10 : ℝ)) :
    Real.rpow M (7 / 10 : ℝ) ≤ V / 2 ∧
      V / 2 ≤ Real.rpow M (8 / 10 : ℝ) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hM0 : 0 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hA : 0 ≤ Real.rpow N (7 / 10 : ℝ) := Real.rpow_nonneg hN0 _
  have hlow : Real.rpow M (7 / 10 : ℝ) ≤
      2 * Real.rpow N (7 / 10 : ℝ) := by
    calc
      Real.rpow M (7 / 10 : ℝ) ≤
          Real.rpow (2 * N) (7 / 10 : ℝ) := by
        apply Real.rpow_le_rpow hM0
        · linarith
        · norm_num
      _ = Real.rpow 2 (7 / 10 : ℝ) * Real.rpow N (7 / 10 : ℝ) := by
        exact Real.mul_rpow (by norm_num) hN0
      _ ≤ 2 * Real.rpow N (7 / 10 : ℝ) := by
        have h2 : Real.rpow 2 (7 / 10 : ℝ) ≤ 2 := by
          calc
            Real.rpow 2 (7 / 10 : ℝ) ≤ Real.rpow 2 1 :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        exact mul_le_mul_of_nonneg_right h2 hA
  have hlow' : Real.rpow M (7 / 10 : ℝ) ≤ V / 2 := by
    linarith
  have hhalf_eq : Real.rpow (1 / 2 : ℝ) (8 / 10 : ℝ) =
      (Real.rpow 2 (8 / 10 : ℝ))⁻¹ := by
    calc
      Real.rpow (1 / 2 : ℝ) (8 / 10 : ℝ) =
          Real.rpow 1 (8 / 10 : ℝ) / Real.rpow 2 (8 / 10 : ℝ) := by
        exact Real.div_rpow (by norm_num) (by norm_num) _
      _ = (Real.rpow 2 (8 / 10 : ℝ))⁻¹ := by
        norm_num [Real.one_rpow]
  have hhalfpow : (1 / 2 : ℝ) ≤
      Real.rpow (1 / 2 : ℝ) (8 / 10 : ℝ) := by
    have hneg : Real.rpow 2 (-1 : ℝ) ≤
        Real.rpow 2 (-(8 / 10 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hneg' : (Real.rpow 2 1)⁻¹ ≤
        (Real.rpow 2 (8 / 10 : ℝ))⁻¹ := by
      simpa [Real.rpow_neg] using hneg
    rw [hhalf_eq]
    simpa [Real.rpow_one] using hneg'
  have hupper : V / 2 ≤ Real.rpow M (8 / 10 : ℝ) := by
    have hA8 : 0 ≤ Real.rpow N (8 / 10 : ℝ) := Real.rpow_nonneg hN0 _
    have hbase : Real.rpow (N / 2) (8 / 10 : ℝ) ≤
        Real.rpow M (8 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hMlow (by norm_num)
    have hsplit : Real.rpow (N / 2) (8 / 10 : ℝ) =
        Real.rpow N (8 / 10 : ℝ) *
          Real.rpow (1 / 2) (8 / 10 : ℝ) := by
      have hd := Real.div_rpow hN0 (by norm_num : (0 : ℝ) ≤ 2)
        (8 / 10 : ℝ)
      calc
        _ = Real.rpow N (8 / 10 : ℝ) /
            Real.rpow 2 (8 / 10 : ℝ) := hd
        _ = Real.rpow N (8 / 10 : ℝ) *
            (Real.rpow 2 (8 / 10 : ℝ))⁻¹ := by ring
        _ = _ := by rw [← hhalf_eq]
    calc
      V / 2 ≤ Real.rpow N (8 / 10 : ℝ) / 2 := by linarith
      _ ≤ Real.rpow N (8 / 10 : ℝ) *
          Real.rpow (1 / 2) (8 / 10 : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hhalfpow)
          hA8
      _ = Real.rpow (N / 2) (8 / 10 : ℝ) := hsplit.symm
      _ ≤ Real.rpow M (8 / 10 : ℝ) := hbase
  exact ⟨hlow', hupper⟩

end
end GuthMaynardTwoPlateauThreshold

#print axioms GuthMaynardTwoPlateauThreshold.half_threshold_transfer
