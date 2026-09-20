import PostA5RecenteredDetectorAbsorption

/-!
# Source-normalized detector budget

The direct Type-II branch in `PostA5RecenteredSourceSplit` needs the literal
budget `E + V + V`, rather than the bridge-facing budget
`E + V + C_beta(T) * V`.  Since `C_beta(T)` tends to zero on the high strip,
the latter cannot imply the former by monotonicity.  This file proves the
source budget directly from the repaired polynomial-height detector envelope.
-/

namespace PostA5RecenteredSourceBudget

open Filter CGLProofDAG MAPAppendixA4RecenteredGammaRepair
open PostA5RecenteredDetectorAbsorption

noncomputable section

/-- At the floor mollifier scale, the repaired detector error and two copies
of the input-loss threshold fit inside the exact source-normalized detector
budget.  No high-strip beta estimate is used here. -/
theorem eventually_recentered_source_budget_floor_inputLoss
    (K kappa eta : ℝ) (hkappa : 0 < kappa)
    (hkappaCap : kappa < 1 / 20) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) (rho : ℂ),
        (q : ℝ) ≤ Real.rpow (Real.log T) K →
        |rho.im| ≤ T →
        detectorTruncationErrorEnvelopePolynomialHeight q
              ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T +
            Real.rpow T (-inputLoss kappa eta) +
            Real.rpow T (-inputLoss kappa eta) ≤
          Real.exp (-(1 / Real.rpow T (1 / 2))) := by
  have hloss : 0 < inputLoss kappa eta := inputLoss_pos hkappa heta
  have henv :=
    eventually_cost_mul_detector_envelope_polylog_level_le_rpow_neg
      K (2 * kappa) 0 1
  have hVgrow := (tendsto_rpow_atTop hloss).eventually
    (eventually_ge_atTop 16)
  have hYgrow :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_ge_atTop 2)
  have hpowGrow := (tendsto_rpow_atTop hkappa).eventually
    (eventually_ge_atTop 2)
  filter_upwards [henv, hVgrow, hYgrow, hpowGrow,
    eventually_ge_atTop 16] with T henvT hVgrowT hYgrowT hpowGrowT hT16
  intro q rho hq hheight
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hUscale :
      (⌊Real.rpow T kappa⌋₊ + 1 : ℝ) ≤ Real.rpow T (2 * kappa) := by
    have hpow0 : 0 ≤ Real.rpow T kappa := Real.rpow_nonneg hT0 _
    have hfloor : (⌊Real.rpow T kappa⌋₊ : ℝ) ≤
        Real.rpow T kappa := Nat.floor_le hpow0
    have hpowGrowT' : 2 ≤ Real.rpow T kappa := by exact hpowGrowT
    have hquad : Real.rpow T kappa + 1 ≤
        Real.rpow T kappa * Real.rpow T kappa := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hpowGrowT') (sub_nonneg.mpr hpowGrowT')]
    calc
      (⌊Real.rpow T kappa⌋₊ + 1 : ℝ) ≤
          Real.rpow T kappa + 1 := by
            linarith
      _ ≤ Real.rpow T kappa * Real.rpow T kappa := hquad
      _ = Real.rpow T (2 * kappa) := by
        change T ^ kappa * T ^ kappa = T ^ (2 * kappa)
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
  have henvRaw := henvT q ⌊Real.rpow T kappa⌋₊ rho 1
    hq hUscale hheight (by norm_num) (by simp [Real.rpow_zero])
  have henvPower :
      detectorTruncationErrorEnvelopePolynomialHeight q
          ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T ≤
        Real.rpow T (-1) := by
    simpa using henvRaw
  have hTinv : Real.rpow T (-1) ≤ 1 / 16 := by
    rw [show Real.rpow T (-1) = T⁻¹ by
      change T ^ (-1 : ℝ) = T⁻¹
      simp [Real.rpow_neg_one]]
    simpa [one_div] using
      ((inv_le_inv₀ hTpos (by norm_num : (0 : ℝ) < 16)).2 hT16)
  have henvSmall :
      detectorTruncationErrorEnvelopePolynomialHeight q
          ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T ≤
        1 / 16 := henvPower.trans hTinv
  have hVsmall : Real.rpow T (-inputLoss kappa eta) ≤ 1 / 16 := by
    rw [show Real.rpow T (-inputLoss kappa eta) =
        (Real.rpow T (inputLoss kappa eta))⁻¹ by
      change T ^ (-inputLoss kappa eta) =
        (T ^ (inputLoss kappa eta))⁻¹
      exact Real.rpow_neg hT0 (inputLoss kappa eta)]
    simpa [one_div] using
      ((inv_le_inv₀ (Real.rpow_pos_of_pos hTpos (inputLoss kappa eta))
        (by norm_num : (0 : ℝ) < 16)).2 hVgrowT)
  have hinvY : 1 / Real.rpow T (1 / 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hYgrowT
  have hrhs : 1 / 2 ≤ Real.exp (-(1 / Real.rpow T (1 / 2))) := by
    have hadd := Real.add_one_le_exp (-(1 / Real.rpow T (1 / 2)))
    linarith
  calc
    detectorTruncationErrorEnvelopePolynomialHeight q
          ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T +
        Real.rpow T (-inputLoss kappa eta) +
        Real.rpow T (-inputLoss kappa eta) ≤
      1 / 16 + 1 / 16 + 1 / 16 :=
        add_le_add (add_le_add henvSmall hVsmall) hVsmall
    _ ≤ 1 / 2 := by norm_num
    _ ≤ Real.exp (-(1 / Real.rpow T (1 / 2))) := hrhs

/-- The same source-normalized budget at the manuscript height `T=X^tau`. -/
theorem eventually_recentered_source_budget_floor_inputLoss_at_rpow_height
    (K kappa eta tau : ℝ) (hkappa : 0 < kappa)
    (hkappaCap : kappa < 1 / 20) (heta : 0 < eta) (htau : 0 < tau) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ (q : ℕ) (rho : ℂ),
        (q : ℝ) ≤
            Real.rpow (Real.log (Real.rpow X tau)) K →
        |rho.im| ≤ Real.rpow X tau →
        detectorTruncationErrorEnvelopePolynomialHeight q
              ⌊Real.rpow (Real.rpow X tau) kappa⌋₊ rho
              (Real.rpow (Real.rpow X tau) (1 / 2))
              (Real.rpow X tau) +
            Real.rpow (Real.rpow X tau) (-inputLoss kappa eta) +
            Real.rpow (Real.rpow X tau) (-inputLoss kappa eta) ≤
          Real.exp (-(1 /
            Real.rpow (Real.rpow X tau) (1 / 2))) := by
  exact (tendsto_rpow_atTop htau).eventually
    (eventually_recentered_source_budget_floor_inputLoss
      K kappa eta hkappa hkappaCap heta)

end
end PostA5RecenteredSourceBudget

#print axioms PostA5RecenteredSourceBudget.eventually_recentered_source_budget_floor_inputLoss
#print axioms PostA5RecenteredSourceBudget.eventually_recentered_source_budget_floor_inputLoss_at_rpow_height
