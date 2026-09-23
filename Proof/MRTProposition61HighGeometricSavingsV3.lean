import MRTProposition61HighTruncationParametersV3

/-! # The free-T mixed bracket at the literal MAP parameter choices -/

namespace MRTProposition61HighGeometricSavingsV3

open MRTProposition61HighTruncationParametersV3

noncomputable section
set_option maxHeartbeats 1000000

/-- All four high mixed-mean sectors retain a saving at the actual aperture.
`hcollar` and `hN` are supplied by endpoint geometry and active-mask pruning. -/
theorem high_free_core_le_three_losses
    {X H U q Q L N delta reserve : ℝ}
    (hX : 1 ≤ X) (hU : 1 ≤ U) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hdelta : delta ≤ 1 / 240) (hr : reserve ≤ 1 / 1200)
    (hH : H = (1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve))
    (hqu : q * U ≤ H / Q) (hcollar : q * L ≤ X / Real.sqrt Q)
    (hN : N ≤ Real.rpow X (7 / 8 : ℝ)) :
    q * (2 * L + 4 * ((U / H) * Real.rpow X (23 / 24 : ℝ)) +
      4 * U + N + 2 * X / U) ≤
      9 * X * (Q * Real.rpow X (-delta) + 1 / Real.sqrt Q + Q / U) := by
  have hX0 : 0 < X := by linarith
  have hQ : 1 ≤ Q := hq.trans hqQ
  have hQ0 : 0 < Q := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hU0 : 0 < U := by linarith
  have hH0 : 0 < H := by rw [hH]; exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  let R := Real.rpow X (-delta)
  have hR : 0 ≤ R := Real.rpow_nonneg hX0.le _
  have hp (a : ℝ) (ha : a ≤ 1 - delta) : Real.rpow X a ≤ X * R := by
    calc
      _ ≤ Real.rpow X (1 - delta) := Real.rpow_le_rpow_of_exponent_le hX ha
      _ = X * R := by
        have he := Real.rpow_add hX0 1 (-delta)
        simpa only [Real.rpow_one, sub_eq_add_neg] using! he
  have hHpow : H ≤ X * R := by
    rw [hH]
    have hh := hp (2 / 15 + reserve) (by linarith)
    have hh0 : 0 ≤ Real.rpow X (2 / 15 + reserve) := Real.rpow_nonneg hX0.le _
    linarith
  have hT := highFreeTruncation_mul_modulus_le (sigma := (1 / 24 : ℝ)) hX0.le hH0 hQ0 hqu
  norm_num at hT
  have hTpow : q * ((U / H) * Real.rpow X (23 / 24 : ℝ)) ≤ X * R := by
    have hdiv : Real.rpow X (23 / 24 : ℝ) / Q ≤ Real.rpow X (23 / 24 : ℝ) :=
      div_le_self (Real.rpow_nonneg hX0.le _) hQ
    exact (hT.trans hdiv).trans (hp _ (by linarith))
  have hUbound : q * U ≤ X * R := (hqu.trans (div_le_self hH0.le hQ)).trans hHpow
  have hNbound : q * N ≤ Q * X * R := by
    have hn := mul_le_mul_of_nonneg_left (hN.trans (hp _ (by linarith))) hq0
    have hqR := mul_le_mul_of_nonneg_right hqQ (mul_nonneg hX0.le hR)
    nlinarith
  have hQR : X * R ≤ Q * X * R := by nlinarith [mul_nonneg hX0.le hR]
  have htail : q * (2 * X / U) ≤ Q * (2 * X / U) :=
    mul_le_mul_of_nonneg_right hqQ (by positivity)
  have hb0 : 0 ≤ X / Real.sqrt Q := by positivity
  have hu0 : 0 ≤ Q * X / U := by positivity
  have hsum : q * (2 * L + 4 * ((U / H) * Real.rpow X (23 / 24 : ℝ)) +
      4 * U + N + 2 * X / U) ≤
      9 * Q * X * R + 2 * X / Real.sqrt Q + 2 * Q * X / U := by
    ring_nf at hTpow hUbound hNbound hQR htail hcollar ⊢
    linarith only [hTpow, hUbound, hNbound, hQR, htail, hcollar]
  calc
    _ ≤ _ := hsum
    _ ≤ 9 * X * (Q * R + 1 / Real.sqrt Q + Q / U) := by
      ring_nf at hb0 hu0 ⊢
      linarith only [hb0, hu0]
    _ = _ := rfl

end
end MRTProposition61HighGeometricSavingsV3

#print axioms MRTProposition61HighGeometricSavingsV3.high_free_core_le_three_losses
