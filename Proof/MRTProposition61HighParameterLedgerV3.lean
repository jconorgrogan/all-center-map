import Mathlib

/-! # Exact high-packet normalization and the role of Perron truncation

These are scalar identities for the literal mixed-mean majorant, not lower
bounds for the source integral. They distinguish the loss in the current
`X`-padded majorant from a counterexample to the desired source estimate.
-/

namespace MRTProposition61HighParameterLedgerV3

/-- The complete mixed-mean bracket after the source normalization. -/
theorem normalized_high_mixed_core_eq
    {D q U C M N W : ℝ} (hq : q ≠ 0) (hU : U ≠ 0) :
    D / (q * U ^ 2) * (U * q ^ 2 * C * (U * W + U * N + M * N + W)) =
      D * q * C * (W + N + M * N / U + W / U) := by
  field_simp

/-- Increasing the far width cannot remove the `2X` contribution of the
currently hardcoded padded interval. This only diagnoses that majorant. -/
theorem x_padded_majorant_ge_two_X
    {D q U C M N X L : ℝ}
    (hD : 0 ≤ D) (hq : 0 < q) (hU : 0 < U) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hX : 0 ≤ X) (hL : 0 ≤ L) :
    2 * D * q * C * X ≤
      D / (q * U ^ 2) *
        (U * q ^ 2 * C *
          (U * (L + 2 * X + 2 * U) + U * N + M * N + (L + 2 * X + 2 * U))) := by
  rw [normalized_high_mixed_core_eq hq.ne' hU.ne']
  have hbracket : 2 * X ≤ L + 2 * X + 2 * U + N +
      M * N / U + (L + 2 * X + 2 * U) / U := by
    have h1 : 0 ≤ M * N / U := by positivity
    have h2 : 0 ≤ (L + 2 * X + 2 * U) / U := by positivity
    linarith
  have h := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ D * q * C by positivity)
  convert h using 1 <;> ring

/-- With a free truncation and the sharp-mask product bound, the mixed core
retains the actual interval and the useful `MN/U` saving. -/
theorem normalized_high_core_le_free_truncation
    {D q U C M N X L T : ℝ}
    (hD : 0 ≤ D) (hq : 0 < q) (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hproduct : M * N ≤ 2 * X) :
    D / (q * U ^ 2) *
      (U * q ^ 2 * C *
        (U * (L + 2 * T + 2 * U) + U * N + M * N + (L + 2 * T + 2 * U))) ≤
      D * q * C * (2 * L + 4 * T + 4 * U + N + 2 * X / U) := by
  have hU0 : 0 < U := by linarith
  rw [normalized_high_mixed_core_eq hq.ne' hU0.ne']
  have hprod := div_le_div_of_nonneg_right hproduct hU0.le
  have hwidth : (L + 2 * T + 2 * U) / U ≤ L + 2 * T + 2 * U :=
    div_le_self (by positivity) hU
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- Each remaining high-core sector now has its own actual geometric saving.
This is the positive route after active-mask pruning and free truncation. -/
theorem normalized_high_core_le_parameter_envelope
    {D q Q U C M N X L T H R S : ℝ}
    (hD : 0 ≤ D) (hq : 0 < q) (hQ : 0 ≤ Q) (hqQ : q ≤ Q)
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hproduct : M * N ≤ 2 * X)
    (hcollar : q * L ≤ X / Real.sqrt Q)
    (htrunc : q * T ≤ S / Q) (hwidth : q * U ≤ H / Q)
    (hlong : N ≤ R) :
    D / (q * U ^ 2) *
      (U * q ^ 2 * C *
        (U * (L + 2 * T + 2 * U) + U * N + M * N + (L + 2 * T + 2 * U))) ≤
      D * C * (2 * X / Real.sqrt Q + 4 * S / Q + 4 * H / Q +
        Q * R + 2 * Q * X / U) := by
  have hbase := normalized_high_core_le_free_truncation hD hq hU hC hL hT hproduct
  have hNq : q * N ≤ Q * R :=
    (mul_le_mul_of_nonneg_left hlong hq.le).trans
      (mul_le_mul_of_nonneg_right hqQ hR)
  have hU0 : 0 ≤ U := by linarith
  have hqX : q * (2 * X / U) ≤ Q * (2 * X / U) :=
    mul_le_mul_of_nonneg_right hqQ (by positivity)
  have hsum : q * (2 * L + 4 * T + 4 * U + N + 2 * X / U) ≤
      2 * X / Real.sqrt Q + 4 * S / Q + 4 * H / Q + Q * R + 2 * Q * X / U := by
    ring_nf at hcollar htrunc hwidth hNq hqX ⊢
    linarith only [hcollar, htrunc, hwidth, hNq, hqX]
  calc
    _ ≤ _ := hbase
    _ = D * C * (q * (2 * L + 4 * T + 4 * U + N + 2 * X / U)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg hD hC)

end MRTProposition61HighParameterLedgerV3

#print axioms MRTProposition61HighParameterLedgerV3.x_padded_majorant_ge_two_X
#print axioms MRTProposition61HighParameterLedgerV3.normalized_high_core_le_parameter_envelope
