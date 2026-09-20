import MRTProposition61TypeIIEndpointWidthV3

/-! # Scalar endpoint-width cancellation in the Type-II ledger -/

namespace MRTProposition61TypeIIEndpointLedgerV3

noncomputable section

/-- Expanding the actual long mean-square length
`L + 2*T + 2*U` preserves the collar saving.  This is the scalar bridge
that would be lost by the crude replacement `L ≤ X`. -/
theorem normalized_long_length_terms_le
    {X eta H U L T q G H₀ : ℝ}
    (hX : 0 < X) (heta : 0 < eta) (hH : 0 < H) (hU : 0 < U)
    (hL0 : 0 ≤ L) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hG : 0 ≤ G) (hH₀ : 0 ≤ H₀)
    (hL : L ≤ U * X / (eta * H)) :
    2 * q * (L + 2 * T + 2 * U) / X +
        16 * Real.pi * G * H₀ * (L + 2 * T + 2 * U) / (U * X) ≤
      2 * q * U / (eta * H) + 4 * q * T / X + 4 * q * U / X +
        16 * Real.pi * G * H₀ / (eta * H) +
        32 * Real.pi * G * H₀ * T / (U * X) +
        32 * Real.pi * G * H₀ / X := by
  have hqL : 2 * q * L / X ≤ 2 * q * U / (eta * H) := by
    calc
      2 * q * L / X ≤ 2 * q * (U * X / (eta * H)) / X := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hq)) hX.le
      _ = 2 * q * U / (eta * H) := by field_simp
  have hGL : 16 * Real.pi * G * H₀ * L / (U * X) ≤
      16 * Real.pi * G * H₀ / (eta * H) := by
    have hc : 0 ≤ 16 * Real.pi * G * H₀ := by positivity
    calc
      16 * Real.pi * G * H₀ * L / (U * X) ≤
          16 * Real.pi * G * H₀ * (U * X / (eta * H)) /
            (U * X) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL hc)
          (mul_nonneg hU.le hX.le)
      _ = 16 * Real.pi * G * H₀ / (eta * H) := by field_simp
  calc
    2 * q * (L + 2 * T + 2 * U) / X +
        16 * Real.pi * G * H₀ * (L + 2 * T + 2 * U) / (U * X) =
      2 * q * L / X + 4 * q * T / X + 4 * q * U / X +
        16 * Real.pi * G * H₀ * L / (U * X) +
        32 * Real.pi * G * H₀ * T / (U * X) +
        32 * Real.pi * G * H₀ / X := by field_simp; ring
    _ ≤ _ := by linarith

end
end MRTProposition61TypeIIEndpointLedgerV3

#print axioms MRTProposition61TypeIIEndpointLedgerV3.normalized_long_length_terms_le
