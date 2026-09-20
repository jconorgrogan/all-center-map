import Mathlib

/-! # Exact scalar expansion of the Type-II Lemma 2.10 product -/

namespace MRTProposition61TypeIINormalizedLedgerV3

/-- The four terms in manuscript equation (3.5), before substituting the
specific bounds for `T`, `H₀`, and logarithmic losses.  Here `D` is
`X^delta`, `G` is the finite dyadic dilation `2^prefix.length`, and `c`
is the mean-square constant `8*pi`. -/
theorem normalized_typeII_product_le_four_terms
    {q U X N M T c D G H₀ : ℝ}
    (hq : 1 ≤ q) (hU : 0 < U) (hX : 0 < X) (hD : 0 < D)
    (hN : 0 ≤ N) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hc : 0 ≤ c) (hG : 0 ≤ G) (hH₀ : 0 ≤ H₀)
    (hshortLower : D ≤ 2 * N)
    (hshortUpper : N ≤ G * H₀)
    (hproductUpper : N * M ≤ 2 * X) :
    ((q * (2 * U) + c * N) * (q * T + c * M)) /
        (q * U * X) ≤
      2 * q * T / X + 8 * c / D +
        c * G * H₀ * T / (U * X) + 2 * c ^ 2 / U := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hden : 0 < q * U * X := mul_pos (mul_pos hqpos hU) hX
  have hexpand :
      ((q * (2 * U) + c * N) * (q * T + c * M)) /
          (q * U * X) =
        2 * q * T / X + 2 * c * M / X +
          c * N * T / (U * X) + c ^ 2 * N * M / (q * U * X) := by
    field_simp [hqpos.ne', hU.ne', hX.ne']
    ring
  rw [hexpand]
  have hDM : D * M ≤ 4 * X := by
    have hmul := mul_le_mul_of_nonneg_right hshortLower hM
    nlinarith [hproductUpper]
  have hsecond : 2 * c * M / X ≤ 8 * c / D := by
    apply (div_le_div_iff₀ hX hD).2
    have hcmul := mul_le_mul_of_nonneg_left hDM hc
    nlinarith
  have hthird : c * N * T / (U * X) ≤
      c * G * H₀ * T / (U * X) := by
    have hdenUX : 0 < U * X := mul_pos hU hX
    apply div_le_div_of_nonneg_right _ hdenUX.le
    have hbase : c * N ≤ c * G * H₀ := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hshortUpper hc
    exact mul_le_mul_of_nonneg_right hbase hT
  have hNMq : c ^ 2 * N * M ≤ 2 * c ^ 2 * q * X := by
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have hscaled := mul_le_mul_of_nonneg_left hproductUpper hc2
    have hqscale : 2 * c ^ 2 * X ≤ 2 * c ^ 2 * q * X := by
      have := mul_le_mul_of_nonneg_left hq (mul_nonneg (by positivity) hc2)
      nlinarith
    nlinarith
  have hfourth : c ^ 2 * N * M / (q * U * X) ≤ 2 * c ^ 2 / U := by
    apply (div_le_iff₀ hden).2
    field_simp [hU.ne']
    nlinarith [hNMq]
  linarith

end MRTProposition61TypeIINormalizedLedgerV3

#print axioms MRTProposition61TypeIINormalizedLedgerV3.normalized_typeII_product_le_four_terms
