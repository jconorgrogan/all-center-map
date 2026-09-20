import GuthMaynardGMPointwiseHighTPartition

namespace GuthMaynardGMResonanceScalar
open GuthMaynardGMPointwiseHighTPartition

theorem bandLabels_card_le_eight_t_div_N {N : ℕ} {t : ℝ}
    (hN : 1 ≤ N) (hNt : (N : ℝ) ≤ t) :
    ((gmBandLabels N t).card : ℝ) ≤ 8 * t / N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ht : 0 ≤ t := by linarith
  have hx : 1 ≤ t / N := (le_div_iff₀ hNR).2 (by simpa using hNt)
  have hc := gmBandLabels_card_le hN ht
  have hcR : ((gmBandLabels N t).card : ℝ) ≤ 2 * (Nat.ceil (t / (N : ℝ) + 1) : ℝ) + 1 := by exact_mod_cast hc
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ t / (N : ℝ) + 1 by linarith)
  rw [show 8 * t / N = 8 * (t / N) by ring]
  linarith

theorem high_range_scalar {N t L K : ℝ}
    (hN : 0 < N) (hNt : N ≤ t) (htN : t ≤ N ^ 2)
    (hL : L ≤ 8 * t / N)
    (hK : K ≤ L * (1 + 18 * (Real.sqrt t / N) * N ^ 2 / t +
      3 * Real.pi / (Real.sqrt t / N))) : K ≤ 300 * Real.sqrt t := by
  have ht : 0 < t := lt_of_lt_of_le hN hNt
  have hu : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hu2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have huN : Real.sqrt t ≤ N := (Real.sqrt_le_left hN.le).2 htN
  have hfactor : 0 ≤ 1 + 18 * (Real.sqrt t / N) * N ^ 2 / t +
      3 * Real.pi / (Real.sqrt t / N) := by positivity
  have hh := hK.trans (mul_le_mul_of_nonneg_right hL hfactor)
  have heq : (8 * t / N) * (1 + 18 * (Real.sqrt t / N) * N ^ 2 / t +
      3 * Real.pi / (Real.sqrt t / N)) =
      8 * t / N + 144 * Real.sqrt t + 24 * Real.pi * Real.sqrt t := by
    field_simp
    linear_combination -24 * N * Real.pi * hu2
  rw [heq] at hh
  have hdiv : t / N ≤ Real.sqrt t := (div_le_iff₀ hN).2 (by nlinarith)
  rw [show 8 * t / N = 8 * (t / N) by ring] at hh
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hu.le
  linarith

end GuthMaynardGMResonanceScalar
#print axioms GuthMaynardGMResonanceScalar.high_range_scalar
