import Mathlib

noncomputable section
namespace FordPoweredDecay

theorem powered_decay {m : ℕ} {x C N eps : ℝ} (hm : 1 ≤ m)
    (hx : 0 ≤ x) (hC : 0 ≤ C) (hN : 0 < N)
    (hbound : x ^ m ≤ C ^ m * N ^ (-eps)) :
    x ≤ C * N ^ (-eps / (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hid : (N ^ (-eps / (m : ℝ))) ^ m = N ^ (-eps) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    field_simp
  apply (pow_le_pow_iff_left₀ hx (mul_nonneg hC (Real.rpow_nonneg hN.le _))
    (show m ≠ 0 by omega)).mp
  simpa only [mul_pow, hid] using hbound

/-- Absorb the final `17` before taking the iterated square root. -/
theorem decay_of_iteration {m : ℕ} {x N eps : ℝ} (hm : 1 ≤ m)
    (hx : 0 ≤ x) (hN : 0 < N)
    (hbound : x ^ m ≤ 16 ^ m * (17 * N ^ (-eps))) :
    x ≤ 272 * N ^ (-eps / (m : ℝ)) := by
  have h17 : (17 : ℝ) ≤ 17 ^ m := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 17) hm
  apply powered_decay hm hx (by norm_num) hN
  calc
    x ^ m ≤ 16 ^ m * (17 * N ^ (-eps)) := hbound
    _ ≤ 16 ^ m * (17 ^ m * N ^ (-eps)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h17 (Real.rpow_nonneg hN.le _)) (by positivity)
    _ = 272 ^ m * N ^ (-eps) := by rw [← mul_assoc, ← mul_pow]; norm_num

end FordPoweredDecay
#print axioms FordPoweredDecay.powered_decay
#print axioms FordPoweredDecay.decay_of_iteration
