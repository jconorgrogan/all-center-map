import FordWeakBilinear
import FordUniformEnvelope

open scoped BigOperators
noncomputable section
namespace FordCoarseDyadic

/-- A quantitative polynomial-versus-exponential bound sufficient to use q=N. -/
theorem nat_power_lt_two_pow {N p : ℕ} (hp : 1 ≤ p) (hN : 64 * p ^ 2 ≤ N) :
    N ^ p < 2 ^ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by nlinarith)
  have hppos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hNR : 64 * (p : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsqr := Real.sq_sqrt hNpos.le
  have hsq : (8 * (p : ℝ)) ^ 2 ≤ (Real.sqrt (N : ℝ)) ^ 2 := by nlinarith
  have hroot : 8 * (p : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsq
  have hlog := Real.log_le_sub_one_of_pos hsqrtpos
  rw [Real.log_sqrt hNpos.le] at hlog
  have hlogN : Real.log (N : ℝ) < 2 * Real.sqrt (N : ℝ) := by linarith
  have hquarter : 2 * (p : ℝ) * Real.sqrt (N : ℝ) ≤ (N : ℝ) / 4 := by
    have hm := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (N : ℝ))
    nlinarith
  have hlogtwo : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpower : (p : ℝ) * Real.log (N : ℝ) < (N : ℝ) * Real.log 2 := by
    have hpbound := mul_lt_mul_of_pos_left hlogN hppos
    nlinarith
  have hpow : (N : ℝ) ^ p < (2 : ℝ) ^ N := by
    apply (Real.log_lt_log_iff (pow_pos hNpos _) (by positivity)).mp
    simpa only [Real.log_pow] using hlogpower
  exact_mod_cast hpow

/-- The literal frequency width lies below 2^N with a polynomial size threshold. -/
theorem frequency_lt_two_pow {N r M k j : ℕ}
    (hN : 64 * (k + 1) ^ 2 ≤ N) (hr : r ≤ N) (hM : M ≤ N) (hj : j ≤ k) :
    r * M ^ j < 2 ^ N := by
  have hNpos : 0 < N := by nlinarith
  calc
    r * M ^ j ≤ N * N ^ j := Nat.mul_le_mul hr (Nat.pow_le_pow_left hM j)
    _ ≤ N * N ^ k := Nat.mul_le_mul_left N (Nat.pow_le_pow_right hNpos hj)
    _ = N ^ (k + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _
    _ < 2 ^ N := nat_power_lt_two_pow (by omega) hN

/-- q_j=N is legal at every coordinate for the proved fixed moment order. -/
theorem fixed_order_frequency_lt {N M k : ℕ}
    (hN : 1024 * (k + 1) ^ 2 ≤ N) (hM : M ≤ N) (j : Fin k) :
    FordWeakBilinear.order k * M ^ (j.val + 1) < 2 ^ N := by
  apply frequency_lt_two_pow (k := k)
  · nlinarith
  · unfold FordWeakBilinear.order
    have hh : k ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  · exact hM
  · omega

/-- The cost of the coarse dyadic choice is retained explicitly as 3^k*N^k. -/
theorem dyadic_cost_le (k N : ℕ) (hN : 1 ≤ N) :
    (∏ _j : Fin k, (2 * (N : ℝ) + 1)) ≤ (3 : ℝ) ^ k * (N : ℝ) ^ k := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ = (2 * (N : ℝ) + 1) ^ k := by simp
    _ ≤ (3 * (N : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    _ = _ := by rw [mul_pow]

/-- The N^k cost leaves a uniform quadratic saving on the already proved slab. -/
theorem raw_saving_after_coarse_cost {K : ℕ} {lam : ℝ} (hK : 2000 ≤ K)
    (hlow : FordWEnvelopeScalar.b * (K : ℝ) ≤ lam)
    (hupp : lam ≤ FordWEnvelopeScalar.b * (K : ℝ) + 1) :
    (K : ℝ) ^ 2 / 100 ≤ FordUniformEnvelope.rawSaving K lam - (K : ℝ) := by
  have hs := FordUniformEnvelope.raw_saving_ge_target hK hlow hupp
  have hKR : (2000 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith

end FordCoarseDyadic
#print axioms FordCoarseDyadic.nat_power_lt_two_pow
#print axioms FordCoarseDyadic.fixed_order_frequency_lt
#print axioms FordCoarseDyadic.dyadic_cost_le
#print axioms FordCoarseDyadic.raw_saving_after_coarse_cost
