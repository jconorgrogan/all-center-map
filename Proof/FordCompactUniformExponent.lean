import FordCompactDifferenceScales

noncomputable section
namespace FordCompactUniformExponent
open FordCompactDifferenceScales

def degreeDecay (r : ℕ) : ℝ := 1 / (4 * (r : ℝ) * (2 : ℝ)^r)
def uniformDecay : ℝ := 1 / (4 * (1299 : ℝ) * (2 : ℝ)^1299)

theorem uniformDecay_pos : 0 < uniformDecay := by
  unfold uniformDecay
  positivity

theorem uniform_le_degree {r : ℕ} (hr : 1 ≤ r) (hrmax : r ≤ 1299) :
    uniformDecay ≤ degreeDecay r := by
  unfold uniformDecay degreeDecay
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hpow : (2 : ℝ)^r ≤ (2 : ℝ)^1299 := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hrmax)
  have hden : 4 * (r : ℝ) * (2 : ℝ)^r ≤
      4 * (1299 : ℝ) * (2 : ℝ)^1299 := by
    have hmul := mul_le_mul (show (r : ℝ) ≤ 1299 by exact_mod_cast hrmax)
      hpow (by positivity) (by positivity)
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) hden

theorem cutoff_div_pow_eq_degree {r : ℕ} (hr : 1 ≤ r) :
    cutoffExponent r / ((2^r : ℕ) : ℝ) = degreeDecay r := by
  unfold cutoffExponent degreeDecay
  norm_num [Nat.cast_pow]
  field_simp

theorem uniform_power_bound {N : ℝ} {r : ℕ}
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hrmax : r ≤ 1299) :
    N ^ (-degreeDecay r) ≤ N ^ (-uniformDecay) := by
  have hdec := uniform_le_degree hr hrmax
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  simp only [Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  nlinarith

end FordCompactUniformExponent
#print axioms FordCompactUniformExponent.uniform_power_bound
