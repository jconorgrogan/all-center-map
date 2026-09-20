import Mathlib

noncomputable section
namespace FordCompactMarginScalar

def margin (r N : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ r * 4 ^ (r + 1)) *
    (N : ℝ) ^ (-(3 / 4 : ℝ))

lemma margin_pos {r N : ℕ} (hN : 1 ≤ N) :
    0 < margin r N := by
  unfold margin
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  positivity

theorem margin_le_one {r N : ℕ} (hN : 1 ≤ N) :
    margin r N ≤ 1 := by
  unfold margin
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hc : (1 : ℝ) ≤ (2 : ℝ) ^ r * 4 ^ (r + 1) := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num)
    simpa using mul_le_mul h2 h4 (by positivity) (by positivity)
  have hc0 : 0 ≤ (N : ℝ) ^ (-(3 / 4 : ℝ)) :=
    (Real.rpow_nonneg (by exact_mod_cast (show 0 ≤ N by omega)) _)
  have hfrac :
      1 / ((2 : ℝ) ^ r * 4 ^ (r + 1)) ≤ 1 := by
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  exact (mul_le_mul hfrac hpow hc0 (by positivity)).trans_eq (by ring)

lemma coefficient_identity (r : ℕ) :
    (2 : ℝ) ^ r * 4 ^ (r + 1) = 4 * 8 ^ r := by
  calc
    (2 : ℝ) ^ r * 4 ^ (r + 1) =
        4 * ((2 : ℝ) ^ r * 4 ^ r) := by
          rw [pow_succ]
          ring
    _ = 4 * (2 * 4) ^ r := by rw [mul_pow]
    _ = 4 * 8 ^ r := by norm_num

theorem normalized_ratio {r N : ℕ} (hN : 0 < N) :
    (3 * Real.pi / margin r N) / (N : ℝ) =
      (12 * Real.pi * 8 ^ r) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hcoeff := coefficient_identity r
  have hrpow :
      (N : ℝ) ^ (3 / 4 : ℝ) / (N : ℝ) =
        (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hNr]
    norm_num
  have hneg : (N : ℝ) ^ (-(3 / 4 : ℝ)) =
      ((N : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hNr.le]
  unfold margin
  rw [hcoeff, hneg]
  field_simp [hNne]
  have hcombine : (N : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) =
      (N : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by norm_num
      _ = (N : ℝ) ^ ((1 : ℝ) + (-(1 / 4 : ℝ))) := by
        rw [← Real.rpow_add hNr]
      _ = (N : ℝ) ^ (3 / 4 : ℝ) := by norm_num
  rw [show (N : ℝ) * 12 * (N : ℝ) ^ (-(1 / 4 : ℝ)) =
      12 * ((N : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ))) by ring,
    hcombine]
  ring

theorem endpoint_upper_of_le_one {r N : ℕ} {U : ℝ}
    (hN : 1 ≤ N)
    (hupper : U ≤ 1) :
    U ≤ 2 * Real.pi - margin r N := by
  have hm := margin_le_one (r := r) hN
  have hpi : (1 : ℝ) < Real.pi := by nlinarith [Real.pi_gt_three]
  nlinarith

end FordCompactMarginScalar

#print axioms FordCompactMarginScalar.margin_le_one
#print axioms FordCompactMarginScalar.normalized_ratio
#print axioms FordCompactMarginScalar.endpoint_upper_of_le_one
