import Mathlib

noncomputable section
namespace FordCompactIncrementScales

theorem upper_scale_identity {N lam q : ℝ} {r : ℕ} (hN : 0 < N)
    (hexp : lam + (r : ℝ) * q - (r + 1) = -(1 / 2)) :
    N ^ lam * (N ^ q) ^ r / N ^ (r + 1) = N ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_natCast N (r + 1)]
  rw [← Real.rpow_add hN, ← Real.rpow_sub hN]
  congr 1
  push_cast
  linarith

theorem lower_scale_identity {N lam q eps : ℝ} {r : ℕ} (hN : 0 < N)
    (hexp : lam + (r : ℝ) * (q - eps) - (r + 1) = -(3 / 4)) :
    N ^ lam * ((N ^ q / 2) * N ^ (-eps)) ^ r / (4 * N) ^ (r + 1) =
      1 / ((2 : ℝ) ^ r * 4 ^ (r + 1)) * N ^ (-(3 / 4 : ℝ)) := by
  have hi : (N ^ q / 2) * N ^ (-eps) = N ^ (q - eps) / 2 := by
    rw [div_mul_eq_mul_div, ← Real.rpow_add hN]
    congr 2
  have he : N ^ lam * (N ^ (q - eps)) ^ r / N ^ (r + 1) = N ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_natCast N (r + 1)]
    rw [← Real.rpow_add hN, ← Real.rpow_sub hN]
    congr 1
    push_cast
    linarith
  rw [hi, div_pow, mul_pow]
  rw [← he]
  ring

end FordCompactIncrementScales
#print axioms FordCompactIncrementScales.upper_scale_identity
#print axioms FordCompactIncrementScales.lower_scale_identity
