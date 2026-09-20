import FordScaleCancellation
import FordWeakCompleteMoment

open FordWEnvelopeScalar FordScaleCancellation FordWeakCompleteMoment

namespace FordBilinearNormalization
noncomputable section

theorem normalize_powers {R k : ℕ} {x y : ℝ} (hR : 1 ≤ R)
    (hx : 0 < x) (hy : 0 < y) :
    y ^ ((R - 1) * (2 * R)) *
        (x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
          y ^ weakExponent R k) =
      (x * y) ^ (R * (2 * R)) *
        (x ^ (eps * (k : ℝ) ^ 2) *
          y ^ (-deficit k)) := by
  have hRcast : (((R - 1) * (2 * R) : ℕ) : ℝ) =
      (R : ℝ) * (2 * (R : ℝ)) - 2 * (R : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hR]
    push_cast
    ring
  have hRpow : (((R * (2 * R) : ℕ) : ℝ)) =
      (R : ℝ) * (2 * (R : ℝ)) := by
    push_cast
    ring
  have hweak : weakExponent R k =
      2 * (R : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 +
        (k : ℝ) ^ 2 / 1000 := by rfl
  rw [← Real.rpow_natCast y ((R - 1) * (2 * R)),
    ← Real.rpow_natCast (x * y) (R * (2 * R)), hRcast, hRpow]
  rw [Real.mul_rpow (le_of_lt hx) (le_of_lt hy)]
  rw [hweak]
  calc
    y ^ ((R : ℝ) * (2 * (R : ℝ)) - 2 * (R : ℝ)) *
        (x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
          y ^ (2 * (R : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 +
            (k : ℝ) ^ 2 / 1000)) =
      x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
        (y ^ ((R : ℝ) * (2 * (R : ℝ)) - 2 * (R : ℝ)) *
          y ^ (2 * (R : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 +
            (k : ℝ) ^ 2 / 1000)) := by ring
    _ = x ^ (2 * (R : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
        y ^ ((R : ℝ) * (2 * (R : ℝ)) - 2 * (R : ℝ) +
          (2 * (R : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 +
            (k : ℝ) ^ 2 / 1000)) := by rw [← Real.rpow_add hy]
    _ = x ^ ((R : ℝ) * (2 * (R : ℝ))) *
      y ^ ((R : ℝ) * (2 * (R : ℝ))) *
        (x ^ (eps * (k : ℝ) ^ 2) * y ^ (-deficit k)) := by
      have hright :
          x ^ ((R : ℝ) * (2 * (R : ℝ))) *
              y ^ ((R : ℝ) * (2 * (R : ℝ))) *
              (x ^ (eps * (k : ℝ) ^ 2) * y ^ (-deficit k)) =
            x ^ ((R : ℝ) * (2 * (R : ℝ)) + eps * (k : ℝ) ^ 2) *
              y ^ ((R : ℝ) * (2 * (R : ℝ)) - deficit k) := by
        calc
          _ = (x ^ ((R : ℝ) * (2 * (R : ℝ))) *
                x ^ (eps * (k : ℝ) ^ 2)) *
              (y ^ ((R : ℝ) * (2 * (R : ℝ))) * y ^ (-deficit k)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hx, ← Real.rpow_add hy]
            congr 1 <;> ring
      rw [hright]
      congr 1
      · unfold eps
        ring
      · unfold deficit
        ring

end
end FordBilinearNormalization

#print axioms FordBilinearNormalization.normalize_powers
