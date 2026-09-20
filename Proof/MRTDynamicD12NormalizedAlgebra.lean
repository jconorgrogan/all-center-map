import MRTDynamicD12PerBagLedger

namespace MRTDynamicD12NormalizedAlgebra
open scoped BigOperators
open Real
noncomputable section
set_option maxHeartbeats 900000

theorem normalized_d12_main_identity
    (D4 kappa Cm J q lambda U H X Q : ℝ) (delta : ℝ) (L : ℝ) (Em : ℕ)
    (hq : 0 < q) (hlambda : 0 < lambda) (hH : 0 < H)
    (hU : U = lambda * H) (hT : (2 * lambda * X * Real.sqrt Q) =
      2 * lambda * X * Real.sqrt Q) :
    D4 / (q * U ^ 2) *
        (2 * kappa ^ 2 * J ^ 2 *
          (Cm * (q * U + X ^ delta) * U *
            (q * (2 * lambda * X * Real.sqrt Q)) * L ^ Em)) =
      4 * kappa ^ 2 * Cm * J ^ 2 * D4 * X * Real.sqrt Q *
        (q * lambda + X ^ delta / H) * L ^ Em := by
  rw [hU]
  field_simp
  ring

theorem normalized_d12_error_bound_ordered
    (D4 kappa D q lambda U H X Q Delta P Bcoeff Y J : ℝ)
    (epsilon : ℝ)
    (hD4 : 0 ≤ D4) (hkappa : 0 ≤ kappa) (hD : 0 ≤ D)
    (hq : 0 < q) (hlambda : 0 < lambda) (hU : U = lambda * H)
    (hH : 0 < H) (hX : 0 < X) (hQ : 0 ≤ Q)
    (hDelta0 : 0 ≤ Delta) (hDelta : Delta ≤ lambda * X * Real.sqrt Q)
    (hJ : J ≤ q) (hJ0 : 0 ≤ J) (hB : Bcoeff ≤ D * X ^ epsilon)
    (hB0 : 0 ≤ Bcoeff) (hY : Y ≤ 2 * X) (hY0 : 0 ≤ Y)
    (hP : P = lambda * X ^ (23 / 24 : ℝ)) (hP0 : 0 < P)
    (hlog : 0 ≤ Real.log (2 + P)) :
    D4 / (q * U ^ 2) *
        (2 * kappa ^ 2 * Delta *
          (2 * U * J * Bcoeff * Real.sqrt Y *
            Real.log (2 + P) / P) ^ 2) ≤
      16 * D4 * kappa ^ 2 * D ^ 2 * q * Real.sqrt Q *
        (H / U) * Real.log (2 + P) ^ 2 *
          X ^ (1 / 12 + 2 * epsilon) := by
  have hinside0 : 0 ≤ 2 * U * J * Bcoeff * Real.sqrt Y *
      Real.log (2 + P) / P := by rw [hU]; positivity
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hXpow0 : 0 ≤ X ^ epsilon := Real.rpow_nonneg (le_of_lt hX) _
  have hinside_le : 2 * U * J * Bcoeff * Real.sqrt Y *
      Real.log (2 + P) / P ≤
      2 * U * q * (D * X ^ epsilon) * Real.sqrt (2 * X) *
        Real.log (2 + P) / P := by
    have hs : Real.sqrt Y ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hY
    gcongr
  have hsq := (sq_le_sq₀ hinside0 (by positivity)).2 hinside_le
  have hnorm : 0 ≤ D4 / (q * U ^ 2) * (2 * kappa ^ 2 * Delta) := by
    rw [hU]; positivity
  have hmain := mul_le_mul_of_nonneg_left hsq hnorm
  calc
    _ ≤ D4 / (q * U ^ 2) * (2 * kappa ^ 2 * Delta) *
        (2 * U * q * (D * X ^ epsilon) * Real.sqrt (2 * X) *
          Real.log (2 + P) / P) ^ 2 := by simpa [mul_assoc] using hmain
    _ ≤ D4 / (q * U ^ 2) * (2 * kappa ^ 2 *
        (lambda * X * Real.sqrt Q)) *
        (2 * U * q * (D * X ^ epsilon) * Real.sqrt (2 * X) *
          Real.log (2 + P) / P) ^ 2 := by gcongr
    _ = _ := by
      rw [hU, hP]
      have hsq2 : Real.sqrt (2 * X) ^ 2 = 2 * X := Real.sq_sqrt (by positivity)
      have hpowE : (X ^ epsilon) ^ 2 = X ^ (2 * epsilon) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        ring_nf
      have hpowP : (X ^ (23 / 24 : ℝ)) ^ 2 = X ^ (2 * (23 / 24 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        ring_nf
      field_simp [hP0.ne']
      rw [hsq2, hpowE, hpowP]
      have hxp : X ^ (2 : ℕ) * X ^ (epsilon * 2) =
          X ^ (23 / 12 : ℝ) * X ^ (1 / 12 + epsilon * 2) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
        congr 1 <;> ring
      ring_nf
      calc
        _ = D4 * kappa ^ 2 * Real.sqrt Q * D ^ 2 *
            Real.log (2 + lambda * X ^ (23 / 24 : ℝ)) ^ 2 * 16 *
            (X ^ (2 : ℕ) * X ^ (epsilon * 2)) := by
              simp only [mul_assoc, mul_left_comm, mul_comm]
        _ = D4 * kappa ^ 2 * Real.sqrt Q * D ^ 2 *
            Real.log (2 + lambda * X ^ (23 / 24 : ℝ)) ^ 2 * 16 *
            (X ^ (23 / 12 : ℝ) * X ^ (1 / 12 + epsilon * 2)) := by rw [hxp]
        _ = _ := by
          simp only [mul_assoc, mul_left_comm, mul_comm]


end
end MRTDynamicD12NormalizedAlgebra
