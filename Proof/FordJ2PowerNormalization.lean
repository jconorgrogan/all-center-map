import FordJ2GeometricAlgebra
import FordDifferencingScalarAbsorption

noncomputable section
set_option autoImplicit false
namespace FordJ2PowerNormalization
open FordJ2GeometricAlgebra MAPFordWeakPolicy

theorem terminal_exponent_normalized {s k r Delta : ℝ}
    (hk : k ≠ 0) (hr : r ≠ 0) :
    k + (1 / r) * (eZero s k r - 1) +
      (1 - fordPhi1 k Delta (k - r) - 1 / r) * lambda s k Delta =
      (1 - fordPhi1 k Delta (k - r)) * lambda s k Delta +
        2 * (k * r * fordPhi1 k Delta (k - r)) := by
  have h := cancellation (s := s) (Delta := Delta) hk hr
  linear_combination 2 * h

theorem power_absorb {L F A J K C D P Z u v : ℝ}
    (hP : 0 < P) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hJ0 : 0 ≤ J) (hK0 : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hZ : 0 < Z) (hJ : J ≤ C * P ^ u)
    (hK : K ≤ D * C * P ^ (u + 2 * v)) (hdiv : P ^ v ≤ Z)
    (hL : L ≤ F * max (A * J) (2 / Z * Real.sqrt (J * K))) :
    L ≤ F * C * P ^ u * max A (2 * Real.sqrt D) := by
  have hp : P ^ (u + 2 * v) = P ^ u * (P ^ v) ^ (2 : ℕ) := by
    rw [Real.rpow_add hP, show 2 * v = v * 2 by ring,
      Real.rpow_mul hP.le, Real.rpow_two]
  have hK' : K ≤ D * C * (P ^ u) * (P ^ v) ^ (2 : ℕ) := by
    rw [hp] at hK
    simpa only [mul_assoc] using hK
  exact FordDifferencingScalarAbsorption.max_absorb hF hA hJ0 hK0 hC
    (Real.rpow_nonneg hP.le _) hD (Real.rpow_nonneg hP.le _) hZ hJ hK' hdiv hL

theorem divisor_power_lower {P a : ℝ} {p r k : ℕ}
    (hP : 0 < P) (hp : P ^ a ≤ (p : ℝ)) :
    P ^ ((k : ℝ) * (r : ℝ) * a) ≤ (p : ℝ) ^ (r * k) := by
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hP.le a) hp (r * k)
  have heq : P ^ ((k : ℝ) * (r : ℝ) * a) = (P ^ a) ^ (r * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
    congr 1
    push_cast
    ring
  rw [heq]
  exact hpow

end FordJ2PowerNormalization
#print axioms FordJ2PowerNormalization.terminal_exponent_normalized
#print axioms FordJ2PowerNormalization.power_absorb
#print axioms FordJ2PowerNormalization.divisor_power_lower
