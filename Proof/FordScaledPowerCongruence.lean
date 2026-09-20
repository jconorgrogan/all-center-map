import FordP16SourceCountBridge

open scoped BigOperators
namespace MAPFordScaledPowerCongruence
open MAPFordP16FiniteFourierBridge

/-- The scaled power block vanishes at each literal mixed modulus. -/
theorem scaled_power_block_dvd {s k Q : ℕ} (p q r : ℕ)
    (u : Fin s → Fin (Q+1)) (j : Fin k) :
    (p : ℤ)^(min (j.val+1) r) ∣ fordQFrequencyAt (q := p*q) u j := by
  apply Finset.dvd_sum
  intro i hi
  unfold fordQScalarFrequency
  have hbase : (p : ℤ) ∣ ((p*q : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact dvd_mul_right _ _
  exact (pow_dvd_pow_of_dvd_of_le hbase (Nat.min_le_left _ _)).trans
    (dvd_mul_right _ _)

/-- Each exact total frequency determines the polynomial mixed target;
no invertibility of q, prime bound, or omitted low row is needed. -/
theorem source_modEq_total {s k P Q : ℕ} (p q r : ℕ)
    (psi : Fin k → Polynomial ℤ) (z : Fin k → Fin (P+1))
    (u : Fin s → Fin (Q+1)) (j : Fin k) :
    Int.ModEq ((p : ℤ)^(min (j.val+1) r))
      (fordSourceFrequencyAt psi z j)
      (fordSourceFrequencyAt psi z j + fordQFrequencyAt (q := p*q) u j) := by
  apply Int.modEq_iff_dvd.mpr
  simpa using scaled_power_block_dvd p q r u j

end MAPFordScaledPowerCongruence
#print axioms MAPFordScaledPowerCongruence.scaled_power_block_dvd
#print axioms MAPFordScaledPowerCongruence.source_modEq_total
