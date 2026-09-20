import FordCompleteMomentLiftBound
import FordSmallPowerAbsorption

noncomputable section
set_option autoImplicit false
namespace FordJ2SmallUniform
open MAPFordCompleteSystemMoment FordJ2GeometricAlgebra

/-- Actual small-P moment step: the only count input is the prior J bound. -/
theorem small_uniform_bound {s k P : ℕ} {Delta DeltaNext C : ℝ}
    (hP : 1 ≤ P) (hsmall : P ≤ 2 ^ (100 * k ^ 4))
    (hC : 0 ≤ C) (hdrop : Delta - DeltaNext ≤ (k : ℝ))
    (hJ : (completeMoment s k P : ℝ) ≤
      C * (P : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :
    (completeMoment (s + k) k P : ℝ) ≤
      (2 : ℝ) ^ (8192 * k ^ 5) * C *
        (P : ℝ) ^ lambda ((s + k : ℕ) : ℝ) (k : ℝ) DeltaNext := by
  have hlift : (completeMoment (s + k) k P : ℝ) ≤
      (P : ℝ) ^ (2 * k) * (completeMoment s k P : ℝ) := by
    exact_mod_cast FordCompleteMomentLiftBound.completeMoment_lift
      (s := s) (t := k) (k := k) hP
  exact FordSmallPowerAbsorption.small_power_absorb
    (s := s) (k := k) (P := (P : ℝ)) (by exact_mod_cast hP)
    hC (by exact_mod_cast hsmall) hdrop hlift hJ
/-- Increasing the moment order while leaving the deficit unchanged. -/
theorem unchanged_deficit_lift {s k P : ℕ} {Delta C : ℝ}
    (hP : 1 ≤ P)
    (hJ : (completeMoment s k P : ℝ) ≤
      C * (P : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :
    (completeMoment (s + k) k P : ℝ) ≤
      C * (P : ℝ) ^ lambda ((s + k : ℕ) : ℝ) (k : ℝ) Delta := by
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hlift : (completeMoment (s + k) k P : ℝ) ≤
      (P : ℝ) ^ (2 * k) * (completeMoment s k P : ℝ) := by
    exact_mod_cast FordCompleteMomentLiftBound.completeMoment_lift
      (s := s) (t := k) (k := k) hP
  have hexp : ((2 * k : ℕ) : ℝ) + lambda (s : ℝ) (k : ℝ) Delta =
      lambda ((s + k : ℕ) : ℝ) (k : ℝ) Delta := by
    simp only [lambda, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  calc
    (completeMoment (s + k) k P : ℝ) ≤
        (P : ℝ) ^ (2 * k) * (C * (P : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :=
      hlift.trans (mul_le_mul_of_nonneg_left hJ (by positivity))
    _ = C * ((P : ℝ) ^ ((2 * k : ℕ) : ℝ) *
        (P : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) := by rw [Real.rpow_natCast]; ring
    _ = _ := by rw [← Real.rpow_add hPpos, hexp]
end FordJ2SmallUniform
#print axioms FordJ2SmallUniform.small_uniform_bound

#print axioms FordJ2SmallUniform.unchanged_deficit_lift
