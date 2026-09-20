import FordJ2PolicyUniform
import FordJ2SmallUniform
import FordWeakTrajectoryExponent
import FordInitialMomentSeed
import FordWeakTotalCoefficient

noncomputable section
set_option autoImplicit false
namespace FordWeakTrajectoryMoment
open MAPFordWeakPolicy MAPFordCompleteSystemMoment FordJ2GeometricAlgebra

def trajectoryCoefficient (k n : ℕ) : ℝ :=
  (k.factorial : ℝ) * (2 : ℝ) ^ (n * (8192 * k ^ 5))

lemma coefficient_step (k n : ℕ) : trajectoryCoefficient k (n + 1) =
    (2 : ℝ) ^ (8192 * k ^ 5) * trajectoryCoefficient k n := by
  dsimp [trajectoryCoefficient]
  rw [Nat.add_mul, one_mul, pow_add]
  ring

lemma coefficient_nonneg (k n : ℕ) : 0 ≤ trajectoryCoefficient k n := by
  dsimp [trajectoryCoefficient]
  positivity

lemma coefficient_mono_step (k n : ℕ) :
    trajectoryCoefficient k n ≤ trajectoryCoefficient k (n + 1) := by
  rw [coefficient_step]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (8192 * k ^ 5) := one_le_pow₀ (by norm_num)
  simpa using mul_le_mul_of_nonneg_right h1 (coefficient_nonneg k n)

/-- Actual complete moments along every bounded lower-policy iterate. -/
theorem trajectory_moment_bound {k n : ℕ} (hk : 2000 ≤ k)
    (hn : n ≤ Nat.ceil (1001 * (k : ℝ)) + 1) :
    ∀ P : ℕ, 1 ≤ P →
      (completeMoment (k + n * k) k P : ℝ) ≤
        trajectoryCoefficient k n * (P : ℝ) ^
          lambda ((k + n * k : ℕ) : ℝ) (k : ℝ) (policyTrajectoryLower (k : ℝ) n) := by
  induction n with
  | zero =>
    intro P hP
    have hbase : (completeMoment k k P : ℝ) ≤ (k.factorial : ℝ) * (P : ℝ) ^ k := by
      exact_mod_cast MAPFordInitialMomentSeed.initialMoment_diagonal_bound k P
    have hexp : lambda (k : ℝ) (k : ℝ) (policyTrajectoryLower (k : ℝ) 0) = (k : ℝ) := by
      rw [policyTrajectoryLower_zero]
      dsimp [lambda]
      ring
    simpa [trajectoryCoefficient, hexp, Real.rpow_natCast] using hbase
  | succ n ih =>
    have hnn : n ≤ Nat.ceil (1001 * (k : ℝ)) + 1 := by omega
    have ihJ := ih hnn
    have hkR : (2000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hs1 : 1 ≤ k + n * k := by omega
    have hs : k + n * k ≤ 1003 * k ^ 2 := by
      have hh := policyTrajectoryLower_s_parameter_bound hkR hkpos hnn
      exact_mod_cast hh
    have hupper := policyTrajectoryLower_upper hkR hkpos n
    have hll := FordWeakTrajectoryExponent.policyTrajectoryLower_lambda_bound hk n
    have hlambda : 0 ≤ lambda ((k + n * k : ℕ) : ℝ) (k : ℝ)
        (policyTrajectoryLower (k : ℝ) n) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hll.1.trans hll.2
    have hsnext : k + (n + 1) * k = (k + n * k) + k := by ring
    intro P hP
    by_cases ha : (k : ℝ) ^ 2 / 1000 ≤ policyTrajectoryLower (k : ℝ) n
    · have hd : policyTrajectoryLower (k : ℝ) (n + 1) =
          fordDeltaNext (k : ℝ) (policyTrajectoryLower (k : ℝ) n)
            (max 1 (Nat.ceil (policyTrajectoryLower (k : ℝ) n / (k : ℝ) - 1) : ℝ)) := by
        change (if _ then _ else _) = _
        exact if_pos ha
      have hh := FordJ2PolicyUniform.policy_uniform_bound
        (s := k + n * k) (k := k) (P := P)
        (Delta := policyTrajectoryLower (k : ℝ) n) (C := trajectoryCoefficient k n)
        hk hs1 hs ha hupper hP (coefficient_nonneg k n) hlambda ihJ
      simpa only [hsnext, coefficient_step, hd] using hh
    · have hd : policyTrajectoryLower (k : ℝ) (n + 1) = policyTrajectoryLower (k : ℝ) n := by
        change (if _ then _ else _) = _
        exact if_neg ha
      have hh := FordJ2SmallUniform.unchanged_deficit_lift
        (s := k + n * k) (k := k) (P := P)
        (Delta := policyTrajectoryLower (k : ℝ) n) hP (ihJ P hP)
      rw [hsnext, hd]
      exact hh.trans (mul_le_mul_of_nonneg_right (coefficient_mono_step k n) (by positivity))
end FordWeakTrajectoryMoment
#print axioms FordWeakTrajectoryMoment.trajectory_moment_bound
