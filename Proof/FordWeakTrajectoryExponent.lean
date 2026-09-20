import Mathlib
import FordWeakPolicyLowerTrajectory
import FordWeakLowerPolicyNatBridge
import FordJ2GeometricAlgebra

open MAPFordWeakPolicy

namespace FordWeakTrajectoryExponent
noncomputable section
set_option maxHeartbeats 900000

/-- Every lower-floor trajectory value is bounded below by the initial value
    minus at most `k` per previous update.  The inactive branch is constant,
    while the active branch uses the natural-policy `DeltaNext` drop bound. -/
theorem policyTrajectoryLower_delta_lower_bound
    {kNat : ℕ} (hkNat : 2000 ≤ kNat) (n : ℕ) :
    ((kNat : ℝ) ^ 2 - (kNat : ℝ)) / 2 -
        (n : ℝ) * (kNat : ℝ) ≤
      MAPFordWeakPolicy.policyTrajectoryLower (kNat : ℝ) n := by
  induction n with
  | zero =>
      simp [MAPFordWeakPolicy.policyTrajectoryLower_zero]
  | succ n ih =>
      have hk0 : 0 < (kNat : ℝ) := by positivity
      have hkReal : (2000 : ℝ) ≤ (kNat : ℝ) := by
        exact_mod_cast hkNat
      have hupper := MAPFordWeakPolicy.policyTrajectoryLower_upper
        hkReal hk0 n
      let Dn : ℝ := MAPFordWeakPolicy.policyTrajectoryLower (kNat : ℝ) n
      have hupperDn : Dn ≤ ((kNat : ℝ) ^ 2 - (kNat : ℝ)) / 2 := by
        dsimp [Dn]
        exact hupper
      rw [show MAPFordWeakPolicy.policyTrajectoryLower (kNat : ℝ) (n + 1) =
          (if (kNat : ℝ) ^ 2 / 1000 ≤ Dn then
            MAPFordWeakPolicy.fordDeltaNext (kNat : ℝ) Dn
              (max 1 (Nat.ceil (Dn / (kNat : ℝ) - 1) : ℝ))
          else Dn) by
            dsimp [Dn]
            rfl]
      split
      · rename_i hactive
        have hdrop := FordWeakLowerNat.lower_policy_deltaNext_drop_le
          (kNat := kNat) (Delta := Dn) hkNat hactive hupperDn
        have hdrop0 : Dn -
            MAPFordWeakPolicy.fordDeltaNext (kNat : ℝ) Dn
              (max 1 (Nat.ceil (Dn / (kNat : ℝ) - 1) : ℝ)) ≤
              (kNat : ℝ) := by
          simpa [FordWeakLowerNat.lowerPolicyA] using hdrop
        have hdrop' :
            MAPFordWeakPolicy.fordDeltaNext (kNat : ℝ) Dn
                (max 1 (Nat.ceil (Dn / (kNat : ℝ) - 1) : ℝ)) ≥
              Dn - (kNat : ℝ) := by
          linarith
        have ihDn : ((kNat : ℝ) ^ 2 - (kNat : ℝ)) / 2 -
            (n : ℝ) * (kNat : ℝ) ≤ Dn := by
          simpa [Dn] using ih
        have hnsucc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
        rw [hnsucc]
        nlinarith [ihDn, hdrop']
      · rename_i hactive
        have ihDn : ((kNat : ℝ) ^ 2 - (kNat : ℝ)) / 2 -
            (n : ℝ) * (kNat : ℝ) ≤ Dn := by
          simpa [Dn] using ih
        have hnsucc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
        rw [hnsucc]
        nlinarith [ihDn, hk0]


/-- Along the lower-floor trajectory, the Ford exponent at the lifted moment
    index stays nonnegative, with the explicit lower bound `s`. -/
theorem policyTrajectoryLower_lambda_bound
    {kNat : ℕ} (hkNat : 2000 ≤ kNat) (n : ℕ) :
    0 ≤ (kNat : ℝ) + (n : ℝ) * (kNat : ℝ) ∧
      (kNat : ℝ) + (n : ℝ) * (kNat : ℝ) ≤
        FordJ2GeometricAlgebra.lambda
          ((kNat : ℝ) + (n : ℝ) * (kNat : ℝ))
          (kNat : ℝ)
          (MAPFordWeakPolicy.policyTrajectoryLower (kNat : ℝ) n) := by
  have hk0 : 0 < (kNat : ℝ) := by positivity
  have hDelta := policyTrajectoryLower_delta_lower_bound hkNat n
  constructor
  · positivity
  · unfold FordJ2GeometricAlgebra.lambda
    nlinarith [hDelta]

end
end FordWeakTrajectoryExponent

#print axioms FordWeakTrajectoryExponent.policyTrajectoryLower_delta_lower_bound
#print axioms FordWeakTrajectoryExponent.policyTrajectoryLower_lambda_bound
