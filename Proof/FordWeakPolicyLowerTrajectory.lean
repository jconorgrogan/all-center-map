import Mathlib
import FordWeakPolicyLowerFloor
import FordWeakLinearStopping

namespace MAPFordWeakPolicy
noncomputable section
set_option maxHeartbeats 1200000

/-- The lower-floor trajectory uses the exact ceiling policy until it crosses
    `k²/1000`, then remains stopped. -/
def policyTrajectoryLower (k : ℝ) : ℕ → ℝ :=
  Nat.rec ((k ^ 2 - k) / 2) (fun _ d =>
    if k ^ 2 / 1000 ≤ d then
      fordDeltaNext k d (max 1 (Nat.ceil (d / k - 1) : ℝ))
    else d)

theorem policyTrajectoryLower_zero (k : ℝ) :
    policyTrajectoryLower k 0 = (k ^ 2 - k) / 2 := by
  rfl

theorem policyTrajectoryLower_upper
    {k : ℝ} (hk : 2000 ≤ k) (hk0 : 0 < k) :
    ∀ n, policyTrajectoryLower k n ≤ (k ^ 2 - k) / 2 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change (if k ^ 2 / 1000 ≤ policyTrajectoryLower k n then
          fordDeltaNext k (policyTrajectoryLower k n)
            (max 1 (Nat.ceil (policyTrajectoryLower k n / k - 1) : ℝ))
        else policyTrajectoryLower k n) ≤ (k ^ 2 - k) / 2
      by_cases h : k ^ 2 / 1000 ≤ policyTrajectoryLower k n
      · rw [if_pos h]
        have hs := policy_step_lower_floor hk hk0 h ih
        nlinarith [hs, ih]
      · rw [if_neg h]
        exact ih

theorem policyTrajectoryLower_step
    {k : ℝ} (hk : 2000 ≤ k) (hk0 : 0 < k) (n : ℕ)
    (hfloor : k ^ 2 / 1000 ≤ policyTrajectoryLower k n) :
    policyTrajectoryLower k (n + 1) ≤
      policyTrajectoryLower k n - k / 2000 := by
  change (if k ^ 2 / 1000 ≤ policyTrajectoryLower k n then
      fordDeltaNext k (policyTrajectoryLower k n)
        (max 1 (Nat.ceil (policyTrajectoryLower k n / k - 1) : ℝ))
    else policyTrajectoryLower k n) ≤ policyTrajectoryLower k n - k / 2000
  rw [if_pos hfloor]
  have hs := policy_step_lower_floor hk hk0 hfloor
    (policyTrajectoryLower_upper hk hk0 n)
  nlinarith [hs]

theorem policyTrajectoryLower_stops
    {k : ℝ} (hk : 2000 ≤ k) (hk0 : 0 < k) :
    ∃ n ≤ Nat.ceil (1001 * k) + 1,
      policyTrajectoryLower k n < k ^ 2 / 1000 := by
  let N : ℕ := Nat.ceil (1001 * k) + 1
  apply finite_linear_stopping (D0 := (k ^ 2 - k) / 2)
    (floor := k ^ 2 / 1000) (c := k / 2000) (N := N)
  · rfl
  · positivity
  · intro n hn
    exact policyTrajectoryLower_step hk hk0 n hn
  · dsimp [N]
    have hceil : (1001 * k : ℝ) ≤ (Nat.ceil (1001 * k) : ℝ) :=
      Nat.le_ceil _
    norm_num at hceil ⊢
    nlinarith [hceil]

theorem policyTrajectoryLower_s_parameter_bound
    {k : ℝ} (hk : 2000 ≤ k) (hk0 : 0 < k) {n : ℕ}
    (hn : n ≤ Nat.ceil (1001 * k) + 1) :
    k + (n : ℝ) * k ≤ 1003 * k ^ 2 := by
  have hceil : (Nat.ceil (1001 * k) : ℝ) < 1001 * k + 1 := by
    apply Nat.ceil_lt_add_one
    positivity
  have hn' : (n : ℝ) ≤ (Nat.ceil (1001 * k) : ℝ) + 1 := by
    exact_mod_cast hn
  have hnb : (n : ℝ) + 1 ≤ 1001 * k + 3 := by
    nlinarith [hceil, hn']
  have hscale := mul_le_mul_of_nonneg_left hnb (le_of_lt hk0)
  nlinarith [hscale, hk]

end
end MAPFordWeakPolicy

#print axioms MAPFordWeakPolicy.policyTrajectoryLower_upper
#print axioms MAPFordWeakPolicy.policyTrajectoryLower_step
#print axioms MAPFordWeakPolicy.policyTrajectoryLower_stops
#print axioms MAPFordWeakPolicy.policyTrajectoryLower_s_parameter_bound
