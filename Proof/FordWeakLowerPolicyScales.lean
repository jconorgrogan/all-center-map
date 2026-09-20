import Mathlib
import FordWeakPolicyIntegerBridge

open MAPFordWeakPolicy

namespace FordWeakLowerPolicyScales
noncomputable section
set_option maxHeartbeats 1200000

theorem lower_policy_scales
    {k Delta : ℝ} (hk : 2000 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 1000 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2) :
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    let r : ℝ := k - A
    let a1 : ℝ := fordPhi1 k Delta A
    let a2 : ℝ := 1 / r
    1 ≤ A ∧ A ≤ k / 2 ∧ 4 ≤ r ∧ r < k ∧
      1 / (k + 1) ≤ a1 ∧ 1 / (k + 1) ≤ a2 ∧
      a1 + 2 * a2 ≤ (9 / 10 : ℝ) := by
  dsimp
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  let r : ℝ := k - A
  let a1 : ℝ := fordPhi1 k Delta A
  let a2 : ℝ := 1 / r
  have hy0 : 0 ≤ Delta / k - 1 := by
    have hDk : k / 1000 ≤ Delta / k := by
      apply (le_div_iff₀ hk0).2
      nlinarith [hD0]
    nlinarith [hk, hDk]
  have hceillo : Delta / k - 1 ≤ (Nat.ceil (Delta / k - 1) : ℝ) :=
    Nat.le_ceil _
  have hceilhi : (Nat.ceil (Delta / k - 1) : ℝ) < Delta / k := by
    have hh := Nat.ceil_lt_add_one hy0
    linarith
  have hDkhi : Delta / k ≤ (k - 1) / 2 := by
    apply (div_le_iff₀ hk0).2
    nlinarith [hD1]
  have hA1 : 1 ≤ A := by
    dsimp [A]
    exact le_max_left _ _
  have hAupper : A ≤ Delta / k := by
    dsimp [A]
    apply max_le
    · nlinarith [hk, hDkhi]
    · exact le_of_lt hceilhi
  have hAlower : Delta / k - 1 ≤ A := by
    dsimp [A]
    exact le_trans hceillo (le_max_right _ _)
  have hDupperA : Delta ≤ k * (A + 1) := by
    have hh : Delta / k ≤ A + 1 := by linarith [hAlower]
    simpa [mul_comm] using (div_le_iff₀ hk0).mp hh
  have hAhalf : A ≤ k / 2 := by
    dsimp [A]
    apply max_le
    · nlinarith [hk]
    · exact (le_trans (le_of_lt hceilhi) (by nlinarith [hDkhi]))
  have hr4 : 4 ≤ r := by
    dsimp [r]
    nlinarith [hAhalf, hk]
  have hrk : r < k := by
    dsimp [r]
    nlinarith [hA1]
  have hrpos : 0 < r := by linarith [hr4]
  have hrne : k - A ≠ 0 := by linarith [hrpos]
  have hr2ne : (k - A) ^ 2 ≠ 0 := pow_ne_zero _ hrne
  have ha2lo : 1 / (k + 1) ≤ a2 := by
    dsimp [a2]
    apply (div_le_div_iff₀ (by linarith) hrpos).2
    nlinarith [hrk]
  have ha1lo : 1 / (k + 1) ≤ a1 := by
    dsimp [a1, fordPhi1]
    have hN : 0 ≤ k ^ 2 + k + (k - A) ^ 2 - (k - A) +
        2 * (k - 1) - 2 * Delta := by
      nlinarith [hD1, sq_nonneg (k - A)]
    have hden : 0 < 4 * k * (k - A) ^ 2 := by positivity
    have hrewrite :
        1 / (2 * (k - A)) +
            (k ^ 2 + k + (k - A) ^ 2 - (k - A) + 2 * (k - 1) - 2 * Delta) /
              (4 * k * (k - A) ^ 2) =
          (2 * k * (k - A) +
            (k ^ 2 + k + (k - A) ^ 2 - (k - A) + 2 * (k - 1) - 2 * Delta)) /
            (4 * k * (k - A) ^ 2) := by
      field_simp [ne_of_gt hk0, hrne, hr2ne]
      ring
    rw [hrewrite]
    apply (le_div_iff₀ hden).2
    field_simp [ne_of_gt (show 0 < k + 1 by positivity)]
    have hNlow :
        -k ^ 2 + 2 * k * (k - A) + (k - A) ^ 2 - (k - A) - 2 ≤
          k ^ 2 + k + (k - A) ^ 2 - (k - A) + 2 * (k - 1) - 2 * Delta := by
      nlinarith [hDupperA]
    have hmulN := mul_le_mul_of_nonneg_left hNlow (by positivity : 0 ≤ k + 1)
    have hAsq : A ^ 2 ≤ (k / 2) * A := by
      simpa [pow_two] using
        (mul_le_mul_of_nonneg_right hAhalf (by positivity : 0 ≤ A))
    have hAsqk := mul_le_mul_of_nonneg_right hAsq (by positivity : 0 ≤ 3 * k)
    nlinarith [hmulN, hAsqk, hD1, hN, hA1, hAhalf, sq_nonneg (k - A)]
  have ha1gap : a1 + 2 * a2 ≤ (9 / 10 : ℝ) := by
    dsimp [a1, a2, fordPhi1]
    have hNup : k ^ 2 + k + (k - A) ^ 2 - (k - A) +
        2 * (k - 1) - 2 * Delta ≤ 2 * k ^ 2 + 4 * k := by
      nlinarith [hD0, hA1, hAhalf, sq_nonneg (k - A)]
    have hrlo : k / 2 ≤ k - A := by nlinarith [hAhalf]
    have hfirst : 1 / (2 * (k - A)) ≤ 1 / k := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hrlo, hk0]
    have hsecond :
        (k ^ 2 + k + (k - A) ^ 2 - (k - A) + 2 * (k - 1) - 2 * Delta) /
            (4 * k * (k - A) ^ 2) ≤ 4 / k := by
      apply (div_le_iff₀ (show 0 < 4 * k * (k - A) ^ 2 by positivity)).2
      have hr2 : 4 * k ^ 2 ≤ 16 * (k - A) ^ 2 := by
        nlinarith [sq_nonneg (2 * (k - A) - k)]
      field_simp [ne_of_gt hk0]
      nlinarith [hNup, hr2, hk0]
    have htwo : 2 * (1 / (k - A)) ≤ 4 / k := by
      rw [show 2 * (1 / (k - A)) = 2 / (k - A) by ring]
      apply (div_le_iff₀ hrpos).2
      field_simp [ne_of_gt hk0]
      nlinarith [hrlo, hk0]
    have hsmall : 1 / k + 4 / k + 4 / k ≤ (9 / 10 : ℝ) := by
      have hsmall' : (9 : ℝ) / k ≤ 9 / 10 := by
        apply (div_le_iff₀ hk0).2
        nlinarith [hk]
      convert hsmall' using 1 <;> ring
    nlinarith [hfirst, hsecond, htwo, hsmall]
  change 1 ≤ A ∧ A ≤ k / 2 ∧ 4 ≤ r ∧ r < k ∧
      1 / (k + 1) ≤ a1 ∧ 1 / (k + 1) ≤ a2 ∧
      a1 + 2 * a2 ≤ (9 / 10 : ℝ)
  exact ⟨hA1, hAhalf, hr4, hrk, ha1lo, ha2lo, ha1gap⟩

end
end FordWeakLowerPolicyScales

#print axioms FordWeakLowerPolicyScales.lower_policy_scales
