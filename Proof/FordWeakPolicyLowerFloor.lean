import Mathlib
import FordWeakPolicyIntegerBridge

namespace MAPFordWeakPolicy
noncomputable section
set_option maxHeartbeats 1200000

/-- With the lower floor `k²/1000`, the exact j=2 recurrence still loses a
    fixed positive multiple of `k` at every step. -/
theorem policy_step_lower_floor
    {k Delta : ℝ} (hk : 2000 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 1000 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2) :
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    (1 / 2000 : ℝ) * k ≤ Delta - fordDeltaNext k Delta A := by
  dsimp
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  by_cases hhigh : k ^ 2 / 10 ≤ Delta
  · have hh := policy_high_contraction (hk := by linarith [hk]) hk0 hhigh hD1
    dsimp at hh
    have hh' := (le_div_iff₀ hk0).1 hh
    have hscale : ((7 : ℝ) * (Delta / k ^ 2) / 5) * k =
        7 * Delta / (5 * k) := by
      field_simp
    rw [hscale] at hh'
    have hhigh' : k / 10 ≤ Delta / k := by
      apply (le_div_iff₀ hk0).2
      field_simp
      nlinarith [hhigh]
    have hstep : (1 / 2000 : ℝ) * k ≤ 7 * Delta / (5 * k) := by
      apply (le_div_iff₀ (show 0 < 5 * k by positivity)).2
      field_simp [ne_of_gt hk0]
      nlinarith [hhigh]
    linarith
  · have hlow : Delta ≤ k ^ 2 / 10 := le_of_not_ge hhigh
    have hylo : 1 ≤ Delta / k - 1 := by
      have hk1000 : 2 ≤ k / 1000 := by nlinarith [hk]
      have hDk : k / 1000 ≤ Delta / k := by
        apply (le_div_iff₀ hk0).2
        nlinarith [hD0]
      nlinarith
    have hy0 : 0 ≤ Delta / k - 1 := by linarith
    have hceillo : Delta / k - 1 ≤ (Nat.ceil (Delta / k - 1) : ℝ) :=
      Nat.le_ceil _
    have hceilhi : (Nat.ceil (Delta / k - 1) : ℝ) < Delta / k := by
      have h := Nat.ceil_lt_add_one hy0
      linarith
    have hDkhi : Delta / k ≤ (k - 1) / 2 := by
      apply (div_le_iff₀ hk0).2
      nlinarith [hD1]
    have hA1 : 1 ≤ A := by dsimp [A]; exact le_max_left _ _
    have hAupper : A ≤ Delta / k := by
      dsimp [A]
      apply max_le
      · have hDk : k / 1000 ≤ Delta / k := by
          apply (le_div_iff₀ hk0).2
          nlinarith [hD0]
        nlinarith [hk, hDk]
      · exact le_of_lt hceilhi
    have hAlower : Delta / k - 1 ≤ A := by
      dsimp [A]
      exact le_trans hceillo (le_max_right _ _)
    have hAhalf : A ≤ k / 2 := by
      dsimp [A]
      apply max_le
      · nlinarith [hk]
      · exact (le_trans (le_of_lt hceilhi) (by nlinarith [hDkhi]))
    have hR4 : 0 < k - A := by nlinarith [hAhalf, hk]
    let x : ℝ := Delta / k ^ 2
    let z : ℝ := A / k
    let t : ℝ := 1 / k
    let u : ℝ := 1 - z
    let b : ℝ := x - z ^ 2 / 2 - t * (z / 2 + 1)
    have hx0 : (1 / 1000 : ℝ) ≤ x := by
      dsimp [x]
      apply (le_div_iff₀ (sq_pos_of_pos hk0)).2
      nlinarith [hD0]
    have hx1 : x ≤ (1 / 10 : ℝ) := by
      dsimp [x]
      apply (div_le_iff₀ (sq_pos_of_pos hk0)).2
      nlinarith [hlow]
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    have ht1 : t ≤ (1 / 2000 : ℝ) := by
      dsimp [t]
      apply (div_le_iff₀ hk0).2
      nlinarith [hk]
    have hz0 : 0 ≤ z := by dsimp [z]; positivity
    have hzx : z ≤ x := by
      dsimp [z, x]
      calc
        A / k ≤ (Delta / k) / k := (div_le_div_iff_of_pos_right hk0).2 hAupper
        _ = Delta / k ^ 2 := by field_simp
    have hz1 : z ≤ (1 / 10 : ℝ) := hzx.trans hx1
    have hu0 : (9 / 10 : ℝ) ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 := by dsimp [u]; linarith
    have hb0 : 0 ≤ b := by
      have hzsq : z ^ 2 ≤ x / 10 := by
        have hmul : 0 ≤ z * ((1 / 10 : ℝ) - z) :=
          mul_nonneg hz0 (sub_nonneg.mpr hz1)
        nlinarith [hmul, hzx]
      have htz : t * (z / 2 + 1) ≤ (21 : ℝ) / 40000 := by
        have hzfac : z / 2 + 1 ≤ (21 / 20 : ℝ) := by nlinarith [hz1]
        calc
          t * (z / 2 + 1) ≤ (1 / 2000 : ℝ) * (z / 2 + 1) :=
            mul_le_mul_of_nonneg_right ht1 (by positivity)
          _ ≤ (1 / 2000 : ℝ) * (21 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_left hzfac (by positivity)
          _ = (21 : ℝ) / 40000 := by norm_num
      dsimp [b]
      nlinarith [hx0, hzsq, htz]
    have hb1 : b ≤ (1 / 10 : ℝ) := by
      dsimp [b]
      nlinarith [hx1]
    have hub : 0 ≤ u - b := by nlinarith [hu0, hb1]
    have hdef :
        0 ≤ b * (3 * u - b) + t ^ 2 * (u - b) - u ^ 2 / 1000 := by
      have hfactor : (13 / 5 : ℝ) ≤ 3 * u - b := by
        nlinarith [hu0, hb1]
      have hprod : (13 / 5 : ℝ) * b ≤ b * (3 * u - b) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hfactor hb0
      have hblow : (17 / 40000 : ℝ) ≤ b := by
        have hzsq : z ^ 2 ≤ x / 10 := by
          have hmul : 0 ≤ z * ((1 / 10 : ℝ) - z) :=
            mul_nonneg hz0 (sub_nonneg.mpr hz1)
          nlinarith [hmul, hzx]
        have htz : t * (z / 2 + 1) ≤ (21 : ℝ) / 40000 := by
          have hzfac : z / 2 + 1 ≤ (21 / 20 : ℝ) := by nlinarith [hz1]
          calc
            t * (z / 2 + 1) ≤ (1 / 2000 : ℝ) * (z / 2 + 1) :=
              mul_le_mul_of_nonneg_right ht1 (by positivity)
            _ ≤ (1 / 2000 : ℝ) * (21 / 20 : ℝ) :=
              mul_le_mul_of_nonneg_left hzfac (by positivity)
            _ = (21 : ℝ) / 40000 := by norm_num
        dsimp [b]
        nlinarith [hx0, hzsq, htz]
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      have hterm : 0 ≤ t ^ 2 * (u - b) := mul_nonneg ht2 hub
      nlinarith [hprod, hblow, hterm, hu1]
    have hID := ford_j2_normalized_identity (k := k) (Delta := Delta) (A := A)
      hk0 hR4
    have hnorm :
        (Delta - fordDeltaNext k Delta A) / k =
          1 - (u - b) * (2 * u - b - t ^ 2) / (2 * u ^ 2) := by
      calc
        (Delta - fordDeltaNext k Delta A) / k =
            1 - (1 - A / k + (A / k) ^ 2 / 2 - Delta / k ^ 2 +
              (1 / k) * ((A / k) / 2 + 1)) *
              (1 - A / k + (1 - A / k + (A / k) ^ 2 / 2 - Delta / k ^ 2 +
                (1 / k) * ((A / k) / 2 + 1)) - (1 / k) ^ 2) /
              (2 * (1 - A / k) ^ 2) := hID
        _ = 1 - (u - b) * (2 * u - b - t ^ 2) / (2 * u ^ 2) := by
          dsimp [u, b, x, z, t]
          ring
    have hu_pos : 0 < u := by linarith [hu0]
    have hratio :
        (u - b) * (2 * u - b - t ^ 2) / (2 * u ^ 2) ≤
          1 - (1 / 2000 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * u ^ 2)).2
      have hprod :
          (u - b) * (2 * u - b - t ^ 2) ≤
            2 * u ^ 2 - u ^ 2 / 1000 := by
        have hEq :
            2 * u ^ 2 - (u - b) * (2 * u - b - t ^ 2) =
              b * (3 * u - b) + t ^ 2 * (u - b) := by ring
        nlinarith [hdef, hEq]
      nlinarith [hprod]
    have hbound : (1 / 2000 : ℝ) ≤
        1 - (u - b) * (2 * u - b - t ^ 2) / (2 * u ^ 2) := by
      linarith [hratio]
    have hstep : (1 / 2000 : ℝ) * k ≤ Delta - fordDeltaNext k Delta A := by
      rw [← hnorm] at hbound
      exact (le_div_iff₀ hk0).1 hbound
    exact hstep

end
end MAPFordWeakPolicy

#print axioms MAPFordWeakPolicy.policy_step_lower_floor
