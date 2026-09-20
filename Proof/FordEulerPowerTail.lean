import Mathlib

open Set Interval intervalIntegral
open scoped BigOperators
noncomputable section
namespace FordEulerPowerTail

theorem sum_power_le {a sigma : ℝ} (ha : 0 < a) (hs : 0 < sigma) (K : ℕ) :
    (∑ n ∈ Finset.range K, (a + n) ^ (-sigma - 1)) ≤
      a ^ (-sigma - 1) + a ^ (-sigma) / sigma := by
  cases K with
  | zero => simp; positivity
  | succ K =>
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-sigma - 1)) (Icc a (a + K)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hsum := hanti.sum_le_integral
    have hz : (0 : ℝ) ∉ [[a, a + K]] := by
      rw [uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg K))]
      intro h
      linarith [h.1]
    have hi := integral_rpow (a := a) (b := a + K) (r := -sigma - 1)
      (Or.inr ⟨by linarith, hz⟩)
    have hb : (∫ x : ℝ in a..a + K, x ^ (-sigma - 1)) ≤ a ^ (-sigma) / sigma := by
      rw [hi]
      rw [show -sigma - 1 + 1 = -sigma by ring]
      have hp : 0 ≤ (a + K) ^ (-sigma) / sigma := by positivity
      calc
        ((a + K) ^ (-sigma) - a ^ (-sigma)) / (-sigma) =
            a ^ (-sigma) / sigma - (a + K) ^ (-sigma) / sigma := by ring
        _ ≤ a ^ (-sigma) / sigma := sub_le_self _ hp
    rw [Finset.sum_range_succ']
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, add_comm] using
      add_le_add_right (hsum.trans hb) (a ^ (-sigma - 1))

theorem summable_power {a sigma : ℝ} (ha : 0 < a) (hs : 0 < sigma) :
    Summable (fun n : ℕ => (a + n) ^ (-sigma - 1)) := by
  exact summable_of_sum_range_le (fun n => by positivity) (sum_power_le ha hs)

theorem tsum_power_le {a sigma : ℝ} (ha : 0 < a) (hs : 0 < sigma) :
    (∑' n : ℕ, (a + n) ^ (-sigma - 1)) ≤
      a ^ (-sigma - 1) + a ^ (-sigma) / sigma := by
  exact Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_power_le ha hs)

end FordEulerPowerTail
#print axioms FordEulerPowerTail.sum_power_le
#print axioms FordEulerPowerTail.summable_power
#print axioms FordEulerPowerTail.tsum_power_le
