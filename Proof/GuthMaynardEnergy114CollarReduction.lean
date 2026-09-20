import GuthMaynardS3LiteralLemma83Energy
import GuthMaynardLemma118IntervalPacking

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy114CollarReduction
open GuthMaynardS3LiteralLemma83Energy GuthMaynardLemma118

/-- The closed unit collar contains at most three one-separated points. -/
theorem unit_collar_card_le_three (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y|) (z : ℝ) :
    ((W.filter fun t => |z-t| ≤ 1).card : ℝ) ≤ 3 := by
  have hh := card_cast_le_one_add_div (W.filter fun t => |z-t| ≤ 1)
    (z-1) 2 1 (by norm_num) (by norm_num) (by
      intro t ht
      have ha := abs_le.mp (Finset.mem_filter.mp ht).2
      constructor <;> linarith) (by
      intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  norm_num at hh
  exact_mod_cast hh

/-- Literal source energy is the sum of the fourth-point collar multiplicities. -/
theorem energy_eq_sum_collar (W : Finset ℝ) :
    (sourceApproximateAdditiveEnergy W : ℝ) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        ((W.filter fun d => |a+b-c-d| ≤ 1).card : ℝ) := by
  simp only [sourceApproximateAdditiveEnergy, Finset.card_filter, Finset.product_eq_sprod,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_product, sub_add_eq_sub_sub]

/-- Deterministic part of the energy-to-third-moment argument. The local L2
estimate is an explicit input to this adapter; its analytic producer is kept
separate. No collar endpoints or fourth-point multiplicities are dropped. -/
theorem energy_le_local_cubic_average
    (W : Finset ℝ) (F : ℝ → ℂ) (H : ℝ → ℝ) {V C : ℝ}
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hH : ∀ t, 0 ≤ H t)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y|)
    (hlarge : ∀ t ∈ W, V ≤ ‖F t‖)
    (hlocal : ∀ u v : ℝ, |u-v| ≤ 1 → ‖F u‖^2 ≤ C*H v) :
    (sourceApproximateAdditiveEnergy W : ℝ)*V^2 ≤
      3*C*(∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, H (a+b-c)) := by
  have hpoint : ∀ a b c : ℝ,
      ((W.filter fun d => |a+b-c-d| ≤ 1).card : ℝ)*V^2 ≤ 3*C*H (a+b-c) := by
    intro a b c
    have hsum : (∑ d ∈ W.filter (fun d => |a+b-c-d| ≤ 1), V^2) ≤
        ∑ d ∈ W.filter (fun d => |a+b-c-d| ≤ 1), C*H (a+b-c) := by
      apply Finset.sum_le_sum
      intro d hd
      have hmem := Finset.mem_filter.mp hd
      have hval := pow_le_pow_left₀ hV (hlarge d hmem.1) 2
      have hdist : |d-(a+b-c)| ≤ 1 := by
        rw [abs_sub_comm]
        exact hmem.2
      exact hval.trans (hlocal d (a+b-c) hdist)
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcount := unit_collar_card_le_three W hsep (a+b-c)
    have hmul := mul_le_mul_of_nonneg_right hcount (mul_nonneg hC (hH (a+b-c)))
    exact hsum.trans (by simpa only [mul_assoc] using hmul)
  rw [energy_eq_sum_collar]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  apply Finset.sum_le_sum
  intro c hc
  exact hpoint a b c

end GuthMaynardEnergy114CollarReduction
#print axioms GuthMaynardEnergy114CollarReduction.unit_collar_card_le_three
#print axioms GuthMaynardEnergy114CollarReduction.energy_eq_sum_collar
#print axioms GuthMaynardEnergy114CollarReduction.energy_le_local_cubic_average
