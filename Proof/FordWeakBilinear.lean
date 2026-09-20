import FordBilinearFinite
import FordWeakCompleteMoment

open scoped BigOperators
noncomputable section
namespace FordWeakBilinear
open FordPolynomialPhase FordSubsetMoment FordWeakCompleteMoment

def order (k : ℕ) : ℕ := 1003 * k ^ 2

def capFactor (L K q : ℕ) (gamma : ℝ) : ℝ :=
  min (2 * (K : ℝ))
    (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
      6 * (K : ℝ) * |gamma| + (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|))

lemma degree_sum (k : ℕ) :
    (∑ j : Fin k, ((j.val + 1 : ℕ) : ℝ)) = (k : ℝ) * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

lemma kernel_product (r k M1 M2 s : ℕ) (hM1 : 1 ≤ M1)
    (q : Fin k → ℕ) (gamma : Fin k → ℝ) :
    (∏ j : Fin k, FordBilinearFinite.kernelFactor (r * M1 ^ (j.val + 1))
      (s * M2 ^ (j.val + 1)) (q j) (gamma j)) =
      (r : ℝ) ^ k * (M1 : ℝ) ^ ((k : ℝ) * (k + 1) / 2) *
        ∏ j : Fin k, capFactor (r * M1 ^ (j.val + 1))
          (s * M2 ^ (j.val + 1)) (q j) (gamma j) := by
  have hpos : 0 < (M1 : ℝ) := by exact_mod_cast (show 0 < M1 by omega)
  have hp : (∏ j : Fin k, (M1 : ℝ) ^ (j.val + 1)) =
      (M1 : ℝ) ^ ((k : ℝ) * (k + 1) / 2) := by
    simp_rw [← Real.rpow_natCast]
    rw [← Real.rpow_sum_of_pos hpos]
    rw [degree_sum]
  change (∏ j : Fin k, ((r * M1 ^ (j.val + 1) : ℕ) : ℝ) *
    capFactor (r * M1 ^ (j.val + 1)) (s * M2 ^ (j.val + 1)) (q j) (gamma j)) = _
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hp]
  simp

private lemma first_scale_exponent (r k M : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M) :
    (M : ℝ) ^ (r * (2 * r - 2)) * (M : ℝ) ^ weakExponent r k *
      (M : ℝ) ^ ((k : ℝ) * (k + 1) / 2) =
    (M : ℝ) ^ (2 * (r : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) := by
  have hpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  congr 1
  have hc : ((r * (2 * r - 2) : ℕ) : ℝ) = (r : ℝ) * (2 * (r : ℝ) - 2) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 2 ≤ 2 * r by omega)]
    push_cast
    ring
  rw [hc]
  unfold weakExponent
  ring

/-- Insertion of the proved fixed complete-moment row, with exact cancellation
of the first scale's triangular degree and all capped factors retained. -/
theorem weak_bilinear_bound (B : Finset ℕ) (k M1 M2 : ℕ)
    (hk : 2000 ≤ k) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M2)
    (q : Fin k → ℕ) (gamma : Fin k → ℝ)
    (hq : ∀ j, order k * M1 ^ (j.val + 1) < 2 ^ q j)
    (hg : ∀ j, gamma j ≠ 0) :
    ‖∑ b : BoundedNat B, ∑ a : Fin M1,
      e (∑ j : Fin k, gamma j * (b.val : ℝ) ^ (j.val + 1) *
        ((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))‖ ^ (order k * (2 * order k)) ≤
    (B.card : ℝ) ^ ((order k - 1) * (2 * order k)) *
      (weakCoefficient k ^ 2 * (order k : ℝ) ^ k *
        (M1 : ℝ) ^ (2 * (order k : ℝ) ^ 2 + (k : ℝ) ^ 2 / 1000) *
        (M2 : ℝ) ^ weakExponent (order k) k *
        ∏ j : Fin k, capFactor (order k * M1 ^ (j.val + 1))
          (order k * M2 ^ (j.val + 1)) (q j) (gamma j)) := by
  have hR : 2 ≤ order k := by unfold order; nlinarith
  have hJ1 : (MAPFordCompleteSystemMoment.completeMoment (order k) k M1 : ℝ) ≤
      weakCoefficient k * (M1 : ℝ) ^ weakExponent (order k) k :=
    fixed_weak_complete_moment hk M1 hM1
  have hJ2 : (MAPFordCompleteSystemMoment.completeMoment (order k) k M2 : ℝ) ≤
      weakCoefficient k * (M2 : ℝ) ^ weakExponent (order k) k :=
    fixed_weak_complete_moment hk M2 hM2
  have hbase := FordBilinearFinite.bilinear_bound B (order k) (order k) k M1 M2
    hR hR hM1 hM2 hB q gamma hq hg
  let P : ℝ := ∏ j : Fin k, FordBilinearFinite.kernelFactor
    (order k * M1 ^ (j.val + 1)) (order k * M2 ^ (j.val + 1)) (q j) (gamma j)
  have hP : 0 ≤ P := by
    dsimp [P, FordBilinearFinite.kernelFactor]
    positivity
  have hJs := mul_le_mul_of_nonneg_right hJ2 hP
  have hJs' := mul_le_mul hJ1 hJs (by positivity) (by unfold weakCoefficient; positivity)
  have hscaled := mul_le_mul_of_nonneg_left hJs'
    (show 0 ≤ (M1 : ℝ) ^ (order k * (2 * order k - 2)) by positivity)
  have hscaled' := mul_le_mul_of_nonneg_left hscaled
    (show 0 ≤ (B.card : ℝ) ^ ((order k - 1) * (2 * order k)) by positivity)
  have hweak := hbase.trans (by simpa only [P, mul_assoc] using hscaled')
  dsimp [P] at hweak
  rw [kernel_product (order k) k M1 M2 (order k) hM1 q gamma] at hweak
  have hm := first_scale_exponent (order k) k M1 (by omega) hM1
  calc
    _ ≤ _ := hweak
    _ = (B.card : ℝ) ^ ((order k - 1) * (2 * order k)) *
      (weakCoefficient k ^ 2 * (order k : ℝ) ^ k *
        ((M1 : ℝ) ^ (order k * (2 * order k - 2)) *
          (M1 : ℝ) ^ weakExponent (order k) k *
          (M1 : ℝ) ^ ((k : ℝ) * (k + 1) / 2)) *
        (M2 : ℝ) ^ weakExponent (order k) k *
        ∏ j : Fin k, capFactor (order k * M1 ^ (j.val + 1))
          (order k * M2 ^ (j.val + 1)) (q j) (gamma j)) := by ring
    _ = _ := by rw [hm]

end FordWeakBilinear
#print axioms FordWeakBilinear.weak_bilinear_bound
