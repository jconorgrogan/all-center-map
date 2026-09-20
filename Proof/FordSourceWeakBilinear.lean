import FordWeakBilinear
import FordSourceKernelFactor

open scoped BigOperators
open FordWeakBilinear FordSourceKernelFactor
open FordPolynomialPhase FordSubsetMoment FordWeakCompleteMoment

namespace FordSourceWeakBilinear
noncomputable section

def sourceGamma (t z : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (j + 1) * t /
    (2 * Real.pi * (j + 1 : ℝ) * z ^ (j + 1))

lemma order_pos {k : ℕ} (hk : 2000 ≤ k) : 0 < FordWeakBilinear.order k := by
  unfold FordWeakBilinear.order
  positivity

lemma source_capFactor_le
    {k M1 M2 N : ℕ} {t z : ℝ}
    (hk : 2000 ≤ k) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hN : 0 < N) (ht : 0 < t) (hzlo : (N : ℝ) ≤ z)
    (hzhi : z ≤ 2 * N) (q : Fin k → ℕ)
    (hq : ∀ j, FordWeakBilinear.order k * M1 ^ (j.val + 1) < 2 ^ q j) :
    ∀ j : Fin k,
      FordWeakBilinear.capFactor
          (FordWeakBilinear.order k * M1 ^ (j.val + 1))
          (FordWeakBilinear.order k * M2 ^ (j.val + 1)) (q j)
          (sourceGamma t z j.val) ≤
        (2 * (q j : ℝ) + 1) *
          sourceW (FordWeakBilinear.order k) (FordWeakBilinear.order k)
            M1 M2 (j.val + 1) N t := by
  intro j
  let R := FordWeakBilinear.order k
  have hR1 : 1 ≤ R := by
    dsimp [R]
    unfold FordWeakBilinear.order
    nlinarith
  have hL : 2 ≤ R * M1 ^ (j.val + 1) := by
    have hp : 1 ≤ M1 ^ (j.val + 1) := by
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hR2 : 2 ≤ R := by
      dsimp [R]
      unfold FordWeakBilinear.order
      nlinarith
    exact hR2.trans (by simpa using Nat.mul_le_mul_left R hp)
  have hgamma0 : sourceGamma t z j.val ≠ 0 := by
    dsimp [sourceGamma]
    apply div_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt ht)
    · have hz0 : 0 < z := lt_of_lt_of_le (by positivity : 0 < (N : ℝ)) hzlo
      positivity
  have hkernel := kernelFactor_le_source
    (r := R) (s := R) (M := M1) (M2 := M2)
    (j := j.val + 1) (N := N) (q := q j) (t := t) (z := z)
    hR1 hR1 hM1 hM2 (by omega) hN ht hzlo hzhi hL (hq j)
  have hLpos : 0 < (R * M1 ^ (j.val + 1) : ℝ) := by positivity
  have hkernel' :
      (R * M1 ^ (j.val + 1) : ℝ) *
          FordWeakBilinear.capFactor
            (R * M1 ^ (j.val + 1))
            (R * M2 ^ (j.val + 1)) (q j) (sourceGamma t z j.val) ≤
        (R * M1 ^ (j.val + 1) : ℝ) *
          ((2 * (q j : ℝ) + 1) *
            sourceW R R M1 M2 (j.val + 1) N t) := by
    calc
      (R * M1 ^ (j.val + 1) : ℝ) *
          FordWeakBilinear.capFactor
            (R * M1 ^ (j.val + 1))
            (R * M2 ^ (j.val + 1)) (q j) (sourceGamma t z j.val) =
          FordBilinearFinite.kernelFactor
            (R * M1 ^ (j.val + 1))
            (R * M2 ^ (j.val + 1)) (q j) (sourceGamma t z j.val) := by
              simp [FordBilinearFinite.kernelFactor,
                FordWeakBilinear.capFactor, Nat.cast_mul, Nat.cast_pow]
      _ ≤ _ := by
        simpa [R, sourceGamma, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hkernel
      _ = (R * M1 ^ (j.val + 1) : ℝ) *
          ((2 * (q j : ℝ) + 1) *
            sourceW R R M1 M2 (j.val + 1) N t) := by ring
  exact le_of_mul_le_mul_left hkernel' hLpos

lemma source_factor_nonneg
    {k M1 M2 N : ℕ} {t z : ℝ} (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hN : 0 < N) (ht : 0 < t) (hzlo : (N : ℝ) ≤ z) (j : Fin k) :
    0 ≤ (2 * (j.val + 1 : ℝ) + 1) *
      sourceW (FordWeakBilinear.order k) (FordWeakBilinear.order k)
        M1 M2 (j.val + 1) N t := by
  unfold sourceW sourceC
  positivity

 theorem weak_bilinear_bound_source
    (B : Finset ℕ) (k M1 M2 N : ℕ)
    (hk : 2000 ≤ k) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M2)
    (hN : 0 < N) (t z : ℝ) (ht : 0 < t)
    (hzlo : (N : ℝ) ≤ z) (hzhi : z ≤ 2 * N)
    (q : Fin k → ℕ)
    (hq : ∀ j, FordWeakBilinear.order k * M1 ^ (j.val + 1) < 2 ^ q j) :
    ‖∑ b : FordSubsetMoment.BoundedNat B, ∑ a : Fin M1,
      e (∑ j : Fin k, sourceGamma t z j.val * (b.val : ℝ) ^ (j.val + 1) *
        ((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))‖ ^
        (FordWeakBilinear.order k * (2 * FordWeakBilinear.order k)) ≤
    (B.card : ℝ) ^ ((FordWeakBilinear.order k - 1) *
        (2 * FordWeakBilinear.order k)) *
      (weakCoefficient k ^ 2 * (FordWeakBilinear.order k : ℝ) ^ k *
        (M1 : ℝ) ^ (2 * (FordWeakBilinear.order k : ℝ) ^ 2 +
          (k : ℝ) ^ 2 / 1000) *
        (M2 : ℝ) ^ weakExponent (FordWeakBilinear.order k) k *
        ∏ j : Fin k,
          ((2 * (q j : ℝ) + 1) *
            sourceW (FordWeakBilinear.order k) (FordWeakBilinear.order k)
              M1 M2 (j.val + 1) N t)) := by
  let gamma : Fin k → ℝ := fun j => sourceGamma t z j.val
  have hgamma : ∀ j, gamma j ≠ 0 := by
    intro j
    dsimp [gamma]
    apply div_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt ht)
    · have hz0 : 0 < z := lt_of_lt_of_le (by positivity : 0 < (N : ℝ)) hzlo
      positivity
  have hweak := FordWeakBilinear.weak_bilinear_bound B k M1 M2
    hk hM1 hM2 hB q gamma hq hgamma
  dsimp [gamma] at hweak
  have hcap := source_capFactor_le hk hM1 hM2 hN ht hzlo hzhi q hq
  have hprod :
      (∏ j : Fin k, FordWeakBilinear.capFactor
        (FordWeakBilinear.order k * M1 ^ (j.val + 1))
        (FordWeakBilinear.order k * M2 ^ (j.val + 1)) (q j) (gamma j)) ≤
      ∏ j : Fin k,
        ((2 * (q j : ℝ) + 1) *
          sourceW (FordWeakBilinear.order k) (FordWeakBilinear.order k)
            M1 M2 (j.val + 1) N t) := by
    apply Finset.prod_le_prod
    · intro j hj
      dsimp [FordWeakBilinear.capFactor]
      positivity
    · intro j hj
      simpa [gamma] using hcap j
  have hbase0 : 0 ≤
      (B.card : ℝ) ^ ((FordWeakBilinear.order k - 1) *
        (2 * FordWeakBilinear.order k)) *
      (weakCoefficient k ^ 2 * (FordWeakBilinear.order k : ℝ) ^ k *
        (M1 : ℝ) ^ (2 * (FordWeakBilinear.order k : ℝ) ^ 2 +
          (k : ℝ) ^ 2 / 1000) *
        (M2 : ℝ) ^ weakExponent (FordWeakBilinear.order k) k) := by positivity
  calc
    _ ≤ (B.card : ℝ) ^ ((FordWeakBilinear.order k - 1) *
        (2 * FordWeakBilinear.order k)) *
      (weakCoefficient k ^ 2 * (FordWeakBilinear.order k : ℝ) ^ k *
        (M1 : ℝ) ^ (2 * (FordWeakBilinear.order k : ℝ) ^ 2 +
          (k : ℝ) ^ 2 / 1000) *
        (M2 : ℝ) ^ weakExponent (FordWeakBilinear.order k) k *
        ∏ j : Fin k, FordWeakBilinear.capFactor
          (FordWeakBilinear.order k * M1 ^ (j.val + 1))
          (FordWeakBilinear.order k * M2 ^ (j.val + 1)) (q j) (gamma j)) := hweak
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hprod hbase0
      simpa [mul_assoc] using hmul
    _ = _ := by ring

end
end FordSourceWeakBilinear

#print axioms FordSourceWeakBilinear.weak_bilinear_bound_source
