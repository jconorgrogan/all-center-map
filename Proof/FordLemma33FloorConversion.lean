import Mathlib

open scoped BigOperators

noncomputable section
namespace FordLemma33FloorConversion

/-- The natural floor quotient loses no more than the corresponding real divisor
bound after raising to the moment power and multiplying by a nonnegative factor. -/
theorem floor_term_le_source_scalar
    (p P k r : ℕ) (hp : 0 < p) (hP : 0 < P) (hk : 0 < k) (hr : 0 < r)
    {J K : ℝ} (hJ : 0 ≤ J) (hK : 0 ≤ K) :
    (2 : ℝ) ^ (k + 1) * (((P / p ^ r : ℕ) : ℝ) ^ k) * Real.sqrt (J * K) ≤
      (2 * (P : ℝ)) ^ k *
        (2 / (p : ℝ) ^ (r * k)) * Real.sqrt (J * K) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hprR : 0 < (p : ℝ) ^ r := pow_pos hpR _
  have hfloor : ((P / p ^ r : ℕ) : ℝ) ≤ (P : ℝ) / (p : ℝ) ^ r := by
    simpa [Nat.cast_pow] using
      (Nat.cast_div_le (α := ℝ) (m := P) (n := p ^ r))
  have hfloorpow : (((P / p ^ r : ℕ) : ℝ) ^ k) ≤
      ((P : ℝ) / (p : ℝ) ^ r) ^ k :=
    pow_le_pow_left₀ (by positivity) hfloor k
  have hsqrt : 0 ≤ Real.sqrt (J * K) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hfloorpow hsqrt
  have hmul2 := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ (2 : ℝ) ^ (k + 1))
  calc
    (2 : ℝ) ^ (k + 1) * (((P / p ^ r : ℕ) : ℝ) ^ k) * Real.sqrt (J * K) ≤
        (2 : ℝ) ^ (k + 1) * ((P : ℝ) / (p : ℝ) ^ r) ^ k * Real.sqrt (J * K) := by
          simpa [mul_assoc] using hmul2
    _ = (2 * (P : ℝ)) ^ k *
          (2 / (p : ℝ) ^ (r * k)) * Real.sqrt (J * K) := by
      rw [div_pow, ← pow_mul]
      field_simp
      ring

/-- Convert a finite floor-based maximum bound into the common source scalar
bound. The quotient remains a natural division throughout the hypothesis. -/
theorem finite_floor_bound_le_source_scalar
    (p P k r : ℕ) (hp : 0 < p) (hP : 0 < P) (hk : 0 < k) (hr : 0 < r)
    {L J K : ℝ} (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hL : L ≤ max
      ((2 * (k : ℝ) * (P : ℝ)) ^ k * J)
      ((2 : ℝ) ^ (k + 1) * (((P / p ^ r : ℕ) : ℝ) ^ k) * Real.sqrt (J * K))) :
    L ≤ (2 * (P : ℝ)) ^ k *
      max ((k : ℝ) ^ k * J)
        (2 / (p : ℝ) ^ (r * k) * Real.sqrt (J * K)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hPR : 0 ≤ (P : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (J * K) := Real.sqrt_nonneg _
  have hscale : 0 ≤ (2 * (P : ℝ)) ^ k := by positivity
  have hfirst : (2 * (k : ℝ) * (P : ℝ)) ^ k * J ≤
      (2 * (P : ℝ)) ^ k *
        max ((k : ℝ) ^ k * J)
          (2 / (p : ℝ) ^ (r * k) * Real.sqrt (J * K)) := by
    calc
      (2 * (k : ℝ) * (P : ℝ)) ^ k * J =
          (2 * (P : ℝ)) ^ k * ((k : ℝ) ^ k * J) := by
            rw [mul_assoc, mul_pow]
            ring
      _ ≤ (2 * (P : ℝ)) ^ k *
          max ((k : ℝ) ^ k * J)
            (2 / (p : ℝ) ^ (r * k) * Real.sqrt (J * K)) := by
            exact mul_le_mul_of_nonneg_left (le_max_left _ _)
              (by positivity)
  have hsecond0 := floor_term_le_source_scalar p P k r hp hP hk hr hJ hK
  have hsecond : (2 : ℝ) ^ (k + 1) * (((P / p ^ r : ℕ) : ℝ) ^ k) *
        Real.sqrt (J * K) ≤
      (2 * (P : ℝ)) ^ k *
        max ((k : ℝ) ^ k * J)
          (2 / (p : ℝ) ^ (r * k) * Real.sqrt (J * K)) := by
    exact hsecond0.trans (by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (le_max_right ((k : ℝ) ^ k * J)
            (2 / (p : ℝ) ^ (r * k) * Real.sqrt (J * K))) hscale))
  exact hL.trans (max_le hfirst hsecond)

end FordLemma33FloorConversion

#print axioms FordLemma33FloorConversion.floor_term_le_source_scalar
#print axioms FordLemma33FloorConversion.finite_floor_bound_le_source_scalar
