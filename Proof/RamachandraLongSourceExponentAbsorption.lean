import Mathlib

/-!
# Source-strip exponent absorption for the Ramachandra long contour

After the exact long-contour moment and dyadic cutoff estimates are squared,
their only nonintegral scale is `X^(2-2*sigma)`.  On the Theorem-6 strip this
is at most an absolute constant times `X`, even though the strip is expressed
using the ambient modulus `q` while `X=dT` uses a divisor `d`.
-/

namespace RamachandraLongSourceExponentAbsorption

noncomputable section

/-- The small horizontal displacement contributes at most `exp(1/50)` after
being transferred from the ambient scale `qT` to the primitive scale `dT`. -/
theorem rpow_two_sub_two_sigma_le_exp_mul
    (q d : ℕ) [NeZero q] [NeZero d] {T sigma : ℝ}
    (hdq : d ∣ q) (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    Real.rpow ((d : ℝ) * T) (2 - 2 * sigma) ≤
      Real.exp (1 / 50 : ℝ) * ((d : ℝ) * T) := by
  have hdqNat : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdq
  have hdpos : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hTpos : 0 < T := by linarith
  let X : ℝ := (d : ℝ) * T
  let Q : ℝ := (q : ℝ) * T
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQthree : 3 ≤ Q := by
    dsimp [Q]
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    nlinarith
  have hlogQ : 1 < Real.log Q :=
    (Real.lt_log_iff_exp_lt hQpos).2
      (lt_of_lt_of_le Real.exp_one_lt_three hQthree)
  have hXleQ : X ≤ Q := by
    dsimp [X, Q]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdqNat) hTpos.le
  have hlogX0 : 0 ≤ Real.log X := by
    apply Real.log_nonneg
    dsimp [X]
    have hdone : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
    nlinarith
  have hlogXle : Real.log X ≤ Real.log Q :=
    Real.log_le_log hXpos hXleQ
  have hdelta : (1 / 2 : ℝ) - sigma ≤
      (100 * Real.log Q)⁻¹ := by
    have hlo : -(100 * Real.log Q)⁻¹ ≤ sigma - (1 / 2 : ℝ) := by
      simpa only [Q] using (abs_le.mp hstrip).1
    linarith
  have hdenpos : 0 < 100 * Real.log Q := by positivity
  have hexponent : Real.log X * (1 - 2 * sigma) ≤ 1 / 50 := by
    have htwodelta : 1 - 2 * sigma ≤
        2 * (100 * Real.log Q)⁻¹ := by linarith
    have hnonnegDelta : 0 ≤ 2 * (100 * Real.log Q)⁻¹ := by positivity
    calc
      Real.log X * (1 - 2 * sigma) ≤
          Real.log X * (2 * (100 * Real.log Q)⁻¹) :=
        mul_le_mul_of_nonneg_left htwodelta hlogX0
      _ ≤ Real.log Q * (2 * (100 * Real.log Q)⁻¹) :=
        mul_le_mul_of_nonneg_right hlogXle hnonnegDelta
      _ = 1 / 50 := by field_simp <;> norm_num
  have hone : Real.rpow X (1 - 2 * sigma) ≤ Real.exp (1 / 50 : ℝ) := by
    calc
      Real.rpow X (1 - 2 * sigma) =
          Real.exp (Real.log X * (1 - 2 * sigma)) :=
        Real.rpow_def_of_pos hXpos (1 - 2 * sigma)
      _ ≤ Real.exp (1 / 50 : ℝ) := Real.exp_le_exp.mpr hexponent
  calc
    Real.rpow ((d : ℝ) * T) (2 - 2 * sigma) =
        Real.rpow X (1 + (1 - 2 * sigma)) := by
      change Real.rpow X (2 - 2 * sigma) = _
      rw [show 2 - 2 * sigma = 1 + (1 - 2 * sigma) by ring]
    _ = Real.rpow X 1 * Real.rpow X (1 - 2 * sigma) :=
      Real.rpow_add hXpos 1 (1 - 2 * sigma)
    _ ≤ X * Real.exp (1 / 50 : ℝ) := by
      rw [show Real.rpow X 1 = X from Real.rpow_one X]
      exact mul_le_mul_of_nonneg_left hone hXpos.le
    _ = Real.exp (1 / 50 : ℝ) * ((d : ℝ) * T) := by
      dsimp [X]
      ring

end
end RamachandraLongSourceExponentAbsorption

#print axioms RamachandraLongSourceExponentAbsorption.rpow_two_sub_two_sigma_le_exp_mul
