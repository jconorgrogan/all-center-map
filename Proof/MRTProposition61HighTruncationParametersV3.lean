import MAPHBPerronSourceData

/-! # Legal free truncation and exact high-packet Perron error scaling -/

namespace MRTProposition61HighTruncationParametersV3

open MAPHBPerronSourceData

noncomputable section

set_option maxHeartbeats 1000000

/-- The free truncation is legal even at the smallest allowed stationary
width. The actual aperture exponent, including its reserve, is retained. -/
theorem highFreeTruncation_ge_one
    {X U reserve sigma : ℝ} (hX : 1 ≤ X) (hU : 1 ≤ U)
    (hr : reserve ≤ 1 / 1200) (hsigma : sigma ≤ 1 / 24) :
    1 ≤ (U / ((1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve))) *
      Real.rpow X (1 - sigma) := by
  have hX0 : 0 < X := by linarith
  have hpow : 1 ≤ Real.rpow X (1 - sigma - (2 / 15 + reserve)) :=
    Real.one_le_rpow hX (by linarith)
  calc
    1 ≤ 2 * U * Real.rpow X (1 - sigma - (2 / 15 + reserve)) := by nlinarith
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_sub hX0]
      ring

/-- The main term from the truncation has a uniform power saving, because
the same collar relation bounds `q*U/H`. -/
theorem highFreeTruncation_mul_modulus_le
    {X H U q Q sigma : ℝ} (hX : 0 ≤ X) (hH : 0 < H) (hQ : 0 < Q)
    (hqu : q * U ≤ H / Q) :
    q * ((U / H) * Real.rpow X (1 - sigma)) ≤ Real.rpow X (1 - sigma) / Q := by
  calc
    _ = (q * U / H) * Real.rpow X (1 - sigma) := by ring
    _ ≤ ((H / Q) / H) * Real.rpow X (1 - sigma) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hqu hH.le)
        (Real.rpow_nonneg hX _)
    _ = _ := by field_simp

/-- Exact source normalization of the literal Perron error. -/
theorem normalized_perronCellError_eq
    {q : ℕ} {D N M T B U a b K : ℝ}
    (hq : 0 < (q : ℝ)) (hU : U ≠ 0) (hNM : 0 ≤ N * M) :
    D / ((q : ℝ) * U ^ 2) * perronCellError q N M T B U a b K =
      8 * K ^ 2 * D * q * (b - a) * B ^ 2 * (N * M) *
        (Real.log (2 + T) / T) ^ 2 := by
  unfold perronCellError
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt hNM]
  field_simp
  <;> ring

/-- Exact power cancellation for `T=(U/H)X^(1-sigma)`. -/
theorem highFreeTruncation_power_ratio
    {X H U sigma : ℝ} (hX : 0 < X) (hH : H ≠ 0) (hU : U ≠ 0) :
    X ^ 2 / ((U / H) * Real.rpow X (1 - sigma)) ^ 2 =
      H ^ 2 / U ^ 2 * Real.rpow X (2 * sigma) := by
  have hp : Real.rpow X (1 - sigma) ^ 2 * Real.rpow X (2 * sigma) = X ^ 2 := by
    calc
      _ = Real.rpow X ((1 - sigma) * 2) * Real.rpow X (2 * sigma) := by
        exact congrArg (fun y : ℝ => y * Real.rpow X (2 * sigma))
          (Real.rpow_mul_natCast hX.le (1 - sigma) 2).symm
      _ = Real.rpow X ((1 - sigma) * 2 + 2 * sigma) := (Real.rpow_add hX _ _).symm
      _ = X ^ 2 := by
        rw [show (1 - sigma) * 2 + 2 * sigma = (2 : ℝ) by ring]
        exact Real.rpow_natCast X 2
  have hp0 : Real.rpow X (1 - sigma) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Real.rpow_pos_of_pos hX _).ne'
  have hratio : X ^ 2 / Real.rpow X (1 - sigma) ^ 2 = Real.rpow X (2 * sigma) := by
    apply (div_eq_iff hp0).2
    simpa only [mul_comm] using hp.symm
  calc
    _ = H ^ 2 / U ^ 2 * (X ^ 2 / Real.rpow X (1 - sigma) ^ 2) := by field_simp
    _ = _ := by rw [hratio]

/-- The actual collar and active product bound yield the correct free-T
error: the power of `X` is `2 sigma`, before inserting the coefficient bound
and the remaining `H/U` factor. -/
theorem normalized_perronCellError_freeT_le
    {q : ℕ} {D N M B U a b K X H eta sigma : ℝ}
    (hq : 0 < (q : ℝ)) (hD : 0 ≤ D) (hX : 0 < X)
    (hH : 0 < H) (hU : 0 < U) (heta : 0 < eta)
    (hab : a ≤ b) (hNM0 : 0 ≤ N * M)
    (hproduct : N * M ≤ 2 * X) (hL : b - a ≤ U * X / (eta * H)) :
    let T := (U / H) * Real.rpow X (1 - sigma)
    D / ((q : ℝ) * U ^ 2) * perronCellError q N M T B U a b K ≤
      16 * K ^ 2 * D * q * H / (eta * U) * B ^ 2 *
        Real.rpow X (2 * sigma) * Real.log (2 + T) ^ 2 := by
  dsimp only
  let T := (U / H) * Real.rpow X (1 - sigma)
  rw [normalized_perronCellError_eq hq hU.ne' hNM0]
  have hT0 : 0 < T := by
    dsimp [T]
    exact mul_pos (div_pos hU hH) (Real.rpow_pos_of_pos hX _)
  calc
    _ ≤ 8 * K ^ 2 * D * q * (U * X / (eta * H)) * B ^ 2 * (2 * X) *
        (Real.log (2 + T) / T) ^ 2 := by gcongr
    _ = 16 * K ^ 2 * D * q * B ^ 2 * (U / (eta * H)) *
        (X ^ 2 / T ^ 2) * Real.log (2 + T) ^ 2 := by ring
    _ = _ := by
      dsimp [T]
      have hr := highFreeTruncation_power_ratio (sigma := sigma) hX hH.ne' hU.ne'
      simp only [Real.rpow_eq_pow] at hr
      rw [hr]
      field_simp
      <;> ring

end
end MRTProposition61HighTruncationParametersV3

#print axioms MRTProposition61HighTruncationParametersV3.highFreeTruncation_ge_one
#print axioms MRTProposition61HighTruncationParametersV3.normalized_perronCellError_freeT_le
