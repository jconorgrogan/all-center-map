import FordBoundaryWeightedHolder

noncomputable section
namespace FordBoundaryScalar

/-- The literal boundary ledger contradicts a majority boundary once the alphabet
is larger than (4s)^2. All zero cases are retained. -/
theorem interior_absorption {s : ℕ} (hs : 1 ≤ s) {E B I H M : ℝ}
    (hE0 : 0 ≤ E) (hB0 : 0 ≤ B) (hI0 : 0 ≤ I)
    (hpartition : E ≤ I + 2 * (s : ℝ) * H)
    (hholder : H ≤ E ^ ((1 : ℝ) - 1 / (2 * s : ℝ)) * B ^ (1 / (2 * s : ℝ)))
    (hdiagonal : M^s * B ≤ E)
    (hsize : (4 * (s : ℝ))^2 < M) : E ≤ 2 * I := by
  by_contra hnot
  have hbig : 2 * I < E := lt_of_not_ge hnot
  have hEp : 0 < E := by linarith
  have hfour : E ≤ 4 * (s : ℝ) * H := by linarith
  have hEholder : E ≤ 4 * (s : ℝ) *
      E ^ ((1 : ℝ) - 1 / (2 * s : ℝ)) * B ^ (1 / (2 * s : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hholder (by positivity : 0 ≤ 4 * (s : ℝ))
    exact hfour.trans (by simpa only [mul_assoc] using hh)
  have hupper := FordBoundaryWeightedHolder.scalar_absorption hs hE0 hB0 hEholder
  have hBp : 0 < B := by
    by_contra hnotB
    have hz : B = 0 := le_antisymm (le_of_not_gt hnotB) hB0
    rw [hz, mul_zero] at hupper
    linarith
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hpower : ((4 * (s : ℝ))^2)^s < M^s := by
    have hh := Real.rpow_lt_rpow (sq_nonneg (4 * (s : ℝ))) hsize hsR
    simpa only [Real.rpow_natCast] using hh
  have hK : (4 * (s : ℝ))^(2*s) < M^s := by
    rw [pow_mul]
    exact hpower
  have hstrict := mul_lt_mul_of_pos_right hK hBp
  linarith

end FordBoundaryScalar
#print axioms FordBoundaryScalar.interior_absorption
