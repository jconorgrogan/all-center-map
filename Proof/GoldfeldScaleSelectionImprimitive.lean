import GoldfeldScaleSelection
import GoldfeldSameLevelImprimitiveComparison

/-!
# Smoothing-scale selection for the imprimitive same-level comparison
-/

namespace MAPGoldfeldSiegel

open Complex

noncomputable section

/-- The degree-twelve smoothing scale together with the current-level
derivative factor has total conductor exponent `13 * (1-beta)`. -/
theorem comparisonScale_mul_level_rpow_le
    {N : ℕ} [NeZero N] {beta : ℝ}
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1) :
    Real.rpow (goldfeldComparisonScale N) (1 - beta) *
        Real.rpow (N : ℝ) (1 - beta) ≤
      (2 * goldfeldBoundaryCoefficient) ^ 2 *
        Real.rpow (N : ℝ) (13 * (1 - beta)) := by
  let C : ℝ := (2 * goldfeldBoundaryCoefficient) ^ 2
  have hgap1 : 1 - beta ≤ 1 := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hC : 1 ≤ C := by
    dsimp [C]
    unfold goldfeldBoundaryCoefficient
    norm_num [Nat.factorial]
  have hCpow : Real.rpow C (1 - beta) ≤ C := by
    have := Real.rpow_le_rpow_of_exponent_le hC hgap1
    simpa [Real.rpow_one, Real.rpow_eq_pow] using this
  have hscalePow : Real.rpow (goldfeldComparisonScale N) (1 - beta) =
      Real.rpow C (1 - beta) * Real.rpow (N : ℝ) (12 * (1 - beta)) := by
    rw [goldfeldComparisonScale_eq]
    change Real.rpow (C * (N : ℝ) ^ 12) (1 - beta) = _
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    calc
      Real.rpow ((N : ℝ) ^ 12) (1 - beta) =
          Real.rpow (Real.rpow (N : ℝ) (12 : ℝ)) (1 - beta) := by
        congr 1
        exact (Real.rpow_natCast (N : ℝ) 12).symm
      _ = Real.rpow (N : ℝ) (12 * (1 - beta)) :=
        (Real.rpow_mul (Nat.cast_nonneg N) 12 (1 - beta)).symm
  rw [hscalePow]
  have hNpow0 : 0 ≤ Real.rpow (N : ℝ) (12 * (1 - beta)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hNpow10 : 0 ≤ Real.rpow (N : ℝ) (1 - beta) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    (Real.rpow C (1 - beta) * Real.rpow (N : ℝ) (12 * (1 - beta))) *
        Real.rpow (N : ℝ) (1 - beta) ≤
      (C * Real.rpow (N : ℝ) (12 * (1 - beta))) *
        Real.rpow (N : ℝ) (1 - beta) := by
          gcongr
    _ = C * Real.rpow (N : ℝ) (13 * (1 - beta)) := by
      have hmerge : Real.rpow (N : ℝ) (12 * (1 - beta)) *
          Real.rpow (N : ℝ) (1 - beta) =
          Real.rpow (N : ℝ) (12 * (1 - beta) + (1 - beta)) :=
        (Real.rpow_add hNpos _ _).symm
      rw [show (C * Real.rpow (N : ℝ) (12 * (1 - beta))) *
          Real.rpow (N : ℝ) (1 - beta) =
          C * (Real.rpow (N : ℝ) (12 * (1 - beta)) *
            Real.rpow (N : ℝ) (1 - beta)) by ring,
        hmerge]
      congr 2
      ring

/-- Same-level lower bound at the selected scale, valid for a possibly
imprimitive exceptional character. -/
theorem sameLevel_goldfeld_Lvalue_lower_nonprimitive
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    (hchiReal : chi ^ 2 = 1) (hpsiReal : psi ^ 2 = 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1) :
    let C := (24000 * (2 * goldfeldBoundaryCoefficient) ^ 2)⁻¹
    C * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
        (1 + Real.log N) ^ 3 ≤
      ‖DirichletCharacter.LFunction psi 1‖ := by
  dsimp only
  let C0 : ℝ := (2 * goldfeldBoundaryCoefficient) ^ 2
  let B : ℝ := 24000 * C0
  have hC0 : 0 < C0 := by
    dsimp [C0]
    positivity [goldfeldBoundaryCoefficient_pos]
  have hB : 0 < B := by dsimp [B]; positivity
  have hX := goldfeldComparisonScale_ge_twentyEight (N := N)
  have hboundary : goldfeldBoundaryConstant N (goldfeldComparisonScale N) ≤
      1 / 2 := by
    rw [goldfeldBoundaryConstant_comparisonScale]
  have hraw := sameLevel_goldfeld_comparison_nonprimitive hN chi psi
    hchi hpsi hmul hchiReal hpsiReal hzero hbetaLow hbetaHigh hX hboundary
  have hscale := comparisonScale_mul_level_rpow_le
    (N := N) hbetaLow hbetaHigh
  have hL0 : 0 < 1 + Real.log (N : ℝ) := by
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (NeZero.one_le : 1 ≤ N))
    linarith
  have hnorm0 : 0 ≤ ‖DirichletCharacter.LFunction psi 1‖ := norm_nonneg _
  have hcoarse : (1 : ℝ) ≤
      B * Real.rpow (N : ℝ) (13 * (1 - beta)) *
        (1 + Real.log N) ^ 3 *
        ‖DirichletCharacter.LFunction psi 1‖ := by
    have hscaled := mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 4)
    have hscaled' : (1 : ℝ) ≤
        24000 *
          (Real.rpow (goldfeldComparisonScale N) (1 - beta) *
            Real.rpow (N : ℝ) (1 - beta)) *
          ((1 + Real.log N) ^ 3 *
            ‖DirichletCharacter.LFunction psi 1‖) := by
      convert hscaled using 1 <;> ring
    have hupper := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 24000))
      (mul_nonneg (pow_nonneg hL0.le 3) hnorm0)
    dsimp [B, C0]
    simpa [mul_assoc] using hscaled'.trans hupper
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hden : 0 < B * Real.rpow (N : ℝ) (13 * (1 - beta)) *
      (1 + Real.log N) ^ 3 :=
    mul_pos (mul_pos hB (Real.rpow_pos_of_pos hNpos _)) (pow_pos hL0 3)
  have hinv : (B * Real.rpow (N : ℝ) (13 * (1 - beta)) *
      (1 + Real.log N) ^ 3)⁻¹ ≤
      ‖DirichletCharacter.LFunction psi 1‖ := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hden).2 (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcoarse)
  have hid : (24000 * (2 * goldfeldBoundaryCoefficient) ^ 2)⁻¹ *
        Real.rpow (N : ℝ) (-13 * (1 - beta)) /
          (1 + Real.log N) ^ 3 =
      (B * Real.rpow (N : ℝ) (13 * (1 - beta)) *
        (1 + Real.log N) ^ 3)⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [show -13 * (1 - beta) = -(13 * (1 - beta)) by ring]
    rw [Real.rpow_neg hNpos.le]
    dsimp [B, C0]
    field_simp
  rw [hid]
  exact hinv

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.comparisonScale_mul_level_rpow_le
#print axioms MAPGoldfeldSiegel.sameLevel_goldfeld_Lvalue_lower_nonprimitive
