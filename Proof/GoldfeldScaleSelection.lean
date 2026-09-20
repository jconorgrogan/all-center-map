import GoldfeldSameLevelComparison

/-!
# Explicit smoothing-scale selection for Goldfeld comparison
-/

namespace MAPGoldfeldSiegel

open Complex

noncomputable section

def goldfeldBoundaryCoefficient : ℝ :=
  (2 * (1600 * 5 ^ 6)) * 5000 ^ 3 *
    ((2 : ℝ) ^ 28 + (2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ))

def goldfeldComparisonScale (N : ℕ) : ℝ :=
  (2 * goldfeldBoundaryCoefficient * (N : ℝ) ^ 6) ^ 2

theorem goldfeldBoundaryCoefficient_pos : 0 < goldfeldBoundaryCoefficient := by
  unfold goldfeldBoundaryCoefficient
  positivity

theorem goldfeldComparisonScale_ge_twentyEight
    {N : ℕ} [NeZero N] : 28 ≤ goldfeldComparisonScale N := by
  have hD : (14 : ℝ) ≤ goldfeldBoundaryCoefficient := by
    unfold goldfeldBoundaryCoefficient
    norm_num [Nat.factorial]
  have hN : (1 : ℝ) ≤ (N : ℝ) ^ 6 := by
    exact one_le_pow₀ (by exact_mod_cast (NeZero.one_le : 1 ≤ N))
  have hbase : (28 : ℝ) ≤
      2 * goldfeldBoundaryCoefficient * (N : ℝ) ^ 6 := by
    calc
      (28 : ℝ) = 2 * 14 * 1 := by norm_num
      _ ≤ 2 * goldfeldBoundaryCoefficient * (N : ℝ) ^ 6 := by gcongr
  unfold goldfeldComparisonScale
  nlinarith [sq_nonneg
    (2 * goldfeldBoundaryCoefficient * (N : ℝ) ^ 6 - 1)]

theorem rpow_sq_neg_half {y : ℝ} (hy : 0 < y) :
    Real.rpow (y ^ 2) (-1 / 2) = y⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring]
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_neg (sq_nonneg y), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hy.le]

theorem goldfeldBoundaryConstant_comparisonScale
    {N : ℕ} [NeZero N] :
    goldfeldBoundaryConstant N (goldfeldComparisonScale N) = 1 / 2 := by
  let D := goldfeldBoundaryCoefficient
  let y : ℝ := 2 * D * (N : ℝ) ^ 6
  have hD : 0 < D := goldfeldBoundaryCoefficient_pos
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hy : 0 < y := by dsimp [y]; positivity
  have hscale : goldfeldComparisonScale N = y ^ 2 := by rfl
  rw [goldfeldBoundaryConstant, goldfeldBoundaryScale, hscale,
    ← Real.rpow_eq_pow, rpow_sq_neg_half hy]
  change ((2 * (1600 * 5 ^ 6)) * (5000 * (N : ℝ) ^ 2) ^ 3 * y⁻¹) *
      ((2 : ℝ) ^ 28 + (2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ)) = 1 / 2
  have hcoeff :
      ((2 * (1600 * 5 ^ 6)) * (5000 * (N : ℝ) ^ 2) ^ 3) *
          ((2 : ℝ) ^ 28 + (2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ)) =
        D * (N : ℝ) ^ 6 := by
    dsimp [D, goldfeldBoundaryCoefficient]
    ring
  rw [show ((2 * (1600 * 5 ^ 6)) * (5000 * (N : ℝ) ^ 2) ^ 3 * y⁻¹) *
      ((2 : ℝ) ^ 28 + (2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ)) =
      (D * (N : ℝ) ^ 6) * y⁻¹ by rw [← hcoeff]; ring]
  dsimp [y]
  field_simp

/-- The chosen scale has conductor degree twelve. -/
theorem goldfeldComparisonScale_eq
    (N : ℕ) :
    goldfeldComparisonScale N =
      (2 * goldfeldBoundaryCoefficient) ^ 2 * (N : ℝ) ^ 12 := by
  unfold goldfeldComparisonScale
  ring

/-- The smoothing scale and the remaining square-root factor cost conductor
exponent at most `13 * (1-beta)`. -/
theorem comparisonScale_mul_sqrt_rpow_le
    {N : ℕ} [NeZero N] {beta : ℝ}
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1) :
    Real.rpow (goldfeldComparisonScale N) (1 - beta) *
        Real.rpow (Real.sqrt N) (1 - beta) ≤
      (2 * goldfeldBoundaryCoefficient) ^ 2 *
        Real.rpow (N : ℝ) (13 * (1 - beta)) := by
  let C : ℝ := (2 * goldfeldBoundaryCoefficient) ^ 2
  have hgap0 : 0 ≤ 1 - beta := by linarith
  have hgap1 : 1 - beta ≤ 1 := by linarith
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (NeZero.one_le : 1 ≤ N)
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
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    have hRsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    have hRone : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 hNreal
    nlinarith [mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (sub_nonneg.mpr hRone)]
  have hsqrtPow : Real.rpow (Real.sqrt N) (1 - beta) ≤
      Real.rpow (N : ℝ) (1 - beta) :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt hgap0
  rw [hscalePow]
  have hfirst : Real.rpow C (1 - beta) *
      Real.rpow (N : ℝ) (12 * (1 - beta)) ≤
      C * Real.rpow (N : ℝ) (12 * (1 - beta)) :=
    mul_le_mul_of_nonneg_right hCpow
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hsecond :
      (Real.rpow C (1 - beta) * Real.rpow (N : ℝ) (12 * (1 - beta))) *
          Real.rpow (Real.sqrt N) (1 - beta) ≤
        (C * Real.rpow (N : ℝ) (12 * (1 - beta))) *
          Real.rpow (N : ℝ) (1 - beta) :=
    mul_le_mul hfirst hsqrtPow
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (mul_nonneg (zero_le_one.trans hC)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  calc
    (Real.rpow C (1 - beta) * Real.rpow (N : ℝ) (12 * (1 - beta))) *
        Real.rpow (Real.sqrt N) (1 - beta) ≤
      (C * Real.rpow (N : ℝ) (12 * (1 - beta))) *
        Real.rpow (N : ℝ) (1 - beta) := hsecond
    _ = C * Real.rpow (N : ℝ) (13 * (1 - beta)) := by
      have hmerge : Real.rpow (N : ℝ) (12 * (1 - beta)) *
          Real.rpow (N : ℝ) (1 - beta) =
          Real.rpow (N : ℝ) (12 * (1 - beta) + (1 - beta)) :=
        (Real.rpow_add (by positivity) _ _).symm
      rw [show (C * Real.rpow (N : ℝ) (12 * (1 - beta))) *
          Real.rpow (N : ℝ) (1 - beta) =
          C * (Real.rpow (N : ℝ) (12 * (1 - beta)) *
            Real.rpow (N : ℝ) (1 - beta)) by ring,
        hmerge]
      congr 2
      ring

/-- Same-level Goldfeld comparison in the exact shape used by the varying
primitive-level wrapper. -/
theorem sameLevel_goldfeld_Lvalue_lower
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi psi : DirichletCharacter ℂ N)
    (hchiPrim : chi.IsPrimitive)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    (hchiReal : chi ^ 2 = 1) (hpsiReal : psi ^ 2 = 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1) :
    let C := (72000 * (2 * goldfeldBoundaryCoefficient) ^ 2)⁻¹
    C * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
        (1 + Real.log N) ^ 3 ≤
      ‖DirichletCharacter.LFunction psi 1‖ := by
  dsimp only
  let C0 : ℝ := (2 * goldfeldBoundaryCoefficient) ^ 2
  let B : ℝ := 72000 * C0
  have hD := goldfeldBoundaryCoefficient_pos
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hX := goldfeldComparisonScale_ge_twentyEight (N := N)
  have hboundary : goldfeldBoundaryConstant N (goldfeldComparisonScale N) ≤ 1 / 2 := by
    rw [goldfeldBoundaryConstant_comparisonScale]
  have hraw := sameLevel_goldfeld_comparison hN chi psi hchiPrim hchi hpsi hmul
    hchiReal hpsiReal hzero hbetaLow hbetaHigh hX hboundary
  have hscale := comparisonScale_mul_sqrt_rpow_le
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
        72000 *
          (Real.rpow (goldfeldComparisonScale N) (1 - beta) *
            Real.rpow (Real.sqrt N) (1 - beta)) *
          ((1 + Real.log N) ^ 3 *
            ‖DirichletCharacter.LFunction psi 1‖) := by
      convert hscaled using 1 <;> ring
    have hupper := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 72000))
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
  have hid : (72000 * (2 * goldfeldBoundaryCoefficient) ^ 2)⁻¹ *
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

#print axioms MAPGoldfeldSiegel.goldfeldBoundaryConstant_comparisonScale
#print axioms MAPGoldfeldSiegel.comparisonScale_mul_sqrt_rpow_le
#print axioms MAPGoldfeldSiegel.sameLevel_goldfeld_Lvalue_lower
