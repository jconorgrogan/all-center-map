import RamachandraShiftedDirectTailAbsorption

/-!
# Finite-shell absorption for Ramachandra's shifted direct series

This file bounds the only finite expression left by the canonical direct
series theorem.  The sole analytic scalar input is the displayed bound on the
small horizontal shift factor; all shell, harmonic, and dyadic-count estimates
are proved here.
-/

namespace RamachandraShiftedDirectShellAbsorption

open scoped BigOperators
open RamachandraShiftedDirectParameters
open RamachandraShiftedDirectAssembly
open RamachandraShiftedDirectTailAbsorption
open RamachandraPrimitiveShiftedContourReduction
open MRTLemma215DyadicPartition

noncomputable section

variable {X : ℝ}

private theorem canonical_M_cast_le
    (hX : 3 ≤ X) :
    (directTruncation X : ℝ) ≤ 2 * X * Real.log X ^ 16 := by
  have hupper := (directTruncation_upper hX).le
  have hy : 1 ≤ Real.log X := (one_lt_log_of_three_le hX).le
  have hbase : 3 ≤ X * Real.log X ^ 16 := by
    have hp : 1 ≤ Real.log X ^ 16 := one_le_pow₀ hy
    nlinarith
  linarith

private theorem canonical_Y_le
    (hX : 3 ≤ X) :
    directEnergyCeiling X ≤ 4 * X * Real.log X ^ 16 := by
  dsimp [directEnergyCeiling]
  push_cast
  nlinarith [canonical_M_cast_le hX]

private theorem log_four_le_two_log
    (hX : 3 ≤ X) : Real.log 4 ≤ 2 * Real.log X := by
  have hlog2 : Real.log 2 ≤ Real.log X :=
    Real.log_le_log (by norm_num) (by linarith)
  have heq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [heq]
  linarith

private theorem canonical_log_Y_le
    (hX : 3 ≤ X) :
    Real.log (directEnergyCeiling X) ≤ 19 * Real.log X := by
  let y := Real.log X
  have hX0 : 0 < X := by linarith
  have hy : 1 ≤ y := by simpa [y] using (one_lt_log_of_three_le hX).le
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hYpos : 0 < directEnergyCeiling X := by
    dsimp [directEnergyCeiling]
    exact_mod_cast (mul_pos (by norm_num : 0 < (2 : ℕ))
      (directTruncation_pos hX))
  have hupper := canonical_Y_le hX
  have hprodpos : 0 < 4 * X * y ^ 16 := by positivity
  have hlogmono : Real.log (directEnergyCeiling X) ≤
      Real.log (4 * X * y ^ 16) :=
    Real.log_le_log hYpos hupper
  have hsplit : Real.log (4 * X * y ^ 16) =
      Real.log 4 + Real.log X + 16 * Real.log y := by
    rw [Real.log_mul (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hX0.ne')
        (pow_ne_zero 16 hy0.ne'),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hX0.ne',
      Real.log_pow]
    ring
  have hlogy : Real.log y ≤ y :=
    (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  dsimp [y] at hlogmono hsplit hy hlogy ⊢
  rw [hsplit] at hlogmono
  nlinarith [log_four_le_two_log hX]

private theorem canonical_J_le
    (hX : 3 ≤ X) :
    (sourceDyadicCount (directTruncation X) : ℝ) ≤
      39 * Real.log X := by
  let M := directTruncation X
  let y := Real.log X
  have hM3 : 3 ≤ M := by simpa [M] using three_le_directTruncation hX
  have hm1 : 0 < M - 1 := by omega
  have hlogb := Real.log2_le_logb (M - 1)
  have hmono : Real.logb 2 ((M - 1 : ℕ) : ℝ) ≤
      Real.logb 2 (M : ℝ) :=
    (Real.logb_le_logb (b := 2) (by norm_num)
      (by exact_mod_cast hm1)
      (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM3))).2
        (by exact_mod_cast (Nat.sub_le M 1))
  have hnatlog : ((M - 1).log2 : ℝ) ≤ Real.logb 2 (M : ℝ) :=
    hlogb.trans hmono
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hinvlog2 : (Real.log 2)⁻¹ ≤ 2 := by
    have hi : (Real.log 2)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
      (inv_le_inv₀ (a := Real.log 2) (b := (1 / 2 : ℝ))
        (Real.log_pos (by norm_num)) (by norm_num)).2 hlog2half
    norm_num at hi ⊢
    exact hi
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM3)
  have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM3.trans' (by norm_num))
  have hlogbBound : Real.logb 2 (M : ℝ) ≤ 2 * Real.log (M : ℝ) := by
    unfold Real.logb
    rw [div_eq_mul_inv]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hinvlog2 hlogM0
  have hMY : (M : ℝ) ≤ directEnergyCeiling X := by
    dsimp [directEnergyCeiling]
    push_cast
    nlinarith
  have hlogMY : Real.log (M : ℝ) ≤ Real.log (directEnergyCeiling X) :=
    Real.log_le_log hMpos hMY
  have hlogY := canonical_log_Y_le hX
  have hy : 1 ≤ y := by simpa [y] using (one_lt_log_of_three_le hX).le
  unfold sourceDyadicCount
  push_cast
  dsimp [y] at hy ⊢
  nlinarith

private theorem harmonic_shell_le
    (hX : 3 ≤ X)
    (j : Fin (sourceDyadicCount (directTruncation X))) :
    (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ≤ 20 * Real.log X := by
  have hNY := sourceShell_le_directEnergyCeiling hX j
  have hNpos : (0 : ℝ) < (2 * 2 ^ (j : ℕ) : ℕ) := by positivity
  have hlogmono : Real.log ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) ≤
      Real.log (directEnergyCeiling X) :=
    Real.log_le_log hNpos hNY
  calc
    (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ≤
        1 + Real.log ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) :=
      harmonic_le_one_add_log _
    _ ≤ 1 + 19 * Real.log X := add_le_add_right
      (hlogmono.trans (canonical_log_Y_le hX)) _
    _ ≤ 20 * Real.log X := by
      have hy := (one_lt_log_of_three_le hX).le
      linarith

private theorem dyadic_shell_scale_le_M
    (hX : 3 ≤ X)
    (j : Fin (sourceDyadicCount (directTruncation X))) :
    ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ directTruncation X := by
  have h := sourceShell_le_directEnergyCeiling hX j
  dsimp [directEnergyCeiling] at h
  push_cast at h ⊢
  linarith

/-- Each canonical source shell has a uniform `X log(X)^20` cost once the
exact shift exponential is bounded by `3`. -/
theorem directSourceShellCost_canonical_le
    (d : ℕ) [NeZero d] {T delta : ℝ}
    (hT : 3 ≤ T)
    (hshift : Real.exp (2 * delta *
      Real.log (directEnergyCeiling (primitiveShiftedScale d T))) ≤ 3)
    (j : Fin (sourceDyadicCount
      (directTruncation (primitiveShiftedScale d T)))) :
    directSourceShellCost d
      (directTruncation (primitiveShiftedScale d T)) T
      (directEnergyCeiling (primitiveShiftedScale d T)) delta j ≤
      32000000 * primitiveShiftedScale d T *
        Real.log (primitiveShiftedScale d T) ^ 20 := by
  let X := primitiveShiftedScale d T
  have hX : 3 ≤ X := by
    dsimp [X, primitiveShiftedScale]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (NeZero.pos d)
    nlinarith
  have hN := dyadic_shell_scale_le_M hX j
  have hM := canonical_M_cast_le hX
  have hh := harmonic_shell_le hX j
  have hy : 1 ≤ Real.log X := (one_lt_log_of_three_le hX).le
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  unfold directSourceShellCost
  change (((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
    Real.exp (2 * delta * Real.log (directEnergyCeiling X)) *
    (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4) ≤ _
  have hfirst : (d : ℝ) * (2 * T) +
      8 * Real.pi * (2 ^ (j : ℕ) : ℕ) ≤
      66 * X * Real.log X ^ 16 := by
    have hscale : (d : ℝ) * (2 * T) = 2 * X := by
      dsimp [X, primitiveShiftedScale]
      ring
    rw [hscale]
    calc
      2 * X + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ) ≤
          2 * X + 32 * (directTruncation X : ℝ) := by
        have h8pi : 8 * Real.pi ≤ 32 := by nlinarith
        have hprod : 8 * Real.pi * ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤
            32 * (directTruncation X : ℝ) :=
          mul_le_mul h8pi hN (by positivity) (by positivity)
        exact add_le_add_right hprod _
      _ ≤ 2 * X + 64 * X * Real.log X ^ 16 := by nlinarith
      _ ≤ 66 * X * Real.log X ^ 16 := by
        have hp : 1 ≤ Real.log X ^ 16 := one_le_pow₀ hy
        nlinarith
  calc
    (((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
      Real.exp (2 * delta * Real.log (directEnergyCeiling X)) *
      (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4) ≤
      (66 * X * Real.log X ^ 16) * 3 *
        (20 * Real.log X) ^ 4 := by
      let A : ℝ := (d : ℝ) * (2 * T) +
        8 * Real.pi * (2 ^ (j : ℕ) : ℕ)
      let E : ℝ := Real.exp (2 * delta * Real.log (directEnergyCeiling X))
      let H : ℝ := (harmonic (2 * 2 ^ (j : ℕ)) : ℝ)
      have hA0 : 0 ≤ A := by dsimp [A]; positivity
      have hB0 : 0 ≤ 66 * X * Real.log X ^ 16 := by positivity
      have hE0 : 0 ≤ E := by dsimp [E]; positivity
      have hH0 : 0 ≤ H := by
        dsimp [H]
        exact_mod_cast (harmonic_pos (by positivity : 2 * 2 ^ (j : ℕ) ≠ 0)).le
      change A * E * H ^ 4 ≤
        (66 * X * Real.log X ^ 16) * 3 * (20 * Real.log X) ^ 4
      calc
        A * E * H ^ 4 ≤ (66 * X * Real.log X ^ 16) * E * H ^ 4 := by
          gcongr
        _ ≤ (66 * X * Real.log X ^ 16) * 3 * H ^ 4 := by
          gcongr
        _ ≤ (66 * X * Real.log X ^ 16) * 3 *
            (20 * Real.log X) ^ 4 := by
          gcongr
    _ = 31680000 * X * Real.log X ^ 20 := by ring
    _ ≤ 32000000 * X * Real.log X ^ 20 := by
      have hnonneg : 0 ≤ X * Real.log X ^ 20 := by positivity
      nlinarith

/-- The literal primitive `S` leaf, completely absorbed under the one scalar
shift-factor bound used by every shell. -/
theorem primitiveFamilyDirectSecondMoment_le_log200
    (d : ℕ) [NeZero d] {T delta sigma : ℝ}
    (hT : 3 ≤ T)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta)
    (hsigma0 : 0 ≤ sigma)
    (hshift : Real.exp (2 * delta *
      Real.log (directEnergyCeiling (primitiveShiftedScale d T))) ≤ 3) :
    primitiveFamilyDirectSecondMoment d T sigma ≤
      200000000000 * ((d : ℝ) * T) *
        Real.log ((d : ℝ) * T) ^ 200 := by
  let X := primitiveShiftedScale d T
  let M := directTruncation X
  let Y := directEnergyCeiling X
  let J := sourceDyadicCount M
  let y := Real.log X
  have hX : 3 ≤ X := by
    dsimp [X, primitiveShiftedScale]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (NeZero.pos d)
    nlinarith
  have hy : 1 ≤ y := by simpa [y] using (one_lt_log_of_three_le hX).le
  have hJ : (J : ℝ) ≤ 39 * y := by
    simpa [J, M, y] using canonical_J_le hX
  have hshell (j : Fin J) :
      directSourceShellCost d M T Y delta j ≤
        32000000 * X * y ^ 20 := by
    simpa [J, M, Y, X, y] using
      directSourceShellCost_canonical_le d hT hshift j
  have hsum : (∑ j : Fin J, directSourceShellCost d M T Y delta j) ≤
      (J : ℝ) * (32000000 * X * y ^ 20) := by
    calc
      (∑ j : Fin J, directSourceShellCost d M T Y delta j) ≤
          ∑ _j : Fin J, (32000000 * X * y ^ 20) :=
        Finset.sum_le_sum fun j hj => hshell j
      _ = (J : ℝ) * (32000000 * X * y ^ 20) := by simp
  have hraw := primitiveFamilyDirectSecondMoment_le_canonicalShells
    d hT hdelta hsigma hsigma0
  dsimp only at hraw
  have hJ0 : 0 ≤ (J : ℝ) := by positivity
  have hX0 : 0 ≤ X := by linarith
  have hcost0 : 0 ≤ 32000000 * X * y ^ 20 := by positivity
  have hsumBound :
      2 * (4 * X + 2 * (J : ℝ) *
        ∑ j : Fin J, directSourceShellCost d M T Y delta j) +
          400 * X * y ^ 200 ≤
        200000000000 * X * y ^ 200 := by
    calc
      2 * (4 * X + 2 * (J : ℝ) *
          ∑ j : Fin J, directSourceShellCost d M T Y delta j) +
          400 * X * y ^ 200 ≤
        2 * (4 * X + 2 * (J : ℝ) *
          ((J : ℝ) * (32000000 * X * y ^ 20))) +
          400 * X * y ^ 200 := by
            gcongr
      _ ≤ 2 * (4 * X + 2 * (39 * y) *
          ((39 * y) * (32000000 * X * y ^ 20))) +
          400 * X * y ^ 200 := by
            gcongr
      _ = 8 * X + 194688000000 * X * y ^ 22 +
          400 * X * y ^ 200 := by ring
      _ ≤ 200000000000 * X * y ^ 200 := by
        have hp22 : y ^ 22 ≤ y ^ 200 :=
          pow_le_pow_right₀ hy (by norm_num)
        have hp0 : 1 ≤ y ^ 200 := one_le_pow₀ hy
        nlinarith [mul_le_mul_of_nonneg_left hp22 hX0]
  have hfour : 4 * (d : ℝ) * T = 4 * X := by
    dsimp [X, primitiveShiftedScale]
    ring
  rw [hfour] at hraw
  have hraw' : primitiveFamilyDirectSecondMoment d T sigma ≤
      2 * (4 * X + 2 * (J : ℝ) *
        ∑ j : Fin J, directSourceShellCost d M T Y delta j) +
          400 * X * y ^ 200 := by
    simpa [M, Y, J, y] using hraw
  exact hraw'.trans (by
    simpa [X, y, primitiveShiftedScale] using hsumBound)


/-- The exact Theorem 6 strip width makes the canonical shell shift factor
smaller than `3`, uniformly for every inducing conductor `d ∣ q`. -/
theorem canonical_shift_factor_le_three
    (q d : ℕ) [NeZero q] [NeZero d]
    {T delta : ℝ} (hdq : d ∣ q) (hT : 3 ≤ T)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ (100 * Real.log ((q : ℝ) * T))⁻¹) :
    Real.exp (2 * delta *
      Real.log (directEnergyCeiling (primitiveShiftedScale d T))) ≤ 3 := by
  let X := primitiveShiftedScale d T
  let R : ℝ := (q : ℝ) * T
  have hdle : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdq
  have hX : 3 ≤ X := by
    dsimp [X, primitiveShiftedScale]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (NeZero.pos d)
    nlinarith
  have hR : 3 ≤ R := by
    dsimp [R]
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    nlinarith
  have hXR : X ≤ R := by
    dsimp [X, R, primitiveShiftedScale]
    have hdr : (d : ℝ) ≤ q := by exact_mod_cast hdle
    exact mul_le_mul_of_nonneg_right hdr (by linarith)
  have hlogXR : Real.log X ≤ Real.log R :=
    Real.log_le_log (by linarith) hXR
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogY := canonical_log_Y_le hX
  have hlogY0 : 0 ≤ Real.log (directEnergyCeiling X) := by
    apply Real.log_nonneg
    dsimp [directEnergyCeiling]
    have hM := three_le_directTruncation hX
    exact_mod_cast (by omega : 1 ≤ 2 * directTruncation X)
  have hdelta' : delta ≤ 1 / (100 * Real.log R) := by
    simpa [R, one_div] using hdelta
  have hprod : 2 * delta * Real.log (directEnergyCeiling X) ≤
      38 / 100 := by
    have hdenpos : 0 < 100 * Real.log R := by positivity
    calc
      2 * delta * Real.log (directEnergyCeiling X) ≤
          2 * (1 / (100 * Real.log R)) *
            (19 * Real.log X) := by gcongr
      _ ≤ 2 * (1 / (100 * Real.log R)) *
            (19 * Real.log R) := by gcongr
      _ = 38 / 100 := by field_simp; ring
  calc
    Real.exp (2 * delta *
        Real.log (directEnergyCeiling (primitiveShiftedScale d T))) =
      Real.exp (2 * delta * Real.log (directEnergyCeiling X)) := by rfl
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (hprod.trans (by norm_num))
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- Fully source-shaped primitive `S` budget for the exact shifted strip. -/
theorem primitiveFamilyDirectSecondMoment_le_log200_of_sourceStrip
    (q d : ℕ) [NeZero q] [NeZero d]
    {T delta sigma : ℝ} (hdq : d ∣ q) (hT : 3 ≤ T)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ (100 * Real.log ((q : ℝ) * T))⁻¹)
    (hsigma : |sigma - 1 / 2| ≤ delta)
    (hsigma0 : 0 ≤ sigma) :
    primitiveFamilyDirectSecondMoment d T sigma ≤
      200000000000 * ((d : ℝ) * T) *
        Real.log ((d : ℝ) * T) ^ 200 := by
  exact primitiveFamilyDirectSecondMoment_le_log200 d hT hdelta0 hsigma hsigma0
    (canonical_shift_factor_le_three q d hdq hT hdelta0 hdelta)


end
end RamachandraShiftedDirectShellAbsorption

#print axioms RamachandraShiftedDirectShellAbsorption.directSourceShellCost_canonical_le
#print axioms RamachandraShiftedDirectShellAbsorption.primitiveFamilyDirectSecondMoment_le_log200
#print axioms RamachandraShiftedDirectShellAbsorption.primitiveFamilyDirectSecondMoment_le_log200_of_sourceStrip
