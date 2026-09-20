import GuthMaynardS3ActualProfileInputs

noncomputable section
namespace GuthMaynardS3FirstPoissonAbsorption

theorem firstPoisson_scalar_absorption
    {T eta M M1 M2 C H L vol : ℝ}
    (hT : 1 ≤ T) (heta : 0 ≤ eta) (hM : 1 ≤ M)
    (hM1 : 0 < M1) (hM2 : 0 ≤ M2) (hM2M : M2 ≤ M)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hvol : 0 ≤ vol) (hvolUpper : vol ≤ 2 * T ^ 6)
    (hinner : H ≤ 6 * M2 ^ 2 / M1 * L) :
    2 * vol * ((C / T ^ 100) * (4 * M1 * H)) ^ 2 ≤
      2304 * C ^ 2 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hinter : 4 * M1 * H ≤ 24 * M2 ^ 2 * L := by
    have hx := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 4 * M1)
    calc
      4 * M1 * H ≤ 4 * M1 * (6 * M2 ^ 2 / M1 * L) := hx
      _ = 24 * M2 ^ 2 * L := by field_simp; ring
  have hpow : T ^ (6 : ℕ) ≤ T ^ (200 : ℕ) :=
    pow_le_pow_right₀ hT (by norm_num)
  have hratio : vol / T ^ 200 ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < T ^ (200 : ℕ))).2
    exact hvolUpper.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hMpow : M2 ^ (4 : ℕ) ≤ M ^ (6 : ℕ) :=
    (pow_le_pow_left₀ hM2 hM2M 4).trans (pow_le_pow_right₀ hM (by norm_num))
  have hTp : 1 ≤ Real.rpow T (3 * eta) :=
    Real.one_le_rpow hT (by positivity)
  calc
    2 * vol * ((C / T ^ 100) * (4 * M1 * H)) ^ 2 ≤
        2 * vol * ((C / T ^ 100) * (24 * M2 ^ 2 * L)) ^ 2 := by
      gcongr
    _ = (1152 * C ^ 2 * M2 ^ 4 * L ^ 2) * (vol / T ^ 200) := by
      field_simp
      ring
    _ ≤ (1152 * C ^ 2 * M2 ^ 4 * L ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2304 * C ^ 2 * M2 ^ 4 * L ^ 2 := by ring
    _ ≤ 2304 * C ^ 2 * M ^ 6 * L ^ 2 := by gcongr
    _ ≤ 2304 * C ^ 2 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2304 * C ^ 2 * M ^ 6 * L ^ 2)
        (sub_nonneg.mpr hTp)]

end GuthMaynardS3FirstPoissonAbsorption
end

#print axioms GuthMaynardS3FirstPoissonAbsorption.firstPoisson_scalar_absorption
