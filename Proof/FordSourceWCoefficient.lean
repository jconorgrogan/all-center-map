import FordSourceWEnvelope

open FordSourceWEnvelope

namespace FordSourceWCoefficient
noncomputable section

theorem coeff_le {R j : ℕ} (hR : 1 ≤ R) (hj : 1 ≤ j) :
    coeff R j ≤ 32 * (R : ℝ) * (j + 1) * (4 : ℝ) ^ j := by
  have hR0 : 0 < (R : ℝ) := by positivity
  have hj0 : 0 < (j : ℝ) := by positivity
  have hj1 : 1 ≤ (j : ℝ) + 1 := by linarith
  have hpow4 : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hpow2 : 0 ≤ (2 : ℝ) ^ j := by positivity
  have hpi_lo : 1 ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hpi_hi : Real.pi ≤ 4 := Real.pi_le_four
  let Q : ℝ := (R : ℝ) * ((j : ℝ) + 1) * (4 : ℝ) ^ j
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have h1 : 2 * (R : ℝ) ≤ 2 * Q := by
    dsimp [Q]
    have hprod : 1 ≤ ((j : ℝ) + 1) * (4 : ℝ) ^ j := by nlinarith
    nlinarith
  have h2 : (2 : ℝ) ^ (j + 1) ≤ 2 * Q := by
    dsimp [Q]
    rw [pow_succ]
    have hRone : 1 ≤ (R : ℝ) := by exact_mod_cast hR
    have hbase : (2 : ℝ) ^ j ≤ (4 : ℝ) ^ j := by
      exact pow_le_pow_left₀ (by positivity) (by norm_num) j
    have hp : (2 : ℝ) ^ j ≤
        (R : ℝ) * ((j : ℝ) + 1) * (4 : ℝ) ^ j := by
      calc
        (2 : ℝ) ^ j ≤ (4 : ℝ) ^ j := hbase
        _ ≤ (R : ℝ) * ((j : ℝ) + 1) * (4 : ℝ) ^ j := by
          have hf : 1 ≤ (R : ℝ) * ((j : ℝ) + 1) := by
            have hmul := mul_le_mul (show 1 ≤ (R : ℝ) by exact_mod_cast hR)
              hj1 (by positivity) (by positivity)
            simpa using hmul
          have := mul_le_mul_of_nonneg_right hf (show 0 ≤ (4 : ℝ)^j by positivity)
          simpa using this
    nlinarith
  have h3 : (R : ℝ) / (Real.pi * (j : ℝ)) ≤ Q := by
    have hden : 1 ≤ Real.pi * (j : ℝ) := by
      have hjreal : 1 ≤ (j : ℝ) := by exact_mod_cast hj
      have hprod := mul_le_mul hpi_lo le_rfl (by positivity) (by positivity)
      nlinarith [hprod, hjreal]
    have hdiv : (R : ℝ) / (Real.pi * (j : ℝ)) ≤ (R : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    exact hdiv.trans (by
      dsimp [Q]
      nlinarith [hpow4])
  have h4 : 4 * Real.pi * (j : ℝ) * (4 : ℝ) ^ j / (R : ℝ) ≤ 16 * Q := by
    have hpi4 : 4 * Real.pi ≤ (16 : ℝ) := by nlinarith [hpi_hi]
    have hjR : (j : ℝ) ≤ (R : ℝ) * ((j : ℝ) + 1) := by
      have hRone : 1 ≤ (R : ℝ) := by exact_mod_cast hR
      nlinarith
    have hnum : 4 * Real.pi * (j : ℝ) * (4 : ℝ) ^ j ≤
        16 * (R : ℝ) * ((j : ℝ) + 1) * (4 : ℝ) ^ j := by
      calc
        4 * Real.pi * (j : ℝ) * (4 : ℝ) ^ j ≤
            16 * (j : ℝ) * (4 : ℝ) ^ j := by
              gcongr
        _ ≤ 16 * (R : ℝ) * ((j : ℝ) + 1) * (4 : ℝ) ^ j := by
              have hh := mul_le_mul_of_nonneg_right hjR
                (show 0 ≤ 16 * (4 : ℝ)^j by positivity)
              nlinarith
    apply (div_le_iff₀ hR0).mpr
    dsimp [Q]
    have hQmul : 16 * Q ≤ 16 * Q * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_left (show 1 ≤ (R : ℝ) by exact_mod_cast hR)
        (by positivity : 0 ≤ 16 * Q)
      nlinarith
    nlinarith [hnum, hQmul]
  have h5 : (2 : ℝ) ≤ 2 * Q := by
    dsimp [Q]
    have hprod : 1 ≤ (R : ℝ) * ((j : ℝ) + 1) * (4 : ℝ) ^ j := by
      have hf : 1 ≤ (R : ℝ) * ((j : ℝ) + 1) := by
        have hmul := mul_le_mul (show 1 ≤ (R : ℝ) by exact_mod_cast hR)
          hj1 (by positivity) (by positivity)
        simpa using hmul
      have := mul_le_mul_of_nonneg_right hf (show 0 ≤ (4 : ℝ)^j by positivity)
      nlinarith
    nlinarith
  unfold coeff
  dsimp [Q] at h1 h2 h3 h4 h5 ⊢
  nlinarith

end
end FordSourceWCoefficient

#print axioms FordSourceWCoefficient.coeff_le
