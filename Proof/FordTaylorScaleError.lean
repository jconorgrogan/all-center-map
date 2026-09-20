import FordNextDegreeEnvelope

noncomputable section
namespace FordTaylorScaleError

open FordWEnvelopeScalar FordNextDegreeEnvelope

lemma scale_product_le {N M1 M2 : ℕ} (hN : 1 ≤ N)
    (hM1 : (M1 : ℝ) ≤ (N : ℝ) ^ mu1)
    (hM2 : (M2 : ℝ) ≤ (N : ℝ) ^ mu2) :
    ((M1 * M2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (mu1 + mu2) := by
  have hprod := mul_le_mul hM1 hM2 (by positivity) (by positivity)
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  calc
    ((M1 * M2 : ℕ) : ℝ) = (M1 : ℝ) * (M2 : ℝ) := by norm_num
    _ ≤ (N : ℝ) ^ mu1 * (N : ℝ) ^ mu2 := hprod
    _ = (N : ℝ) ^ (mu1 + mu2) := by
      rw [← Real.rpow_add hn0]

theorem two_scale_product_le {N M1 M2 : ℕ} (hN : 1 ≤ N)
    (hM1 : (M1 : ℝ) ≤ (N : ℝ) ^ mu1)
    (hM2 : (M2 : ℝ) ≤ (N : ℝ) ^ mu2) :
    2 * ((M1 * M2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (mu1 + mu2) := by
  exact mul_le_mul_of_nonneg_left (scale_product_le hN hM1 hM2) (by norm_num)

theorem taylor_error_le {N M1 M2 : ℕ} {lam : ℝ}
    (hN : 1 ≤ N)
    (hM1 : (M1 : ℝ) ≤ (N : ℝ) ^ mu1)
    (hM2 : (M2 : ℝ) ≤ (N : ℝ) ^ mu2)
    (hlam : 2000 * b ≤ lam) :
    let k := Nat.floor (lam / b) + 1
    (N : ℝ) ^ lam *
        (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) /
          (k + 1) ≤ (N : ℝ) ^ (-b) := by
  let k : ℕ := Nat.floor (lam / b) + 1
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hD := scale_product_le hN hM1 hM2
  have hratio :
      ((M1 * M2 : ℕ) : ℝ) / (N : ℝ) ≤
        (N : ℝ) ^ (mu1 + mu2 - 1) := by
    apply (div_le_iff₀ hn0).2
    calc
      ((M1 * M2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (mu1 + mu2) := hD
      _ = (N : ℝ) ^ (mu1 + mu2 - 1) * (N : ℝ) := by
        symm
        calc
          (N : ℝ) ^ (mu1 + mu2 - 1) * (N : ℝ) =
              (N : ℝ) ^ (mu1 + mu2 - 1) * (N : ℝ) ^ (1 : ℝ) := by
                rw [Real.rpow_one]
          _ = (N : ℝ) ^ ((mu1 + mu2 - 1) + 1) := by
                rw [← Real.rpow_add hn0]
          _ = (N : ℝ) ^ (mu1 + mu2) := by congr 1 <;> ring
  have hratio0 : 0 ≤ ((M1 * M2 : ℕ) : ℝ) / (N : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hratio0 hratio (k + 1)
  have hnum :
      (N : ℝ) ^ lam *
          (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) ≤
        (N : ℝ) ^ (-b) := by
    have hmul := mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ (N : ℝ) ^ lam)
    have hnext : lam - b * ((k : ℝ) + 1) < -b := by
      simpa [k] using
        (FordNextDegreeEnvelope.floor_next_degree_taylor_exponent hlam)
    have hmu : mu1 + mu2 - 1 = -b := by norm_num [mu1, mu2, b]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
    have hexp : lam + (mu1 + mu2 - 1) * ((k + 1 : ℕ) : ℝ) < -b := by
      rw [hmu, hcast]
      nlinarith [hnext]
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpowexp := Real.rpow_le_rpow_of_exponent_le
      hNreal (le_of_lt hexp)
    calc
      (N : ℝ) ^ lam *
          (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) ≤
          (N : ℝ) ^ lam * (N : ℝ) ^ ((mu1 + mu2 - 1) * ((k + 1 : ℕ) : ℝ)) := by
            calc
              _ ≤ (N : ℝ) ^ lam *
                  ((N : ℝ) ^ (mu1 + mu2 - 1)) ^ (k + 1) := hmul
              _ = _ := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      _ = (N : ℝ) ^ (lam + (mu1 + mu2 - 1) * ((k + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hn0]
      _ ≤ (N : ℝ) ^ (-b) := hpowexp
  change (N : ℝ) ^ lam *
      (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) /
        (k + 1) ≤ (N : ℝ) ^ (-b)
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hnum
    (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ))
  have hfinal :
      (N : ℝ) ^ lam *
          (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) /
            ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (-b) := by
    calc
      (N : ℝ) ^ lam *
          (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) /
            ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (-b) / ((k + 1 : ℕ) : ℝ) := hdiv
      _ ≤ (N : ℝ) ^ (-b) := by
        apply (div_le_iff₀ hkpos).2
        have hone : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          exact_mod_cast (show 1 ≤ k + 1 by omega)
        have hA : 0 ≤ (N : ℝ) ^ (-b) := by positivity
        calc
          (N : ℝ) ^ (-b) = (N : ℝ) ^ (-b) * 1 := by ring
          _ ≤ (N : ℝ) ^ (-b) * ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hone hA
          _ = (N : ℝ) ^ (-b) * ((k + 1 : ℕ) : ℝ) := by norm_num
  simpa only [Nat.cast_add, Nat.cast_one] using hfinal

end FordTaylorScaleError

#print axioms FordTaylorScaleError.two_scale_product_le
#print axioms FordTaylorScaleError.taylor_error_le
