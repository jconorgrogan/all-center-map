import GuthMaynardGMKernelCorrelation

namespace GuthMaynardGMGlobalHighScalar

theorem time_ratio_min_bound {T S : ℝ} (hT : 0 < T) (hS : 0 < S) :
    T / min T S + 1 ≤ T / S + 2 := by
  by_cases hTS : T ≤ S
  · rw [min_eq_left hTS, div_self hT.ne']
    have : 0 ≤ T / S := by positivity
    linarith
  · rw [min_eq_right (le_of_not_ge hTS)]
    linarith

theorem global_high_scalar {N V T A R : ℝ}
    (hN : 0 < N) (hV : 0 < V) (hT : 1 ≤ T) (hA : 1 ≤ A)
    (hR : R ≤ (T / min T (V ^ 4 / (A ^ 2 * N ^ 2)) + 1) *
      (9600 * N ^ 2 * Real.log (2 * min T (V ^ 4 / (A ^ 2 * N ^ 2))) / V ^ 2)) :
    R ≤ 19200 * A ^ 2 * Real.log (2 * T) *
      (N ^ 2 / V ^ 2 + T * N ^ 4 / V ^ 6) := by
  have hT0 : 0 < T := by linarith
  have hA0 : 0 < A := by linarith
  let S : ℝ := V ^ 4 / (A ^ 2 * N ^ 2)
  let L : ℝ := min T S
  have hS : 0 < S := by dsimp [S]; positivity
  have hL : 0 < L := lt_min hT0 hS
  have hLT : L ≤ T := min_le_left _ _
  have hlog : Real.log (2 * L) ≤ Real.log (2 * T) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogT : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hratio := time_ratio_min_bound hT0 hS
  have hfac : 0 ≤ T / L + 1 := by positivity
  have hlocal : 9600 * N ^ 2 * Real.log (2 * L) / V ^ 2 ≤
      9600 * N ^ 2 * Real.log (2 * T) / V ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg V)
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hbound : R ≤ (T / S + 2) * (9600 * N ^ 2 * Real.log (2 * T) / V ^ 2) := by
    calc
      R ≤ (T / L + 1) * (9600 * N ^ 2 * Real.log (2 * L) / V ^ 2) := hR
      _ ≤ (T / L + 1) * (9600 * N ^ 2 * Real.log (2 * T) / V ^ 2) :=
        mul_le_mul_of_nonneg_left hlocal hfac
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)
  have heq : (T / S + 2) * (9600 * N ^ 2 * Real.log (2 * T) / V ^ 2) =
      Real.log (2 * T) * (19200 * (N ^ 2 / V ^ 2) +
        9600 * A ^ 2 * (T * N ^ 4 / V ^ 6)) := by
    dsimp [S]
    field_simp
    ring
  rw [heq] at hbound
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hx : 0 ≤ N ^ 2 / V ^ 2 := by positivity
  have hy : 0 ≤ T * N ^ 4 / V ^ 6 := by positivity
  have hfirst := mul_le_mul_of_nonneg_right hA2 hx
  have hinner : 19200 * (N ^ 2 / V ^ 2) +
      9600 * A ^ 2 * (T * N ^ 4 / V ^ 6) ≤
      19200 * A ^ 2 * (N ^ 2 / V ^ 2 + T * N ^ 4 / V ^ 6) := by
    nlinarith [mul_nonneg (sq_nonneg A) hy]
  calc
    R ≤ _ := hbound
    _ ≤ Real.log (2 * T) *
        (19200 * A ^ 2 * (N ^ 2 / V ^ 2 + T * N ^ 4 / V ^ 6)) :=
      mul_le_mul_of_nonneg_left hinner hlogT
    _ = _ := by ring


theorem log_two_mul_le_rpow {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta) :
    Real.log (2 * T) ≤ (Real.log 2 + 1 / eta) * Real.rpow T eta := by
  have hTp : 0 < T := by linarith
  have hp : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta.le
  have hl := Real.log_le_rpow_div hTp.le heta
  change Real.log T ≤ Real.rpow T eta / eta at hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTp.ne']
  have hh := mul_le_mul_of_nonneg_left hp (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  calc
    Real.log 2 + Real.log T ≤ Real.log 2 * Real.rpow T eta + Real.rpow T eta / eta := by linarith
    _ = _ := by ring

theorem high_classical_terms_le_gm {N V T : ℝ} (hN : 0 < N) (hV : 0 < V)
    (hT : 0 ≤ T) (hhigh : Real.rpow N (4 / 5 : ℝ) ≤ V) :
    N ^ 2 / V ^ 2 + T * N ^ 4 / V ^ 6 ≤
      N ^ 2 / V ^ 2 + Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
        T * Real.rpow N (12 / 5 : ℝ) / V ^ 4 := by
  have hs := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hhigh 2
  change (Real.rpow N (4 / 5 : ℝ)) ^ (2 : ℕ) ≤ V ^ (2 : ℕ) at hs
  have hpow : Real.rpow N (4 / 5 : ℝ) ^ (2 : ℕ) = Real.rpow N (8 / 5 : ℝ) := by
    calc
      _ = Real.rpow (Real.rpow N (4 / 5 : ℝ)) (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = Real.rpow N ((4 / 5 : ℝ) * 2) := (Real.rpow_mul hN.le _ _).symm
      _ = _ := by norm_num
  rw [hpow] at hs
  have hfactor : Real.rpow N (12 / 5 : ℝ) * Real.rpow N (8 / 5 : ℝ) = N ^ 4 := by
    calc
      _ = Real.rpow N ((12 / 5 : ℝ) + 8 / 5) := (Real.rpow_add hN _ _).symm
      _ = Real.rpow N (4 : ℝ) := by norm_num
      _ = _ := Real.rpow_natCast N 4
  have hh := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hN.le (12 / 5 : ℝ))
  change Real.rpow N (12 / 5 : ℝ) * Real.rpow N (8 / 5 : ℝ) ≤ Real.rpow N (12 / 5 : ℝ) * V ^ (2 : ℕ) at hh
  rw [hfactor] at hh
  have hdiv : N ^ 4 / V ^ 6 ≤ Real.rpow N (12 / 5 : ℝ) / V ^ 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have ht := mul_le_mul_of_nonneg_right hh (show 0 ≤ V ^ 4 by positivity)
    convert ht using 1 <;> ring
  have ht := mul_le_mul_of_nonneg_left hdiv hT
  have hm : 0 ≤ Real.rpow N (18 / 5 : ℝ) / V ^ 4 :=
    div_nonneg (Real.rpow_nonneg hN.le _) (pow_nonneg hV.le _)
  calc
    N ^ 2 / V ^ 2 + T * N ^ 4 / V ^ 6 = N ^ 2 / V ^ 2 + T * (N ^ 4 / V ^ 6) := by ring
    _ ≤ N ^ 2 / V ^ 2 + T * (Real.rpow N (12 / 5 : ℝ) / V ^ 4) := by linarith
    _ ≤ _ := by rw [mul_div_assoc]; linarith

end GuthMaynardGMGlobalHighScalar
#print axioms GuthMaynardGMGlobalHighScalar.global_high_scalar
#print axioms GuthMaynardGMGlobalHighScalar.log_two_mul_le_rpow
#print axioms GuthMaynardGMGlobalHighScalar.high_classical_terms_le_gm
