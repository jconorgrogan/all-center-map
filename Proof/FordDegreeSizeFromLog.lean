import FordDegreeScaleBounds

noncomputable section
namespace FordDegreeSizeFromLog

open FordWEnvelopeScalar FordDegreeScaleBounds

/-- The logarithmic size hypothesis already forces the finite moment order to
fit inside the ambient natural scale. -/
theorem degree_size_from_log
    {N k : ℕ} {lam : ℝ}
    (hN : 2 ≤ N)
    (hdegree : k = Nat.floor (lam / b) + 1)
    (hlam : 2000 * b ≤ lam)
    (hlog : 256000000000000 * lam ^ 4 ≤ Real.log (N : ℝ)) :
    1024 * (k + 1) ^ 2 ≤ N := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlam1 : (1 : ℝ) ≤ lam := by
    norm_num [b] at hlam ⊢
    linarith
  have hkdeg : (k : ℝ) ≤ 4 * lam := by
    simpa only [hdegree] using (degree_le_four_lam hlam)
  have hkplus : (k : ℝ) + 1 ≤ 5 * lam := by
    nlinarith
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ (5 * lam) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hkplus 2
  have hsq' : (1024 : ℝ) * ((k : ℝ) + 1) ^ 2 ≤
      (25600 : ℝ) * lam ^ 2 := by
    nlinarith [hsq]
  have hlam_pow : lam ^ 2 ≤ lam ^ 4 := by
    exact pow_le_pow_right₀ hlam1 (by norm_num)
  have hconst : (25600 : ℝ) * lam ^ 2 ≤
      256000000000000 * lam ^ 4 := by
    have hnonneg : 0 ≤ lam ^ 2 := by positivity
    nlinarith [hlam_pow]
  have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hstrong : (25600 : ℝ) * lam ^ 2 ≤ (N : ℝ) :=
    hconst.trans (hlog.trans hlogN)
  have hpoly : (1024 : ℝ) * ((k : ℝ) + 1) ^ 2 ≤ (N : ℝ) :=
    hsq'.trans hstrong
  exact_mod_cast hpoly

end FordDegreeSizeFromLog

#print axioms FordDegreeSizeFromLog.degree_size_from_log
