import GuthMaynardS3LiteralSelectionLedger

open scoped Real
noncomputable section
namespace GuthMaynardS3DyadicLogLoss

/-- Literal bin multiplicity when the source cutoff is at most T². -/
theorem dyadic_bin_log_bound {T : ℝ} (hT : 1 ≤ T) {k : ℕ}
    (hK : (2 : ℝ)^k ≤ T^2) :
    (k : ℝ)+7 ≤ (7+2/Real.log 2)*(1+Real.log T) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2^k) hK
  simp only [Real.log_pow] at hh
  have hk : (k : ℝ) ≤ 2*Real.log T/Real.log 2 :=
    (le_div_iff₀ hlog2).2 hh
  rw [show 2*Real.log T/Real.log 2 = (2/Real.log 2)*Real.log T by ring] at hk
  have hc : 0 ≤ 2/Real.log 2 := by positivity
  nlinarith

theorem shifted_log_cube_le_rpow {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta) :
    (1+Real.log T)^3 ≤ (1+3/eta)^3*T^eta := by
  have hTp : 0 < T := by linarith
  have hlog0 := Real.log_nonneg hT
  have hp : 1 ≤ T^(eta/3) := Real.one_le_rpow hT (by positivity)
  have hl := Real.log_le_rpow_div hTp.le (by positivity : 0 < eta/3)
  have hdiv : T^(eta/3)/(eta/3) = (3/eta)*T^(eta/3) := by ring
  rw [hdiv] at hl
  have hbound : 1+Real.log T ≤ (1+3/eta)*T^(eta/3) := by nlinarith
  have hpower : (T^(eta/3))^3 = T^eta := by
    rw [← Real.rpow_natCast (T^(eta/3)) 3, ← Real.rpow_mul hTp.le]
    congr 1
    ring
  calc
    (1+Real.log T)^3 ≤ ((1+3/eta)*T^(eta/3))^3 :=
      pow_le_pow_left₀ (by linarith) hbound 3
    _ = (1+3/eta)^3*T^eta := by rw [mul_pow, hpower]

theorem selection_and_bin_log_loss {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    {k : ℕ} (hK : (2 : ℝ)^k ≤ T^2) :
    (1+Real.log T)^2*((k : ℝ)+7) ≤
      ((7+2/Real.log 2)*(1+3/eta)^3)*T^eta := by
  have hC : 0 ≤ 7+2/Real.log 2 := by
    have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hb := mul_le_mul_of_nonneg_left (dyadic_bin_log_bound hT hK)
    (sq_nonneg (1+Real.log T))
  have hl := mul_le_mul_of_nonneg_left (shifted_log_cube_le_rpow hT heta) hC
  nlinarith

end GuthMaynardS3DyadicLogLoss
#print axioms GuthMaynardS3DyadicLogLoss.dyadic_bin_log_bound
#print axioms GuthMaynardS3DyadicLogLoss.shifted_log_cube_le_rpow
#print axioms GuthMaynardS3DyadicLogLoss.selection_and_bin_log_loss
