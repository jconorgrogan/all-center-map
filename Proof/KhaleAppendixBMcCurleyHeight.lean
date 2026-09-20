import KhaleAppendixBSourceReduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The McCurley height reduction inside Khale Appendix B.1

Khale first uses McCurley's real-exception theorem to show that a nonreal zero
at ordinate `gamma ≥ exp 10650` must satisfy
`gamma ≥ q^(1/100000)`.  This file certifies that reduction with McCurley's
exact published scale and constant.
-/

namespace MAPKhaleAppendixBMcCurleyHeight

open MAPKhaleAppendixBSource MAPMcCurleyHighImaginaryBridge

noncomputable section

private theorem mccurleyScale_eq_mul
    {q : ℕ} {gamma : ℝ} (hq : 3 ≤ q)
    (hgamma : Real.exp 10650 ≤ gamma) :
    mccurleyScale q gamma = (q : ℝ) * gamma := by
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hgammaOne : (1 : ℝ) ≤ gamma := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 10650)).trans hgamma
  have hqmul : (q : ℝ) ≤ (q : ℝ) * gamma := by nlinarith
  have hten : (10 : ℝ) ≤ (q : ℝ) * gamma := by
    have hexp3 : (4 : ℝ) ≤ Real.exp 3 := by
      have h := Real.add_one_le_exp (3 : ℝ)
      norm_num at h ⊢
      exact h
    have hexp : (4 : ℝ) ≤ Real.exp 10650 :=
      hexp3.trans (Real.exp_le_exp.mpr (by norm_num))
    nlinarith
  unfold mccurleyScale
  rw [abs_of_pos (lt_of_lt_of_le (by norm_num) hgammaOne)]
  rw [max_eq_right hqmul, max_eq_left hten]

/-- Exact use of McCurley in the first paragraph of the proof of Khale's
Theorem B.1.  The decimal calculation is made against the actual published
constant `9.645908801`, rather than the downward rounding in Khale's display.
-/
theorem q_rpow_one_over_100000_le_ordinate_of_zero
    (hMcCurley : McCurleyTheorem11RealException)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {gamma beta : ℝ} (hq : 3 ≤ q)
    (hgamma : Real.exp 10650 ≤ gamma)
    (hbetaGap : 1 - beta ≤ 1 / (18 * Real.log q))
    (hzero : DirichletCharacter.LFunction chi
      ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0) :
    Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ gamma := by
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := by linarith
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 3).trans_le hqReal)
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma
  by_contra hnot
  have hgammaLt : gamma < Real.rpow (q : ℝ) (1 / 100000 : ℝ) :=
    lt_of_not_ge hnot
  have hloggammaLt : Real.log gamma <
      (1 / 100000 : ℝ) * Real.log q := by
    calc
      Real.log gamma < Real.log (Real.rpow (q : ℝ) (1 / 100000 : ℝ)) :=
        Real.log_lt_log hgammaPos hgammaLt
      _ = (1 / 100000 : ℝ) * Real.log q := Real.log_rpow hqPos _
  have hscale : mccurleyScale q gamma = (q : ℝ) * gamma :=
    mccurleyScale_eq_mul hq hgamma
  have hlogscale : Real.log (mccurleyScale q gamma) =
      Real.log q + Real.log gamma := by
    rw [hscale, Real.log_mul hqPos.ne' hgammaPos.ne']
  have hdenLt : publishedR * Real.log (mccurleyScale q gamma) <
      18 * Real.log q := by
    rw [hlogscale]
    dsimp [publishedR]
    nlinarith
  have hdenPos : 0 < publishedR * Real.log (mccurleyScale q gamma) :=
    mul_pos (by norm_num [publishedR]) (log_mccurleyScale_pos q gamma)
  have h18Pos : 0 < 18 * Real.log q := mul_pos (by norm_num) hlogqPos
  have hinv : 1 / (18 * Real.log q) <
      1 / (publishedR * Real.log (mccurleyScale q gamma)) :=
    one_div_lt_one_div_of_lt hdenPos hdenLt
  have hregion : mccurleyBoundary publishedR q gamma < beta := by
    dsimp [mccurleyBoundary]
    linarith
  have him := hMcCurley q chi
    ((beta : ℂ) + (gamma : ℂ) * Complex.I) (by simpa using hregion) hzero
  have : gamma = 0 := by simpa using him
  linarith

end
end MAPKhaleAppendixBMcCurleyHeight

#print axioms MAPKhaleAppendixBMcCurleyHeight.q_rpow_one_over_100000_le_ordinate_of_zero
