import ZeroFreeSiegelSpine
import KhaleAppendixBTrigPolynomialCertified

/-!
# The Appendix-B trigonometric polynomial at the logarithmic derivative

This file certifies the Euler-product positivity used immediately before
Khale's Appendix-B display `(firstpart)`.  It is independent of Khale's
Lemma 4.1: the only analytic input is absolute convergence on `Re s > 1`,
already available in Mathlib.
-/

namespace MAPKhaleAppendixBTrigLogDerivativeCertified

open MAPZeroFreeSiegelSpine
open MAPKhaleAppendixBTrigPolynomialCertified
open PrimitiveExplicitFormulaSpine
open scoped BigOperators ArithmeticFunction LSeries.notation

noncomputable section

/-- Positive powers of the oscillatory character phase are the phases of the
corresponding character powers at the multiplied ordinate. -/
theorem characterPhase_pow_of_pos {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℝ) (n j : ℕ) (hj : j ≠ 0) :
    characterPhase (chi ^ j) ((j : ℝ) * t) n =
      (characterPhase chi t n) ^ j := by
  simp only [characterPhase, chi.pow_apply' hj]
  rw [mul_pow]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem re_pow_of_exp_mul_I
    {z : ℂ} {theta : ℝ} (hz : Complex.exp ((theta : ℂ) * Complex.I) = z)
    (j : ℕ) :
    (z ^ j).re = Real.cos ((j : ℝ) * theta) := by
  have hpow : z ^ j =
      Complex.exp ((((j : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
    Complex.sin_ofReal_re, Complex.I_re, Complex.I_im, mul_zero,
    Complex.sin_ofReal_im, mul_one, sub_zero]
  ring

/-- The literal five-term Mangoldt coefficient is nonnegative.  The proof
handles bad residue classes separately; on a unit the character phase lies
on the unit circle and equation (5.1) applies with its actual angle. -/
theorem appendixB_characterPhase_polynomial_nonneg {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    0 ≤ 10.01055 + 17.145 * (characterPhase chi t n).re +
      10.6825 * ((characterPhase chi t n) ^ 2).re +
      4.5 * ((characterPhase chi t n) ^ 3).re +
      ((characterPhase chi t n) ^ 4).re := by
  let z : ℂ := characterPhase chi t n
  change 0 ≤ 10.01055 + 17.145 * z.re + 10.6825 * (z ^ 2).re +
    4.5 * (z ^ 3).re + (z ^ 4).re
  by_cases hz : z = 0
  · rw [hz]
    norm_num
  have hunit : IsUnit (n : ZMod q) := by
    by_contra hnot
    have hz0 : z = 0 := by
      dsimp [z, characterPhase]
      rw [chi.map_nonunit hnot, zero_mul]
    exact hz hz0
  have hnorm : ‖z‖ = 1 := by
    dsimp [z, characterPhase]
    rw [norm_mul]
    have hchi : ‖chi (n : ZMod q)‖ = 1 := by
      simpa only [hunit.unit_spec] using chi.unit_norm_eq_one hunit.unit
    rw [hchi, Complex.norm_exp_ofReal_mul_I, mul_one]
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff z).mp hnorm
  have h1 : z.re = Real.cos theta := by
    simpa using re_pow_of_exp_mul_I htheta 1
  have h2 : (z ^ 2).re = Real.cos (2 * theta) := by
    simpa using re_pow_of_exp_mul_I htheta 2
  have h3 : (z ^ 3).re = Real.cos (3 * theta) := by
    simpa using re_pow_of_exp_mul_I htheta 3
  have h4 : (z ^ 4).re = Real.cos (4 * theta) := by
    simpa using re_pow_of_exp_mul_I htheta 4
  change 0 ≤ 10.01055 + 17.145 * z.re +
    10.6825 * (z ^ 2).re + 4.5 * (z ^ 3).re + (z ^ 4).re
  rw [h1, h2, h3, h4]
  exact appendixB_trigonometric_nonneg theta

/-- The five absolutely convergent Mangoldt series satisfy Khale's exact
`b0,...,b4` real-part inequality. -/
theorem appendixB_LSeries_re_nonneg {q : ℕ}
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hsigma : 1 < sigma)
    (t : ℝ) :
    0 ≤
      10.01055 * (LSeries (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ)) sigma).re +
      17.145 * (LSeries (twistedMangoldtCoeff chi)
        (sigma + Complex.I * t)).re +
      10.6825 * (LSeries (twistedMangoldtCoeff (chi ^ 2))
        (sigma + Complex.I * (2 * t))).re +
      4.5 * (LSeries (twistedMangoldtCoeff (chi ^ 3))
        (sigma + Complex.I * (3 * t))).re +
      (LSeries (twistedMangoldtCoeff (chi ^ 4))
        (sigma + Complex.I * (4 * t))).re := by
  have h0 : LSeriesSummable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hsigma)
  have h1 : LSeriesSummable (twistedMangoldtCoeff chi)
      (sigma + Complex.I * t) := by
    simpa only [twistedMangoldtCoeff] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi
        (by simpa using hsigma))
  have h2 : LSeriesSummable (twistedMangoldtCoeff (chi ^ 2))
      (sigma + Complex.I * (2 * t)) := by
    simpa only [twistedMangoldtCoeff] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi ^ 2)
        (by simpa using hsigma))
  have h3 : LSeriesSummable (twistedMangoldtCoeff (chi ^ 3))
      (sigma + Complex.I * (3 * t)) := by
    simpa only [twistedMangoldtCoeff] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi ^ 3)
        (by simpa using hsigma))
  have h4 : LSeriesSummable (twistedMangoldtCoeff (chi ^ 4))
      (sigma + Complex.I * (4 * t)) := by
    simpa only [twistedMangoldtCoeff] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi ^ 4)
        (by simpa using hsigma))
  have h0r := (Complex.hasSum_re h0.hasSum).summable.mul_left 10.01055
  have h1r := (Complex.hasSum_re h1.hasSum).summable.mul_left 17.145
  have h2r := (Complex.hasSum_re h2.hasSum).summable.mul_left 10.6825
  have h3r := (Complex.hasSum_re h3.hasSum).summable.mul_left 4.5
  have h4r := (Complex.hasSum_re h4.hasSum).summable
  have h0eq :
      (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) sigma).re =
        ∑' n, (LSeries.term (fun n : ℕ =>
          (ArithmeticFunction.vonMangoldt n : ℂ)) sigma n).re := by
    exact Complex.re_tsum h0
  have h1eq :
      (LSeries (twistedMangoldtCoeff chi)
        (sigma + Complex.I * t)).re =
        ∑' n, (LSeries.term (twistedMangoldtCoeff chi)
          (sigma + Complex.I * t) n).re := by
    exact Complex.re_tsum h1
  have h2eq :
      (LSeries (twistedMangoldtCoeff (chi ^ 2))
        (sigma + Complex.I * (2 * t))).re =
        ∑' n, (LSeries.term (twistedMangoldtCoeff (chi ^ 2))
          (sigma + Complex.I * (2 * t)) n).re := by
    exact Complex.re_tsum h2
  have h3eq :
      (LSeries (twistedMangoldtCoeff (chi ^ 3))
        (sigma + Complex.I * (3 * t))).re =
        ∑' n, (LSeries.term (twistedMangoldtCoeff (chi ^ 3))
          (sigma + Complex.I * (3 * t)) n).re := by
    exact Complex.re_tsum h3
  have h4eq :
      (LSeries (twistedMangoldtCoeff (chi ^ 4))
        (sigma + Complex.I * (4 * t))).re =
        ∑' n, (LSeries.term (twistedMangoldtCoeff (chi ^ 4))
          (sigma + Complex.I * (4 * t)) n).re := by
    exact Complex.re_tsum h4
  rw [h0eq, h1eq, h2eq, h3eq, h4eq,
    ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← h0r.tsum_add h1r, ← (h0r.add h1r).tsum_add h2r,
    ← ((h0r.add h1r).add h2r).tsum_add h3r,
    ← (((h0r.add h1r).add h2r).add h3r).tsum_add h4r]
  refine tsum_nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  ·
    rw [show (LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ)) sigma n).re =
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) from
      re_vonMangoldtTerm_eq sigma hn]
    rw [re_twistedMangoldtTerm_eq chi sigma t hn]
    have harg2 : (sigma : ℂ) + Complex.I * (2 * (t : ℂ)) =
        (sigma : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ) := by push_cast; ring
    have harg3 : (sigma : ℂ) + Complex.I * (3 * (t : ℂ)) =
        (sigma : ℂ) + Complex.I * ((3 * t : ℝ) : ℂ) := by push_cast; ring
    have harg4 : (sigma : ℂ) + Complex.I * (4 * (t : ℂ)) =
        (sigma : ℂ) + Complex.I * ((4 * t : ℝ) : ℂ) := by push_cast; ring
    rw [harg2, re_twistedMangoldtTerm_eq (chi ^ 2) sigma (2 * t) hn,
      harg3, re_twistedMangoldtTerm_eq (chi ^ 3) sigma (3 * t) hn,
      harg4, re_twistedMangoldtTerm_eq (chi ^ 4) sigma (4 * t) hn]
    have hphase2 : characterPhase (chi ^ 2) (2 * t) n =
        (characterPhase chi t n) ^ 2 := by
      simpa using characterPhase_pow_of_pos chi t n 2 (by norm_num)
    have hphase3 : characterPhase (chi ^ 3) (3 * t) n =
        (characterPhase chi t n) ^ 3 := by
      simpa using characterPhase_pow_of_pos chi t n 3 (by norm_num)
    have hphase4 : characterPhase (chi ^ 4) (4 * t) n =
        (characterPhase chi t n) ^ 4 := by
      simpa using characterPhase_pow_of_pos chi t n 4 (by norm_num)
    rw [hphase2, hphase3, hphase4]
    have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hp := appendixB_characterPhase_polynomial_nonneg chi t n
    convert mul_nonneg hw hp using 1
    ring

/-- The exact Appendix-B trigonometric inequality stated for the logarithmic
derivatives of zeta and the four character powers. -/
theorem appendixB_neg_logDeriv_re_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hsigma : 1 < sigma)
    (t : ℝ) :
    0 ≤ 10.01055 * (-logDeriv riemannZeta sigma).re +
      17.145 * (-logDeriv (DirichletCharacter.LFunction chi)
        (sigma + Complex.I * t)).re +
      10.6825 * (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
        (sigma + Complex.I * (2 * t))).re +
      4.5 * (-logDeriv (DirichletCharacter.LFunction (chi ^ 3))
        (sigma + Complex.I * (3 * t))).re +
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 4))
        (sigma + Complex.I * (4 * t))).re := by
  have hzeta := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (show 1 < (sigma : ℂ).re by simpa using hsigma)
  have h1 := LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction chi
    (show 1 < (sigma + Complex.I * t : ℂ).re by simpa using hsigma)
  have h2 := LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction (chi ^ 2)
    (show 1 < (sigma + Complex.I * (2 * t) : ℂ).re by simpa using hsigma)
  have h3 := LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction (chi ^ 3)
    (show 1 < (sigma + Complex.I * (3 * t) : ℂ).re by simpa using hsigma)
  have h4 := LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction (chi ^ 4)
    (show 1 < (sigma + Complex.I * (4 * t) : ℂ).re by simpa using hsigma)
  have h := appendixB_LSeries_re_nonneg chi hsigma t
  rw [hzeta, h1, h2, h3, h4] at h
  simpa only [logDeriv_apply, neg_div] using h

end
end MAPKhaleAppendixBTrigLogDerivativeCertified

#print axioms MAPKhaleAppendixBTrigLogDerivativeCertified.appendixB_characterPhase_polynomial_nonneg
#print axioms MAPKhaleAppendixBTrigLogDerivativeCertified.appendixB_LSeries_re_nonneg
#print axioms MAPKhaleAppendixBTrigLogDerivativeCertified.appendixB_neg_logDeriv_re_nonneg
