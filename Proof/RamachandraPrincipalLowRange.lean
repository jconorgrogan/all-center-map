import RamachandraPrimitiveShiftedContourReduction
import PrincipalZetaFixedStrip

/-!
# The principal low-height branch in Ramachandra's shifted argument

Printed Lemma 3 applies its contour formula to the principal character only
after excluding `|t| < log(qT)^2`.  The proof of Theorem 6 says merely that
the shifted primitive estimate follows in the same way.  This file closes the
otherwise easy-to-hide low-height branch: the already certified polynomial
fixed-strip bound for `(s-1) zeta(s)` gives a completely explicit integral
bound on every symmetric low window.
-/

namespace RamachandraPrincipalLowRange

open Complex MeasureTheory
open RamachandraTheorem6ShiftedStripSource
open RamachandraTheorem6SourceProofChain
open RamachandraPrimitiveShiftedFiniteReduction

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- Uniform raw zeta bound in the narrow region containing the Theorem 6
strip.  The exponent six comes from the certified regularized fixed-strip
bound, not from a fourth-moment input. -/
theorem norm_riemannZeta_shifted_le
    {sigma t : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 3 / 4) :
    ‖riemannZeta ((sigma : ℂ) + t * I)‖ ≤
      6400 * (4 + |t|) ^ 6 := by
  let s : ℂ := (sigma : ℂ) + t * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hreg :=
    MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
      (z := s) (by simp [s]; linarith) (by simp [s]; linarith)
  have hden : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
    have hre := Complex.abs_re_le_norm (s - 1)
    have habs : |sigma - 1| = 1 - sigma := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    have hquarter : (1 / 4 : ℝ) ≤ |(s - 1).re| := by
      have hreEq : (s - 1).re = sigma - 1 := by simp [s]
      rw [hreEq, habs]
      linarith
    exact hquarter.trans hre
  have hshift : ‖s + 3‖ ≤ 4 + |t| := by
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = sigma + 3 + |t| := by
        have hs3 : 0 ≤ sigma + 3 := by linarith
        simp [s, abs_of_nonneg hs3]
      _ ≤ 4 + |t| := by linarith
  have heq : MAPPrincipalZetaFixedStrip.principalRegularized s =
      (s - 1) * riemannZeta s :=
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs1
  change ‖riemannZeta s‖ ≤ _
  calc
    ‖riemannZeta s‖ ≤ 4 * (‖s - 1‖ * ‖riemannZeta s‖) := by
      nlinarith [mul_nonneg (norm_nonneg (s - 1))
        (norm_nonneg (riemannZeta s))]
    _ = 4 * ‖MAPPrincipalZetaFixedStrip.principalRegularized s‖ := by
      rw [heq, norm_mul]
    _ ≤ 4 * (1600 * ‖s + 3‖ ^ 6) := by gcongr
    _ ≤ 4 * (1600 * (4 + |t|) ^ 6) := by gcongr
    _ = 6400 * (4 + |t|) ^ 6 := by ring

/-- Pointwise fourth-power version for the unique conductor-one character. -/
theorem shiftedStripLFourth_modOne_le
    {sigma t : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 3 / 4) :
    shiftedStripLFourth chiOne sigma t ≤
      (6400 * (4 + |t|) ^ 6) ^ 4 := by
  unfold shiftedStripLFourth
  rw [DirichletCharacter.LFunction_modOne_eq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_riemannZeta_shifted_le hsigma0 hsigma1) 4

/-- Explicit integral bound on the principal low-height interval.  Taking
`H = log(qT)^2` makes the right side a fixed power of `log(qT)`, with enormous
room under the source exponent `200`. -/
theorem principalLowRangeFourthIntegral_le
    {sigma H : ℝ} (hsigma0 : 0 ≤ sigma)
    (hsigma1 : sigma ≤ 3 / 4) (hH : 0 ≤ H) :
    (∫ t in (-H)..H, shiftedStripLFourth chiOne sigma t) ≤
      2 * H * (6400 * (4 + H) ^ 6) ^ 4 := by
  have hsigmaNe : sigma ≠ 1 := by linarith
  calc
    (∫ t in (-H)..H, shiftedStripLFourth chiOne sigma t) ≤
        ∫ _t in (-H)..H, (6400 * (4 + H) ^ 6) ^ 4 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (continuous_shiftedStripLFourth chiOne hsigmaNe).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro t ht
        have htAbs : |t| ≤ H := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
        calc
          shiftedStripLFourth chiOne sigma t ≤
              (6400 * (4 + |t|) ^ 6) ^ 4 :=
            shiftedStripLFourth_modOne_le hsigma0 hsigma1
          _ ≤ (6400 * (4 + H) ^ 6) ^ 4 := by
            have hbase : 6400 * (4 + |t|) ^ 6 ≤
                6400 * (4 + H) ^ 6 := by gcongr
            exact pow_le_pow_left₀ (by positivity) hbase 4
    _ = 2 * H * (6400 * (4 + H) ^ 6) ^ 4 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

/-- Ramachandra's stated strip is contained in `[0,3/4]`. -/
theorem sigma_mem_zero_threequarters_of_ramachandraStrip
    {q : ℕ} [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    0 ≤ sigma ∧ sigma ≤ 3 / 4 := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := by linarith
  have hprodpos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  have hthree : (3 : ℝ) ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT
      (by norm_num : (0 : ℝ) ≤ 3) hqpos.le]
  have hlogthree : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlogone : 1 < Real.log ((q : ℝ) * T) := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) hprodpos hthree
    exact hlogthree.trans_le hmono
  have hden : (100 : ℝ) <
      100 * Real.log ((q : ℝ) * T) := by nlinarith
  have hinv : (100 * Real.log ((q : ℝ) * T))⁻¹ <
      (100 : ℝ)⁻¹ := by
    exact (inv_lt_inv₀
      (by positivity : (0 : ℝ) < 100 * Real.log ((q : ℝ) * T))
      (by norm_num : (0 : ℝ) < 100)).2 hden
  have hoff : |sigma - (1 / 2 : ℝ)| < 1 / 4 :=
    hstrip.trans_lt (hinv.trans (by norm_num))
  have hb := (abs_lt.mp hoff)
  constructor <;> linarith

/-- The excluded principal range `|t| ≤ log(T)^2` already satisfies the
primitive p.88 budget.  This formally closes the exceptional first sentence
of Lemma 3 for the continuous shifted theorem. -/
theorem principalLogSquaredLowRange_le_sourceBudget
    {q : ℕ} [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    (∫ t in (-(Real.log T) ^ 2)..(Real.log T) ^ 2,
      shiftedStripLFourth chiOne sigma t) ≤
      (2 * 6400 ^ 4 * 5 ^ 24 : ℝ) * T * Real.log T ^ 200 := by
  obtain ⟨hsigma0, hsigma1⟩ :=
    sigma_mem_zero_threequarters_of_ramachandraStrip hT hstrip
  let L : ℝ := Real.log T
  have hTpos : 0 < T := by linarith
  have hLone : 1 ≤ L := by
    have hlogthree : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
    exact (hlogthree.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hTpos hT)).le
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hlow := principalLowRangeFourthIntegral_le
    hsigma0 hsigma1 (sq_nonneg L)
  have hbase : 4 + L ^ 2 ≤ 5 * L ^ 2 := by
    nlinarith [one_le_pow₀ hLone (n := 2)]
  have hpow : L ^ 50 ≤ L ^ 200 :=
    pow_le_pow_right₀ hLone (by norm_num)
  calc
    (∫ t in (-(Real.log T) ^ 2)..(Real.log T) ^ 2,
        shiftedStripLFourth chiOne sigma t) ≤
        2 * L ^ 2 * (6400 * (4 + L ^ 2) ^ 6) ^ 4 := by
      simpa [L] using hlow
    _ ≤ 2 * L ^ 2 * (6400 * (5 * L ^ 2) ^ 6) ^ 4 := by
      gcongr
    _ = (2 * 6400 ^ 4 * 5 ^ 24 : ℝ) * L ^ 50 := by ring
    _ ≤ (2 * 6400 ^ 4 * 5 ^ 24 : ℝ) * L ^ 200 := by
      gcongr
    _ ≤ (2 * 6400 ^ 4 * 5 ^ 24 : ℝ) * T * L ^ 200 := by
      have hTOne : 1 ≤ T := by linarith
      have hLp : 0 ≤ L ^ 200 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hTOne hLp]
    _ = (2 * 6400 ^ 4 * 5 ^ 24 : ℝ) * T *
        Real.log T ^ 200 := by rfl

end
end RamachandraPrincipalLowRange

#print axioms RamachandraPrincipalLowRange.norm_riemannZeta_shifted_le
#print axioms RamachandraPrincipalLowRange.shiftedStripLFourth_modOne_le
#print axioms RamachandraPrincipalLowRange.principalLowRangeFourthIntegral_le
#print axioms RamachandraPrincipalLowRange.principalLogSquaredLowRange_le_sourceBudget
