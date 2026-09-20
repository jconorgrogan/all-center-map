import AppendixA45GrowthConnector
import AppendixA4GammaWitness
import RieszMellinInversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Full right-line assembly for Appendix (A.4)

This module closes the first exact missing seam in the literal Gamma detector:
the absolutely convergent Dirichlet series for `L(s,χ) M_U(s,χ)` is commuted
through the full Bochner integral on `Re z = 1/2`.
-/

namespace MAPAppendixA4GammaEndpoint

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPMellinDetectorLeaf

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The exact coefficient sequence in (A.3), including the character twist. -/
def detectorCoeff (chi : DirichletCharacter ℂ q) (U : ℕ) : ℕ → ℂ :=
  ((chi ·) : ℕ → ℂ) * mollifierCoeff U

/-- The `n`th term of the Gamma detector on the paper's right line `Re z=1/2`. -/
def gammaRightTerm (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma ((1 / 2 : ℝ) + t * I) *
    (Y : ℂ) ^ ((1 / 2 : ℝ) + t * I) *
    LSeries.term (detectorCoeff chi U)
      (rho + ((1 / 2 : ℝ) + t * I)) n

/-- The literal right-line Gamma--L--mollifier integrand from (A.4). -/
def gammaRightIntegrand (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  Complex.Gamma ((1 / 2 : ℝ) + t * I) *
    (Y : ℂ) ^ ((1 / 2 : ℝ) + t * I) *
    DirichletCharacter.LFunction chi
      (rho + ((1 / 2 : ℝ) + t * I)) *
    mollifier chi U (rho + ((1 / 2 : ℝ) + t * I))

/-- Absolute convergence of the coefficient series on the whole right line.
The point is that `Re (rho + 1/2 + it) = beta+1/2 > 1`. -/
theorem detectorCoeff_LSeriesSummable
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) (t : ℝ) :
    LSeriesSummable (detectorCoeff chi U)
      (rho + ((1 / 2 : ℝ) + t * I)) := by
  have hs : 1 < (rho + ((1 / 2 : ℝ) + t * I)).re := by
    simp
    linarith
  have hchi := DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs
  have hmu : LSeriesSummable
      (((chi ·) : ℕ → ℂ) * truncatedMoebius U)
      (rho + ((1 / 2 : ℝ) + t * I)) :=
    DirichletCharacter.LSeriesSummable_mul chi
      (LSeriesSummable_truncatedMoebius hs)
  have hconv := hchi.convolution hmu
  rw [character_convolution_mollifierCoeff chi] at hconv
  exact hconv

/-- Complex powers respect a quotient of positive real bases. -/
theorem ofReal_div_cpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    ((x / y : ℝ) : ℂ) ^ z = (x : ℂ) ^ z / (y : ℂ) ^ z := by
  rw [Complex.ofReal_div, div_eq_mul_inv, ← Complex.ofReal_inv]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hy.le)]
  rw [Complex.ofReal_inv, Complex.inv_cpow]
  · rfl
  · rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact ne_of_lt Real.pi_pos

/-- A right-line coefficient factors as the arithmetic `n^{-rho}` coefficient
times the one-dimensional Mellin kernel for `exp(-n/Y)`. -/
theorem gammaRightTerm_eq_arithmeticCoeff_mul
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ)
    {Y : ℝ} (hY : 0 < Y) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    gammaRightTerm chi U rho Y n t =
      LSeries.term (detectorCoeff chi U) rho n *
        (Complex.Gamma ((1 / 2 : ℝ) + t * I) *
          ((Y / n : ℝ) : ℂ) ^ ((1 / 2 : ℝ) + t * I)) := by
  let z : ℂ := (1 / 2 : ℝ) + t * I
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold gammaRightTerm
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  rw [ofReal_div_cpow hY hnpos z]
  dsimp [z]
  field_simp

/-- Each coefficient term is continuous in the vertical parameter. -/
theorem continuous_gammaRightTerm
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ)
    {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    Continuous (gammaRightTerm chi U rho Y n) := by
  unfold gammaRightTerm
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr fun t => by
        have hinner : ContinuousAt (fun u : ℝ =>
            ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) t := by fun_prop
        exact (Complex.continuousAt_Gamma _ (fun m h => by
          have hre := congrArg Complex.re h
          simp at hre
          linarith)).comp_of_eq hinner rfl
    · have hpow : Differentiable ℂ (fun z : ℂ => (Y : ℂ) ^ z) :=
        differentiable_id.const_cpow
          (.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
      exact hpow.continuous.comp (by fun_prop)
  · exact continuous_iff_continuousAt.mpr fun t => by
      have hout := (LSeries.hasDerivAt_term (detectorCoeff chi U) n
        (rho + ((1 / 2 : ℝ) + t * I))).continuousAt
      have hinner : ContinuousAt (fun u : ℝ =>
          rho + (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t := by fun_prop
      exact hout.comp_of_eq hinner rfl

/-- The norm of a right-line term factors into its absolute Dirichlet-series
coefficient, the fixed `Y^(1/2)` factor, and the Gamma envelope. -/
theorem norm_gammaRightTerm_eq
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ)
    {Y : ℝ} (hY : 0 < Y) (n : ℕ) (t : ℝ) :
    ‖gammaRightTerm chi U rho Y n t‖ =
      ‖LSeries.term (detectorCoeff chi U) ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ *
        (Y ^ (1 / 2 : ℝ) *
          ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖) := by
  unfold gammaRightTerm
  rw [norm_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have hterm :
      ‖LSeries.term (detectorCoeff chi U)
          (rho + ((1 / 2 : ℝ) + t * I)) n‖ =
        ‖LSeries.term (detectorCoeff chi U)
          ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  rw [hterm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, add_zero]
  ring

/-- Every coefficient term is Bochner integrable on the full vertical line. -/
theorem integrable_gammaRightTerm
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ)
    {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    Integrable (gammaRightTerm chi U rho Y n) := by
  have hGamma : Integrable (fun t : ℝ =>
      Complex.Gamma ((1 / 2 : ℝ) + t * I)) :=
    MAPGammaMellinInversion.verticalIntegrable_Gamma (by norm_num)
  have hnorm : Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖) := hGamma.norm
  let C : ℝ :=
    ‖LSeries.term (detectorCoeff chi U) ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ *
      Y ^ (1 / 2 : ℝ)
  have hdom : Integrable (fun t : ℝ =>
      C * ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖) := hnorm.const_mul C
  apply hdom.mono'
  · exact (continuous_gammaRightTerm chi U rho hY n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [norm_gammaRightTerm_eq chi U rho hY]
      dsimp [C]
      simpa only [mul_assoc] using
        (le_refl (‖LSeries.term (detectorCoeff chi U)
          ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ * Y ^ (1 / 2 : ℝ) *
            ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖)))

/-- The integrated coefficient norms form a summable series.  This is the
Tonelli/Bochner load-bearing estimate, not a theorem-valued premise. -/
theorem summable_integral_norm_gammaRightTerm
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    Summable fun n : ℕ =>
      ∫ t : ℝ, ‖gammaRightTerm chi U rho Y n t‖ := by
  let G : ℝ := ∫ t : ℝ,
    ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖
  have hs : LSeriesSummable (detectorCoeff chi U)
      ((rho.re + 1 / 2 : ℝ) : ℂ) := by
    have hline := detectorCoeff_LSeriesSummable chi U hbeta 0
    exact (LSeriesSummable_iff_of_re_eq_re (f := detectorCoeff chi U)
      (s := rho + ((1 / 2 : ℝ) + (0 : ℝ) * I))
      (s' := ((rho.re + 1 / 2 : ℝ) : ℂ)) (by simp)).mp hline
  have hnorm : Summable fun n : ℕ =>
      ‖LSeries.term (detectorCoeff chi U)
        ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ := summable_norm_iff.mpr hs
  have hscaled : Summable fun n : ℕ =>
      ‖LSeries.term (detectorCoeff chi U)
        ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ * (Y ^ (1 / 2 : ℝ) * G) :=
    hnorm.mul_right (Y ^ (1 / 2 : ℝ) * G)
  apply hscaled.congr
  intro n
  rw [show (fun t : ℝ => ‖gammaRightTerm chi U rho Y n t‖) =
      (fun t : ℝ =>
        (‖LSeries.term (detectorCoeff chi U)
          ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ * Y ^ (1 / 2 : ℝ)) *
          ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖) by
        funext t
        rw [norm_gammaRightTerm_eq chi U rho hY]
        ring]
  rw [MeasureTheory.integral_const_mul]
  dsimp [G]
  ring

/-- Pointwise, the coefficient series is the literal Gamma--L--mollifier
integrand on the right line. -/
theorem tsum_gammaRightTerm_eq_gammaRightIntegrand
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) (Y : ℝ) (t : ℝ) :
    (∑' n : ℕ, gammaRightTerm chi U rho Y n t) =
      gammaRightIntegrand chi U rho Y t := by
  let z : ℂ := (1 / 2 : ℝ) + t * I
  have hs : 1 < (rho + z).re := by
    dsimp [z]
    simp
    linarith
  unfold gammaRightTerm gammaRightIntegrand
  have hrhs :
      Complex.Gamma z * (Y : ℂ) ^ z *
          DirichletCharacter.LFunction chi (rho + z) *
          mollifier chi U (rho + z) =
        Complex.Gamma z * (Y : ℂ) ^ z *
          (DirichletCharacter.LFunction chi (rho + z) *
            mollifier chi U (rho + z)) := by ring
  dsimp [z] at hrhs ⊢
  rw [hrhs]
  rw [LFunction_mul_mollifier_eq chi hs]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  rw [tsum_mul_left]
  dsimp [z]
  unfold detectorCoeff LSeries
  rfl

/-- **Exact Gamma right-line identity with the full Dirichlet series already
inside the Bochner integral.**  This closes the deterministic series/integral
interchange missing from Appendix (A.4). -/
theorem gamma_right_line_series_integral_identity
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    ∑' n : ℕ, ∫ t : ℝ, gammaRightTerm chi U rho Y n t =
      ∫ t : ℝ, gammaRightIntegrand chi U rho Y t := by
  calc
    ∑' n : ℕ, ∫ t : ℝ, gammaRightTerm chi U rho Y n t =
        ∫ t : ℝ, ∑' n : ℕ, gammaRightTerm chi U rho Y n t :=
      MeasureTheory.integral_tsum_of_summable_integral_norm
        (fun n => integrable_gammaRightTerm chi U rho hY n)
        (summable_integral_norm_gammaRightTerm chi U hbeta hY)
    _ = ∫ t : ℝ, gammaRightIntegrand chi U rho Y t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (tsum_gammaRightTerm_eq_gammaRightIntegrand chi U hbeta Y)


/-- The exact normalized vertical integral of one coefficient.  At `n=0`
both sides vanish by the `LSeries.term` convention; for `n>0` this is the
one-coefficient inverse Mellin formula with no normalization ambiguity. -/
theorem normalized_integral_gammaRightTerm_eq
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ)
    {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, gammaRightTerm chi U rho Y n t) =
      LSeries.term (detectorCoeff chi U) rho n *
        (Real.exp (-((n : ℝ) / Y)) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [gammaRightTerm]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hMellin := MAPGammaMellinInversion.exp_neg_nat_div_eq_detector_right_line
      (sigma := (1 / 2 : ℝ)) (Y := Y) (n := n) (by norm_num) hY hnpos
    rw [show (fun t : ℝ => gammaRightTerm chi U rho Y n t) =
        (fun t : ℝ => LSeries.term (detectorCoeff chi U) rho n *
          (Complex.Gamma ((1 / 2 : ℝ) + t * I) *
            ((Y / n : ℝ) : ℂ) ^ ((1 / 2 : ℝ) + t * I))) by
      funext t
      exact gammaRightTerm_eq_arithmeticCoeff_mul chi U rho hY hn t]
    rw [MeasureTheory.integral_const_mul]
    rw [hMellin]
    ring

/-- The arithmetic detector term appearing on the left side of (A.4). -/
def arithmeticDetectorTerm
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (detectorCoeff chi U) rho n *
    (Real.exp (-((n : ℝ) / Y)) : ℂ)

/-- The exponentially weighted arithmetic detector series is summable even
when `Re rho <= 1`; summability is obtained from the certified Gamma-line
Bochner majorant, not asserted separately. -/
theorem summable_arithmeticDetectorTerm
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    Summable (arithmeticDetectorTerm chi U rho Y) := by
  have hnormsum := summable_integral_norm_gammaRightTerm chi U hbeta hY
  have hintNorm : Summable fun n : ℕ =>
      ‖∫ t : ℝ, gammaRightTerm chi U rho Y n t‖ := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => MeasureTheory.norm_integral_le_integral_norm
        (gammaRightTerm chi U rho Y n)) hnormsum
  have hint : Summable fun n : ℕ =>
      ∫ t : ℝ, gammaRightTerm chi U rho Y n t :=
    summable_norm_iff.mp hintNorm
  have hscaled := hint.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  exact hscaled.congr (fun n =>
    normalized_integral_gammaRightTerm_eq chi U rho hY n)

/-- Summing the one-coefficient inversion formula gives the full normalized
right-line integral as the exact arithmetic detector series. -/
theorem normalized_gamma_right_line_eq_arithmetic_tsum
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, gammaRightIntegrand chi U rho Y t) =
        ∑' n : ℕ, arithmeticDetectorTerm chi U rho Y n := by
  rw [← gamma_right_line_series_integral_identity chi U hbeta hY]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact normalized_integral_gammaRightTerm_eq chi U rho hY n

/-- On the detector's initial range only the distinguished coefficient `n=1`
survives.  This is the exact `c_1=1`, `c_n=0` weld in the normalization used
by (A.4). -/
theorem arithmeticDetectorTerm_sum_range_eq_main
    (chi : DirichletCharacter ℂ q) {U : ℕ} (hU : 1 ≤ U)
    (rho : ℂ) {Y : ℝ} (_hY : 0 < Y) :
    ∑ n ∈ Finset.range (U + 1), arithmeticDetectorTerm chi U rho Y n =
      (Real.exp (-(1 / Y)) : ℂ) := by
  rw [Finset.sum_eq_single 1]
  · unfold arithmeticDetectorTerm detectorCoeff
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp [mollifierCoeff_one hU]
  · intro n hn hne
    have hnU : n ≤ U := by
      have : n < U + 1 := Finset.mem_range.mp hn
      omega
    by_cases hn0 : n = 0
    · subst n
      simp [arithmeticDetectorTerm]
    · have hn1 : 1 < n := by omega
      unfold arithmeticDetectorTerm detectorCoeff
      rw [LSeries.term_of_ne_zero hn0]
      simp only [Pi.mul_apply]
      rw [mollifierCoeff_eq_zero_of_one_lt_le hn1 hnU]
      simp
  · intro hnot
    exfalso
    apply hnot
    exact Finset.mem_range.mpr (by omega)

/-- **Literal arithmetic side of (A.4).**  The full series is the displayed
main term plus precisely the `n>U` tail; no coefficient range is hidden. -/
theorem arithmetic_detector_tsum_eq_main_add_tail
    (chi : DirichletCharacter ℂ q) {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    (∑' n : ℕ, arithmeticDetectorTerm chi U rho Y n) =
      (Real.exp (-(1 / Y)) : ℂ) +
        ∑' n : {n // n ∉ Finset.range (U + 1)},
          arithmeticDetectorTerm chi U rho Y n := by
  have hs := summable_arithmeticDetectorTerm chi U hbeta hY
  rw [← hs.sum_add_tsum_subtype_compl (Finset.range (U + 1))]
  rw [arithmeticDetectorTerm_sum_range_eq_main chi hU rho hY]

/-- **Exact full right-line form of Equation (A.4), before contour shift.**
The normalization is `1/(2*pi)` because `z=1/2+it` and `dz=i dt`; the contour
notation `1/(2*pi*i) ∫ ... dz` is therefore identical. -/
theorem literal_A4_right_line_identity
    (chi : DirichletCharacter ℂ q) {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    (Real.exp (-(1 / Y)) : ℂ) +
        ∑' n : {n // n ∉ Finset.range (U + 1)},
          arithmeticDetectorTerm chi U rho Y n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, gammaRightIntegrand chi U rho Y t) := by
  rw [normalized_gamma_right_line_eq_arithmetic_tsum chi U hbeta hY]
  exact (arithmetic_detector_tsum_eq_main_add_tail chi hU hbeta hY).symm


end
end MAPAppendixA4GammaEndpoint

#print axioms MAPAppendixA4GammaEndpoint.gamma_right_line_series_integral_identity
