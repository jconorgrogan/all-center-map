import GuthMaynardLemma295CutoffAnalytic

/-!
# The infinite Dirichlet series on the initial line in Lemma 29.5

This file performs the countable Bochner interchange on the literal line
`Re s = 2`.  Absolute convergence is recorded term by term: the norm of the
`n`th term is exactly a constant multiple of `(n+1)⁻²` times the vertical
Mellin transform of the compactly supported cutoff.
-/

namespace GuthMaynardLemma295LineTwoFubini

open MeasureTheory
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295MellinLineTwo

noncomputable section

def lineTwoPoint (r : ℝ) : ℂ := (2 : ℂ) + r * Complex.I

def shiftedLineTwoPoint (g r : ℝ) : ℂ :=
  lineTwoPoint r - g * Complex.I

/-- The `n+1` Dirichlet-series summand before interchanging sum and integral. -/
def lineTwoTerm (N g : ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  (N : ℂ) ^ shiftedLineTwoPoint g r *
    (1 / (n + 1 : ℂ) ^ shiftedLineTwoPoint g r) *
      mellin sourceHZero (lineTwoPoint r)

/-- The literal zeta integrand on the initial line. -/
def lineTwoZetaIntegrand (N g : ℝ) (r : ℝ) : ℂ :=
  (N : ℂ) ^ shiftedLineTwoPoint g r *
    riemannZeta (shiftedLineTwoPoint g r) *
      mellin sourceHZero (lineTwoPoint r)

theorem lineTwoPoint_re (r : ℝ) : (lineTwoPoint r).re = 2 := by
  simp [lineTwoPoint]

theorem shiftedLineTwoPoint_re (g r : ℝ) :
    (shiftedLineTwoPoint g r).re = 2 := by
  simp [shiftedLineTwoPoint, lineTwoPoint]

theorem continuous_lineTwoCoefficient
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Continuous (fun r : ℝ =>
      (N : ℂ) ^ shiftedLineTwoPoint g r *
        (1 / (n + 1 : ℂ) ^ shiftedLineTwoPoint g r)) := by
  have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hn0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp_rw [Complex.cpow_def_of_ne_zero hN0,
    Complex.cpow_def_of_ne_zero hn0]
  unfold shiftedLineTwoPoint lineTwoPoint
  apply Continuous.mul
  · fun_prop
  · apply Continuous.div₀ continuous_const
    · fun_prop
    · intro r
      exact Complex.exp_ne_zero _

/-- Exact norm separation.  The ordinate shift by `g` is imaginary and hence
does not alter the exponent `2` controlling absolute convergence. -/
theorem norm_lineTwoTerm
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) (r : ℝ) :
    ‖lineTwoTerm N g n r‖ =
      (N ^ 2 / (n + 1 : ℝ) ^ 2) *
        ‖mellin sourceHZero (lineTwoPoint r)‖ := by
  unfold lineTwoTerm
  rw [norm_mul, norm_mul, norm_div, norm_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hN]
  have hnNorm :
      ‖(n + 1 : ℂ) ^ shiftedLineTwoPoint g r‖ =
        ((n : ℝ) + 1) ^ (shiftedLineTwoPoint g r).re := by
    convert Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
        (shiftedLineTwoPoint g r) using 1 <;> norm_num
  rw [hnNorm]
  rw [shiftedLineTwoPoint_re, Real.rpow_two, Real.rpow_two]
  ring

theorem integrable_lineTwoTerm
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Integrable (lineTwoTerm N g n) := by
  have hmellin : Integrable (fun r : ℝ =>
      mellin sourceHZero (lineTwoPoint r)) := by
    simpa [lineTwoPoint] using sourceHZero_verticalIntegrable_two
  have hdom : Integrable (fun r : ℝ =>
      (N ^ 2 / (n + 1 : ℝ) ^ 2) *
        ‖mellin sourceHZero (lineTwoPoint r)‖) :=
    hmellin.norm.const_mul _
  apply hdom.mono'
  · exact (continuous_lineTwoCoefficient hN g n).aestronglyMeasurable.mul
      hmellin.aestronglyMeasurable
  · filter_upwards [] with r
    rw [norm_lineTwoTerm hN]

theorem integral_norm_lineTwoTerm
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    (∫ r : ℝ, ‖lineTwoTerm N g n r‖) =
      (N ^ 2 / (n + 1 : ℝ) ^ 2) *
        ∫ r : ℝ, ‖mellin sourceHZero (lineTwoPoint r)‖ := by
  rw [show (fun r : ℝ => ‖lineTwoTerm N g n r‖) =
      (fun r : ℝ => (N ^ 2 / (n + 1 : ℝ) ^ 2) *
        ‖mellin sourceHZero (lineTwoPoint r)‖) by
      funext r
      exact norm_lineTwoTerm hN g n r]
  exact integral_const_mul _ _

theorem summable_integral_norm_lineTwoTerm
    {N : ℝ} (hN : 0 < N) (g : ℝ) :
    Summable fun n : ℕ => ∫ r : ℝ, ‖lineTwoTerm N g n r‖ := by
  let K : ℝ := ∫ r : ℝ, ‖mellin sourceHZero (lineTwoPoint r)‖
  have hs : Summable fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2 := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    simpa [abs_of_nonneg, Real.rpow_two] using h
  have hscaled := hs.mul_left (N ^ 2 * K)
  apply hscaled.congr
  intro n
  rw [integral_norm_lineTwoTerm hN]
  dsimp [K]
  ring

/-- Pointwise reconstruction of the zeta integrand from its absolutely
convergent Dirichlet series. -/
theorem tsum_lineTwoTerm_eq_zetaIntegrand
    (N g r : ℝ) :
    (∑' n : ℕ, lineTwoTerm N g n r) =
      lineTwoZetaIntegrand N g r := by
  unfold lineTwoTerm lineTwoZetaIntegrand
  have hzeta := zeta_shift_dirichletSeries_line_two g r
  have hzeta' : riemannZeta (shiftedLineTwoPoint g r) =
      ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ shiftedLineTwoPoint g r := by
    simpa [shiftedLineTwoPoint, lineTwoPoint] using hzeta
  change (∑' n : ℕ,
      (N : ℂ) ^ shiftedLineTwoPoint g r *
        (1 / (n + 1 : ℂ) ^ shiftedLineTwoPoint g r) *
          mellin sourceHZero (lineTwoPoint r)) = _
  calc
    _ = ∑' n : ℕ, (N : ℂ) ^ shiftedLineTwoPoint g r *
        ((1 / (n + 1 : ℂ) ^ shiftedLineTwoPoint g r) *
          mellin sourceHZero (lineTwoPoint r)) := by
      apply tsum_congr
      intro n
      ring
    _ = (N : ℂ) ^ shiftedLineTwoPoint g r *
        ((∑' n : ℕ, 1 / (n + 1 : ℂ) ^ shiftedLineTwoPoint g r) *
          mellin sourceHZero (lineTwoPoint r)) := by
      rw [tsum_mul_left, tsum_mul_right]
    _ = _ := by rw [← hzeta']; ring

/-- The full infinite-sum/line-`2` Fubini assembly used before the contour
displacement in Lemma 29.5. -/
theorem lineTwo_series_integral_identity
    {N : ℝ} (hN : 0 < N) (g : ℝ) :
    (∑' n : ℕ, ∫ r : ℝ, lineTwoTerm N g n r) =
      ∫ r : ℝ, lineTwoZetaIntegrand N g r := by
  calc
    (∑' n : ℕ, ∫ r : ℝ, lineTwoTerm N g n r) =
        ∫ r : ℝ, ∑' n : ℕ, lineTwoTerm N g n r :=
      integral_tsum_of_summable_integral_norm
        (fun n => integrable_lineTwoTerm hN g n)
        (summable_integral_norm_lineTwoTerm hN g)
    _ = ∫ r : ℝ, lineTwoZetaIntegrand N g r := by
      apply integral_congr_ae
      filter_upwards [] with r
      exact tsum_lineTwoTerm_eq_zetaIntegrand N g r

theorem lineTwoTerm_eq_inverseMellin_mul_phase
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) (r : ℝ) :
    lineTwoTerm N g n r =
      (((((n : ℝ) + 1) / N : ℝ) : ℂ) ^ (-lineTwoPoint r) *
        ((((n : ℝ) + 1) / N : ℝ) : ℂ) ^ (g * Complex.I)) *
          mellin sourceHZero (lineTwoPoint r) := by
  have hk : 0 < (n : ℝ) + 1 := by positivity
  have hx : 0 < ((n : ℝ) + 1) / N := div_pos hk hN
  have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hk0 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hk.ne'
  have hx0 : ((((n : ℝ) + 1) / N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  unfold lineTwoTerm shiftedLineTwoPoint
  rw [show (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num]
  rw [Complex.cpow_def_of_ne_zero hN0,
    Complex.cpow_def_of_ne_zero hk0,
    Complex.cpow_def_of_ne_zero hx0,
    Complex.cpow_def_of_ne_zero hx0]
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  simp only [one_mul]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [← Complex.ofReal_log hN.le, ← Complex.ofReal_log hk.le,
    ← Complex.ofReal_log hx.le]
  rw [Real.log_div hk.ne' hN.ne']
  push_cast
  ring

/-- Mellin inversion identifies one interchanged Dirichlet coefficient with
the corresponding literal cutoff summand. -/
theorem normalized_integral_lineTwoTerm_eq_sourceHPlus
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ r : ℝ, lineTwoTerm N g n r) =
      sourceHPlus g (((n : ℝ) + 1) / N) := by
  let x : ℝ := ((n : ℝ) + 1) / N
  have hx : 0 < x := div_pos (by positivity) hN
  have hinv := sourceHZero_mellin_inversion_two (x := x) hx
  rw [mellinInv] at hinv
  have hinv' :
      sourceHZero x = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, (x : ℂ) ^ (-lineTwoPoint r) *
          mellin sourceHZero (lineTwoPoint r)) := by
    simpa only [Complex.real_smul, lineTwoPoint] using hinv.symm
  rw [show (fun r : ℝ => lineTwoTerm N g n r) =
      (fun r : ℝ => ((x : ℂ) ^ (g * Complex.I)) *
        ((x : ℂ) ^ (-lineTwoPoint r) *
          mellin sourceHZero (lineTwoPoint r))) by
      funext r
      rw [lineTwoTerm_eq_inverseMellin_mul_phase hN]
      dsimp [x]
      ring]
  rw [integral_const_mul]
  rw [sourceHPlus_eq_sourceHZero_mul_cpow hx]
  rw [hinv']
  ring

/-- Complete initial-line identity: the literal finite smooth sum equals the
normalized full zeta--Mellin integral on `Re s=2`. -/
theorem sourceHPlusSum_eq_lineTwo_zeta_integral
    {N : ℝ} (hN : 0 < N) (g : ℝ) :
    sourceHPlusSum N g =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, lineTwoZetaIntegrand N g r) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hNormInt : Summable fun n : ℕ =>
      ‖∫ r : ℝ, lineTwoTerm N g n r‖ :=
    (summable_integral_norm_lineTwoTerm hN g).of_nonneg_of_le
      (fun n => norm_nonneg _)
      (fun n => norm_integral_le_integral_norm _)
  have hComplexInt : Summable fun n : ℕ =>
      ∫ r : ℝ, lineTwoTerm N g n r := summable_norm_iff.mp hNormInt
  have hIntSummable : Summable fun n : ℕ =>
      c * ∫ r : ℝ, lineTwoTerm N g n r :=
    hComplexInt.mul_left c
  have hshift : Summable fun n : ℕ =>
      sourceHPlus g (((n : ℝ) + 1) / N) := by
    apply hIntSummable.congr
    intro n
    exact normalized_integral_lineTwoTerm_eq_sourceHPlus hN g n
  let f : ℕ → ℂ := fun n => sourceHPlus g ((n : ℝ) / N)
  have hshiftF : Summable fun n : ℕ => f (n + 1) := by
    simpa [f, Nat.cast_add, Nat.cast_one] using hshift
  have hf : Summable f := (summable_nat_add_iff 1).mp hshiftF
  have hfzero : f 0 = 0 := by
    unfold f sourceHPlus
    rw [show ((0 : ℕ) : ℝ) / N = 0 by simp]
    rw [sourceWZero_eq_zero_left (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp
  have htail : (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
    have h := hf.sum_add_tsum_nat_add 1
    simpa [hfzero] using h
  rw [← tsum_sourceHPlus_eq_sourceHPlusSum hN g]
  change (∑' n : ℕ, f n) = c * ∫ r : ℝ, lineTwoZetaIntegrand N g r
  rw [← htail]
  calc
    (∑' n : ℕ, f (n + 1)) =
        ∑' n : ℕ, c * ∫ r : ℝ, lineTwoTerm N g n r := by
      apply tsum_congr
      intro n
      change f (n + 1) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ r : ℝ, lineTwoTerm N g n r)
      simpa [f, Nat.cast_add, Nat.cast_one] using
        (normalized_integral_lineTwoTerm_eq_sourceHPlus hN g n).symm
    _ = c * (∑' n : ℕ, ∫ r : ℝ, lineTwoTerm N g n r) :=
      tsum_mul_left
    _ = c * ∫ r : ℝ, lineTwoZetaIntegrand N g r := by
      rw [lineTwo_series_integral_identity hN]

end
end GuthMaynardLemma295LineTwoFubini

#print axioms GuthMaynardLemma295LineTwoFubini.integrable_lineTwoTerm
#print axioms GuthMaynardLemma295LineTwoFubini.summable_integral_norm_lineTwoTerm
#print axioms GuthMaynardLemma295LineTwoFubini.lineTwo_series_integral_identity
#print axioms GuthMaynardLemma295LineTwoFubini.sourceHPlusSum_eq_lineTwo_zeta_integral
