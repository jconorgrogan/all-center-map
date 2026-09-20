import GoldfeldFourfoldPositivity
import AppendixA4GammaEndpoint

/-!
# A smoothed Mellin identity for Goldfeld's fourfold Dirichlet series

This is the source-faithful Tonelli/Mellin layer of Goldfeld's comparison
argument.  It is stated first for an arbitrary absolutely convergent Dirichlet
series, then specialized to `ζ L(χ)L(ψ)L(χψ)`.
-/

namespace MAPGoldfeldSiegel

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPAppendixA4RieszInversion MAPAppendixA4RieszKernel

noncomputable section

/-- One coefficient on the initial Riesz vertical line. -/
def rieszRightTerm (f : ℕ → ℂ) (rho : ℂ) (k : ℕ)
    (X c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  rieszMellinKernel k ((c : ℂ) + t * I) *
    (X : ℂ) ^ ((c : ℂ) + t * I) *
      LSeries.term f (rho + ((c : ℂ) + t * I)) n

/-- The full Dirichlet-series integrand on the initial line. -/
def rieszRightIntegrand (f : ℕ → ℂ) (rho : ℂ) (k : ℕ)
    (X c : ℝ) (t : ℝ) : ℂ :=
  rieszMellinKernel k ((c : ℂ) + t * I) *
    (X : ℂ) ^ ((c : ℂ) + t * I) *
      LSeries f (rho + ((c : ℂ) + t * I))

/-- A coefficient factors into its value at `rho` and the Mellin scale
`(X/n)^s`. -/
theorem rieszRightTerm_eq_arithmeticCoeff_mul
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) {X c : ℝ}
    (hX : 0 < X) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    rieszRightTerm f rho k X c n t =
      LSeries.term f rho n *
        (rieszMellinKernel k ((c : ℂ) + t * I) *
          ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I)) := by
  let z : ℂ := (c : ℂ) + t * I
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold rieszRightTerm
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  rw [MAPAppendixA4GammaEndpoint.ofReal_div_cpow hX hnpos z]
  dsimp [z]
  field_simp
  <;> ring

/-- Each coefficient term is continuous in the vertical parameter. -/
theorem continuous_rieszRightTerm
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) {X c : ℝ}
    (hX : 0 < X) (hc : 0 < c) (n : ℕ) :
    Continuous (rieszRightTerm f rho k X c n) := by
  unfold rieszRightTerm
  apply Continuous.mul
  · exact (continuous_rieszKernel_vertical k hc).mul
      ((differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp (by fun_prop))
  · exact continuous_iff_continuousAt.mpr fun t => by
      have hout := (LSeries.hasDerivAt_term f n
        (rho + ((c : ℝ) + t * I))).continuousAt
      have hinner : ContinuousAt (fun u : ℝ =>
          rho + ((c : ℂ) + (u : ℂ) * I)) t := by fun_prop
      exact hout.comp_of_eq hinner rfl

/-- The vertical norm factors into an absolute Dirichlet coefficient, a fixed
power of `X`, and the Riesz kernel envelope. -/
theorem norm_rieszRightTerm_eq
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) {X c : ℝ}
    (hX : 0 < X) (n : ℕ) (t : ℝ) :
    ‖rieszRightTerm f rho k X c n t‖ =
      ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ *
        (X ^ c * ‖rieszMellinKernel k ((c : ℂ) + t * I)‖) := by
  unfold rieszRightTerm
  rw [norm_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  have hterm :
      ‖LSeries.term f (rho + ((c : ℂ) + t * I)) n‖ =
        ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  rw [hterm]
  simp
  ring

/-- Every coefficient is Bochner integrable on the initial vertical line. -/
theorem integrable_rieszRightTerm
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c) (n : ℕ) :
    Integrable (rieszRightTerm f rho k X c n) := by
  have hker : Integrable (fun t : ℝ =>
      rieszMellinKernel k ((c : ℂ) + t * I)) :=
    verticalIntegrable_rieszMellinKernel k hk hc
  have hnorm : Integrable (fun t : ℝ =>
      ‖rieszMellinKernel k ((c : ℂ) + t * I)‖) := hker.norm
  let C : ℝ := ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ * X ^ c
  have hdom : Integrable (fun t : ℝ =>
      C * ‖rieszMellinKernel k ((c : ℂ) + t * I)‖) := hnorm.const_mul C
  apply hdom.mono'
  · exact (continuous_rieszRightTerm f rho k hX hc n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [norm_rieszRightTerm_eq f rho k hX]
      dsimp [C]
      ring_nf
      exact le_rfl)

/-- Tonelli's summability condition for the Riesz-smoothed series. -/
theorem summable_integral_norm_rieszRightTerm
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c)
    (hs : LSeriesSummable f (((rho.re + c : ℝ) : ℂ))) :
    Summable fun n : ℕ => ∫ t : ℝ, ‖rieszRightTerm f rho k X c n t‖ := by
  let K : ℝ := ∫ t : ℝ, ‖rieszMellinKernel k ((c : ℂ) + t * I)‖
  have hnorm : Summable fun n : ℕ =>
      ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ := summable_norm_iff.mpr hs
  have hscaled : Summable fun n : ℕ =>
      ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ * (X ^ c * K) :=
    hnorm.mul_right (X ^ c * K)
  apply hscaled.congr
  intro n
  rw [show (fun t : ℝ => ‖rieszRightTerm f rho k X c n t‖) =
      (fun t : ℝ =>
        (‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ * X ^ c) *
          ‖rieszMellinKernel k ((c : ℂ) + t * I)‖) by
        funext t
        rw [norm_rieszRightTerm_eq f rho k hX]
        ring]
  rw [MeasureTheory.integral_const_mul]
  dsimp [K]
  ring

/-- Pointwise the coefficient series sums to the literal L-series integrand. -/
theorem tsum_rieszRightTerm_eq_rieszRightIntegrand
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (X c : ℝ) (t : ℝ) :
    (∑' n : ℕ, rieszRightTerm f rho k X c n t) =
      rieszRightIntegrand f rho k X c t := by
  unfold rieszRightTerm rieszRightIntegrand LSeries
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left]

/-- Exact series/integral interchange on the initial Riesz line. -/
theorem riesz_right_line_series_integral_identity
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c)
    (hs : LSeriesSummable f (((rho.re + c : ℝ) : ℂ))) :
    ∑' n : ℕ, ∫ t : ℝ, rieszRightTerm f rho k X c n t =
      ∫ t : ℝ, rieszRightIntegrand f rho k X c t := by
  calc
    ∑' n : ℕ, ∫ t : ℝ, rieszRightTerm f rho k X c n t =
        ∫ t : ℝ, ∑' n : ℕ, rieszRightTerm f rho k X c n t :=
      MeasureTheory.integral_tsum_of_summable_integral_norm
        (fun n => integrable_rieszRightTerm f rho k hk hX hc n)
        (summable_integral_norm_rieszRightTerm f rho k hk hX hc hs)
    _ = ∫ t : ℝ, rieszRightIntegrand f rho k X c t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (tsum_rieszRightTerm_eq_rieszRightIntegrand f rho k X c)

/-- The full L-series integrand is integrable on the initial line. -/
theorem integrable_rieszRightIntegrand
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c)
    (hs : LSeriesSummable f (((rho.re + c : ℝ) : ℂ))) :
    Integrable (rieszRightIntegrand f rho k X c) := by
  have hcoeff : Summable fun n : ℕ =>
      ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ :=
    summable_norm_iff.mpr hs
  let C : ℝ := (∑' n : ℕ,
      ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖) * X ^ c
  have hker : Integrable (fun t : ℝ =>
      rieszMellinKernel k ((c : ℂ) + t * I)) :=
    verticalIntegrable_rieszMellinKernel k hk hc
  have hdom : Integrable (fun t : ℝ =>
      C * ‖rieszMellinKernel k ((c : ℂ) + t * I)‖) :=
    hker.norm.const_mul C
  apply hdom.mono'
  · have hmeas : AEStronglyMeasurable (fun t : ℝ =>
        ∑' n : ℕ, rieszRightTerm f rho k X c n t) :=
      AEStronglyMeasurable.tsum (fun n =>
        (continuous_rieszRightTerm f rho k hX hc n).aestronglyMeasurable)
    exact hmeas.congr (Filter.Eventually.of_forall fun t =>
      tsum_rieszRightTerm_eq_rieszRightIntegrand f rho k X c t)
  · exact Filter.Eventually.of_forall fun t => by
      have hpoint : Summable fun n : ℕ =>
          ‖rieszRightTerm f rho k X c n t‖ := by
        have hscaled := hcoeff.mul_right
          (X ^ c * ‖rieszMellinKernel k ((c : ℂ) + t * I)‖)
        exact hscaled.congr (fun n => by
          rw [norm_rieszRightTerm_eq f rho k hX])
      rw [← tsum_rieszRightTerm_eq_rieszRightIntegrand f rho k X c t]
      refine (norm_tsum_le_tsum_norm hpoint).trans_eq ?_
      rw [show (fun n : ℕ => ‖rieszRightTerm f rho k X c n t‖) =
          (fun n : ℕ =>
            ‖LSeries.term f ((rho.re + c : ℝ) : ℂ) n‖ *
              (X ^ c * ‖rieszMellinKernel k ((c : ℂ) + t * I)‖)) by
        funext n
        rw [norm_rieszRightTerm_eq f rho k hX]]
      rw [tsum_mul_right]
      dsimp [C]
      ring

/-- The inverse-power presentation used by Mellin inversion. -/
theorem div_cpow_eq_inv_scale_cpow
    {X y : ℝ} (hX : 0 < X) (hy : 0 < y) (z : ℂ) :
    ((X / y : ℝ) : ℂ) ^ z = ((y / X : ℝ) : ℂ) ^ (-z) := by
  rw [Complex.cpow_neg]
  rw [MAPAppendixA4GammaEndpoint.ofReal_div_cpow hX hy]
  rw [MAPAppendixA4GammaEndpoint.ofReal_div_cpow hy hX]
  have hXc : (X : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hyc : ((y : ℂ) ^ z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  field_simp

/-- One coefficient of the normalized vertical integral is exactly its Riesz
weight. -/
theorem normalized_integral_rieszRightTerm_eq
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c) (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, rieszRightTerm f rho k X c n t) =
      LSeries.term f rho n * rieszWeight k ((n : ℝ) / X) := by
  by_cases hn : n = 0
  · subst n
    simp [rieszRightTerm]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hMellin := inverseMellin_integral_rieszKernel k hk hc
      (div_pos hnpos hX)
    rw [show (fun t : ℝ => rieszRightTerm f rho k X c n t) =
        (fun t : ℝ => LSeries.term f rho n *
          (((((n : ℝ) / X : ℝ) : ℂ) ^
              (-((c : ℂ) + t * I))) *
            rieszMellinKernel k ((c : ℂ) + t * I))) by
      funext t
      rw [rieszRightTerm_eq_arithmeticCoeff_mul f rho k hX hn t]
      rw [div_cpow_eq_inv_scale_cpow hX hnpos]
      ring]
    rw [MeasureTheory.integral_const_mul]
    have hMellin' :
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            ((((n : ℝ) / X : ℝ) : ℂ) ^ (-((c : ℂ) + t * I))) *
              rieszMellinKernel k ((c : ℂ) + t * I)) =
            rieszWeight k ((n : ℝ) / X) := by
      simpa only [smul_eq_mul] using hMellin
    calc
      _ = LSeries.term f rho n *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ,
              ((((n : ℝ) / X : ℝ) : ℂ) ^ (-((c : ℂ) + t * I))) *
                rieszMellinKernel k ((c : ℂ) + t * I))) := by ring
      _ = LSeries.term f rho n * rieszWeight k ((n : ℝ) / X) := by rw [hMellin']

/-- The Riesz-smoothed arithmetic term. -/
def goldfeldRieszTerm (f : ℕ → ℂ) (rho : ℂ) (k : ℕ)
    (X : ℝ) (n : ℕ) : ℂ :=
  LSeries.term f rho n * rieszWeight k ((n : ℝ) / X)

/-- The smoothed arithmetic series is summable as a consequence of the
right-line Bochner majorant. -/
theorem summable_goldfeldRieszTerm
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c)
    (hs : LSeriesSummable f (((rho.re + c : ℝ) : ℂ))) :
    Summable (goldfeldRieszTerm f rho k X) := by
  have hnormsum := summable_integral_norm_rieszRightTerm f rho k hk hX hc hs
  have hintNorm : Summable fun n : ℕ =>
      ‖∫ t : ℝ, rieszRightTerm f rho k X c n t‖ := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => MeasureTheory.norm_integral_le_integral_norm
        (rieszRightTerm f rho k X c n)) hnormsum
  have hint : Summable fun n : ℕ =>
      ∫ t : ℝ, rieszRightTerm f rho k X c n t :=
    summable_norm_iff.mp hintNorm
  have hscaled := hint.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  exact hscaled.congr (fun n =>
    normalized_integral_rieszRightTerm_eq f rho k hk hX hc n)

/-- **Exact smoothed Mellin identity.** -/
theorem normalized_riesz_right_line_eq_arithmetic_tsum
    (f : ℕ → ℂ) (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c)
    (hs : LSeriesSummable f (((rho.re + c : ℝ) : ℂ))) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, rieszRightIntegrand f rho k X c t) =
        ∑' n : ℕ, goldfeldRieszTerm f rho k X n := by
  rw [← riesz_right_line_series_integral_identity f rho k hk hX hc hs]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact normalized_integral_rieszRightTerm_eq f rho k hk hX hc n

/-- Specialization of the exact smoothed identity to Goldfeld's fourfold
Dirichlet series. -/
theorem normalized_goldfeld_fourfold_right_line
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (rho : ℂ) (k : ℕ) (hk : 1 ≤ k)
    {X c : ℝ} (hX : 0 < X) (hc : 0 < c)
    (hs : 1 < rho.re + c) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ,
        rieszMellinKernel k ((c : ℂ) + t * I) *
          (X : ℂ) ^ ((c : ℂ) + t * I) *
          (riemannZeta (rho + ((c : ℂ) + t * I)) *
            DirichletCharacter.LFunction chi (rho + ((c : ℂ) + t * I)) *
            DirichletCharacter.LFunction psi (rho + ((c : ℂ) + t * I)) *
            DirichletCharacter.LFunction (chi * psi)
              (rho + ((c : ℂ) + t * I)))) =
      ∑' n : ℕ,
        goldfeldRieszTerm (fun n => goldfeldFourfoldCoeff chi psi n)
          rho k X n := by
  have hsLS : LSeriesSummable (fun n => goldfeldFourfoldCoeff chi psi n)
      (((rho.re + c : ℝ) : ℂ)) := by
    let z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
    let a : ArithmeticFunction ℂ := toArithmeticFunction (chi ·)
    let b : ArithmeticFunction ℂ := toArithmeticFunction (psi ·)
    let d : ArithmeticFunction ℂ := toArithmeticFunction ((chi * psi) ·)
    have hz : LSeriesSummable (fun n => z n) (((rho.re + c : ℝ) : ℂ)) := by
      simpa [z] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    have ha : LSeriesSummable (fun n => a n) (((rho.re + c : ℝ) : ℂ)) := by
      exact (LSeriesSummable_congr _ fun hn =>
        chi.apply_eq_toArithmeticFunction_apply hn).mp
          (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
    have hb : LSeriesSummable (fun n => b n) (((rho.re + c : ℝ) : ℂ)) := by
      exact (LSeriesSummable_congr _ fun hn =>
        psi.apply_eq_toArithmeticFunction_apply hn).mp
          (DirichletCharacter.LSeriesSummable_of_one_lt_re psi hs)
    have hd : LSeriesSummable (fun n => d n) (((rho.re + c : ℝ) : ℂ)) := by
      exact (LSeriesSummable_congr _ fun hn =>
        (chi * psi).apply_eq_toArithmeticFunction_apply hn).mp
          (DirichletCharacter.LSeriesSummable_of_one_lt_re (chi * psi) hs)
    exact ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hz ha) hb) hd
  rw [← normalized_riesz_right_line_eq_arithmetic_tsum
    (fun n => goldfeldFourfoldCoeff chi psi n) rho k hk hX hc hsLS]
  congr 2
  funext t
  ·
    unfold rieszRightIntegrand
    rw [LSeries_goldfeldFourfoldCoeff_eq chi psi]
    · simpa using hs

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.normalized_riesz_right_line_eq_arithmetic_tsum
#print axioms MAPGoldfeldSiegel.normalized_goldfeld_fourfold_right_line
