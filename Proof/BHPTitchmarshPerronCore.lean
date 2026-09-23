import BHPRademacherTitchmarshSources
import SharpFinitePerronStep
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The absolutely convergent core of Titchmarsh 3.19 for BHP

This module expands the literal BHP right edge into its full Dirichlet series,
commutes that absolutely convergent series through the finite vertical
integral, and identifies each coefficient with the already certified sharp
finite Perron kernel.  Thus the only part of Titchmarsh 3.19 left after this
file is the elementary arithmetic summation of the coefficientwise
`1/(pi T |log(X/n)|)` errors (including the endpoint `n=X`).
-/

namespace MAPBHPTitchmarshPerronCore

open Set MeasureTheory Metric TopologicalSpace PerronKernel
open scoped BigOperators Interval LSeries.notation
open MAPBHPCorrectedContourShift
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTLemma211AllCharacterSource

noncomputable section

/-- The `n`th summand of the BHP right-edge integrand. -/
def bhpRightPerronTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (X t c : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (fun n : ℕ => chi n)
      (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I) n *
    verticalPower X c u / ((c : ℂ) + Complex.I * u)

theorem continuous_bhpRightPerronTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {X t c : ℝ} (hX : 0 < X) (hc : 0 < c) (n : ℕ) :
    Continuous (bhpRightPerronTerm chi X t c n) := by
  unfold bhpRightPerronTerm verticalPower
  apply Continuous.div
  · apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr fun u => by
        have houter := (LSeries.hasDerivAt_term (fun n : ℕ => chi n) n
          (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I)).continuousAt
        have hinner : ContinuousAt (fun v : ℝ =>
            (((1 / 2 + c : ℝ) : ℂ) + (t + v) * Complex.I)) u := by
          fun_prop
        have hcomp : ContinuousAt
            ((fun z : ℂ => LSeries.term (fun n : ℕ => chi n) z n) ∘
              (fun v : ℝ =>
                (((1 / 2 + c : ℝ) : ℂ) + (t + v) * Complex.I))) u :=
          ContinuousAt.comp_of_eq houter hinner rfl
        simpa only [Function.comp_apply] using! hcomp
    · fun_prop
  · fun_prop
  · exact fun u => denominator_ne_zero hc

theorem norm_bhpRightPerronTerm_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {X t c : ℝ} (hX : 0 < X) (hc : 0 < c) (n : ℕ) (u : ℝ) :
    ‖bhpRightPerronTerm chi X t c n u‖ ≤
      ‖LSeries.term (fun n : ℕ => chi n)
          ((1 / 2 + c : ℝ) : ℂ) n‖ * (X ^ c / c) := by
  rw [bhpRightPerronTerm, norm_div, norm_mul, norm_verticalPower hX]
  have hterm :
      ‖LSeries.term (fun n : ℕ => chi n)
          (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I) n‖ =
        ‖LSeries.term (fun n : ℕ => chi n)
          ((1 / 2 + c : ℝ) : ℂ) n‖ := by
    simp [LSeries.norm_term_eq]
  rw [hterm]
  have hden := c_le_norm_denominator (t := u) hc.le
  exact calc
    ‖LSeries.term (fun n : ℕ => chi n)
          ((1 / 2 + c : ℝ) : ℂ) n‖ * X ^ c /
        ‖(c : ℂ) + Complex.I * u‖ ≤
      ‖LSeries.term (fun n : ℕ => chi n)
          ((1 / 2 + c : ℝ) : ℂ) n‖ * X ^ c / c := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hX.le _)) hc hden
    _ = _ := by ring

/-- The whole right-edge coefficient family is uniformly summable on every
finite height interval once `1/2+c>1`. -/
theorem summable_restricted_bhpRightPerronTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {X t c T : ℝ} (hX : 0 < X) (hc : 1 / 2 < c) :
    Summable fun n : ℕ =>
      ‖(ContinuousMap.mk (bhpRightPerronTerm chi X t c n)
          (continuous_bhpRightPerronTerm chi hX (by linarith) n)).restrict
        (⟨uIcc (-T) T, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
  let b : ℕ → ℝ := fun n =>
    ‖LSeries.term (fun n : ℕ => chi n)
      ((1 / 2 + c : ℝ) : ℂ) n‖ * (X ^ c / c)
  have hs : LSeriesSummable (fun n : ℕ => chi n)
      ((1 / 2 + c : ℝ) : ℂ) := by
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re chi (by simp; linarith)
  have hb : Summable b :=
    (summable_norm_iff.mpr hs).mul_right (X ^ c / c)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hb
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro u
  exact norm_bhpRightPerronTerm_le chi hX (by linarith) n u

/-- Pointwise, the coefficient series is exactly the literal BHP `/w`
integrand on the right edge. -/
theorem tsum_bhpRightPerronTerm_eq_integrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X t c : ℝ} (hX : 0 < X) (hc : 1 / 2 < c) (u : ℝ) :
    (∑' n : ℕ, bhpRightPerronTerm chi X t c n u) =
      bhpPerronIntegrand chi X t ((c : ℂ) + Complex.I * u) := by
  unfold bhpRightPerronTerm bhpPerronIntegrand
  have hsre : 1 <
      (((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
        ((c : ℂ) + Complex.I * u))).re := by simp; linarith
  rw [DirichletCharacter.LFunction_eq_LSeries chi hsre]
  rw [PerronKernel.verticalPower_eq_exp hX]
  have harg :
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
        ((c : ℂ) + Complex.I * u)) =
      (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I) := by
    push_cast
    ring
  rw [harg]
  unfold LSeries
  simp only [div_eq_mul_inv, mul_assoc]
  rw [tsum_mul_right]

/-- Exact countable-sum/finite-integral interchange for BHP's right line. -/
theorem bhpVerticalLineIntegral_eq_tsum_integrals
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X t c T : ℝ} (hX : 0 < X) (hc : 1 / 2 < c) :
    bhpVerticalLineIntegral chi X t c T =
      ∑' n : ℕ, (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ u in (-T)..T, bhpRightPerronTerm chi X t c n u := by
  let F : ℕ → C(ℝ, ℂ) := fun n =>
    ContinuousMap.mk (bhpRightPerronTerm chi X t c n)
      (continuous_bhpRightPerronTerm chi hX (by linarith) n)
  have hsum : Summable fun n : ℕ =>
      ‖(F n).restrict (⟨uIcc (-T) T, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    simpa only [F] using
      summable_restricted_bhpRightPerronTerm chi hX hc (t := t) (T := T)
  rw [bhpVerticalLineIntegral, tsum_mul_left]
  congr 1
  calc
    (∫ u in (-T)..T,
        bhpPerronIntegrand chi X t ((c : ℂ) + Complex.I * u)) =
      ∫ u in (-T)..T, ∑' n : ℕ, F n u := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact (tsum_bhpRightPerronTerm_eq_integrand chi hX hc u).symm
    _ = ∑' n : ℕ, ∫ u in (-T)..T, F n u :=
      (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum).symm
    _ = ∑' n : ℕ, ∫ u in (-T)..T,
        bhpRightPerronTerm chi X t c n u := by rfl

/-- The exact critical-line L-series coefficient before Perron smoothing. -/
def bhpCriticalLSeriesCoefficient {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (fun n : ℕ => chi n)
    (((1 / 2 : ℝ) : ℂ) + t * Complex.I) n

/-- Branch-sensitive factorization of one nonzero coefficient into its
critical-line L-series value and the positive real Perron ratio. -/
theorem bhpRightPerronTerm_eq_coefficient_mul_verticalIntegrand
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {X t c : ℝ} (hX : 0 < X) (hc : 0 < c)
    {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    bhpRightPerronTerm chi X t c n u =
      bhpCriticalLSeriesCoefficient chi t n *
        verticalIntegrand (X / n) c u := by
  unfold bhpRightPerronTerm bhpCriticalLSeriesCoefficient
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    verticalIntegrand]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [PerronKernel.verticalPower_eq_exp hX,
    PerronKernel.verticalPower_eq_exp (div_pos hX hnpos)]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  rw [Real.log_div hX.ne' hnpos.ne']
  rw [← Complex.natCast_log]
  have hexp :
      Complex.exp (((c : ℂ) + Complex.I * u) * Real.log X) *
          Complex.exp ((Real.log (n : ℝ) : ℂ) *
            (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) =
        Complex.exp ((Real.log (n : ℝ) : ℂ) *
            (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I)) *
          Complex.exp (((c : ℂ) + Complex.I * u) *
            (Real.log X - Real.log (n : ℝ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnum :
      chi n /
          Complex.exp ((Real.log (n : ℝ) : ℂ) *
            (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I)) *
          Complex.exp (((c : ℂ) + Complex.I * u) * Real.log X) =
        chi n /
          Complex.exp ((Real.log (n : ℝ) : ℂ) *
            (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) *
          Complex.exp (((c : ℂ) + Complex.I * u) *
            (Real.log X - Real.log (n : ℝ))) := by
    field_simp [Complex.exp_ne_zero]
    convert congrArg (fun z : ℂ => chi n * z) hexp using 1 <;>
      simp only [Complex.natCast_log] <;>
      ring_nf
  calc
    chi n /
          Complex.exp ((Real.log (n : ℝ) : ℂ) *
            (((1 / 2 + c : ℝ) : ℂ) + (t + u) * Complex.I)) *
          Complex.exp (((c : ℂ) + Complex.I * u) * Real.log X) /
        ((c : ℂ) + Complex.I * u) =
      (chi n /
          Complex.exp ((Real.log (n : ℝ) : ℂ) *
            (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) *
          Complex.exp (((c : ℂ) + Complex.I * u) *
            (Real.log X - Real.log (n : ℝ)))) /
        ((c : ℂ) + Complex.I * u) := congrArg
          (fun z : ℂ => z / ((c : ℂ) + Complex.I * u)) hnum
    _ = _ := by
      rw [Complex.ofReal_sub]
      exact mul_div_assoc _ _ _

/-- The right edge is the infinite sum of the exact critical coefficients
times the certified finite Perron kernels. -/
theorem bhpVerticalLineIntegral_eq_tsum_kernels
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X t c T : ℝ} (hX : 0 < X) (hc : 1 / 2 < c) :
    bhpVerticalLineIntegral chi X t c T =
      ∑' n : ℕ,
        bhpCriticalLSeriesCoefficient chi t n *
          PerronKernel.kernel (X / n) c T := by
  rw [bhpVerticalLineIntegral_eq_tsum_integrals chi hX hc]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [bhpRightPerronTerm, bhpCriticalLSeriesCoefficient]
  · simp_rw [bhpRightPerronTerm_eq_coefficient_mul_verticalIntegrand
      chi hX (by linarith) hn]
    rw [intervalIntegral.integral_const_mul, PerronKernel.kernel]
    ring

end
end MAPBHPTitchmarshPerronCore

#print axioms MAPBHPTitchmarshPerronCore.bhpVerticalLineIntegral_eq_tsum_integrals
#print axioms MAPBHPTitchmarshPerronCore.bhpRightPerronTerm_eq_coefficient_mul_verticalIntegrand
#print axioms MAPBHPTitchmarshPerronCore.bhpVerticalLineIntegral_eq_tsum_kernels
