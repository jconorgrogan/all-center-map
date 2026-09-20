import JutilaTwoScaleSmoothing
import JutilaPrimitiveFunctionalEquation

/-!
# Functional-equation rewrite of Jutila's reflected integrand

After moving the two-scale contour to `Re (s+w) = -1/2`, Jutila applies
the primitive Dirichlet functional equation (Acta Arith. 32 (1977), p. 58).
This file certifies that pointwise substitution for the literal contour
integrand.  No bound, series split, or contour-limit assertion is included.
-/

namespace JutilaReflectedFunctionalEquationIntegrand

open Complex DirichletCharacter
open scoped BigOperators LSeries.notation
open JutilaTwoScaleSmoothing
open JutilaPrimitiveFunctionalEquation

noncomputable section

def reflectedDualLFactor
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  ((q : ℂ) ^ ((1 : ℂ) / 2 - z) * rootNumber chi *
      (LFunction chi⁻¹ (1 - z) * gammaFactor chi⁻¹ (1 - z))) /
    gammaFactor chi z

theorem LFunction_eq_reflectedDualLFactor_on_reflectedLine
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : IsPrimitive chi) {z : ℂ}
    (hzre : z.re = -(1 : ℝ) / 2) :
    LFunction chi z = reflectedDualLFactor chi z := by
  have hz : z ≠ 0 := by
    intro hz0
    subst z
    norm_num at hzre
  have hdual : 1 - z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    rw [hzre] at hre
    norm_num at hre
  have hgamma := gammaFactor_ne_zero_on_reflectedLine chi hzre
  have hfe := primitive_LFunction_functionalEquation_on_reflectedLine
    hchi z hzre (Or.inl hz) (Or.inl hdual)
  unfold reflectedDualLFactor
  exact (eq_div_iff hgamma).2 hfe

/-- Literal functional-equation substitution into the two-scale contour
integrand on Jutila's reflected line. -/
theorem twoScaleContourIntegrand_eq_reflected
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : IsPrimitive chi) (s : ℂ) (N h : ℝ) (w : ℂ)
    (hreflected : (s + w).re = -(1 : ℝ) / 2) :
    twoScaleContourIntegrand chi s N h w =
      Complex.Gamma (1 + w / (h : ℂ)) *
        twoScaleRemovableQuotient N w *
          reflectedDualLFactor chi (s + w) := by
  unfold twoScaleContourIntegrand
  rw [LFunction_eq_reflectedDualLFactor_on_reflectedLine hchi hreflected]

theorem dual_LSeries_summable_on_reflectedLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {z : ℂ}
    (hzre : z.re = -(1 : ℝ) / 2) :
    LSeriesSummable (fun n : ℕ => chi⁻¹ n) (1 - z) := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    exact chi⁻¹.norm_le_one (n : ZMod q)
  · simp only [Complex.sub_re, Complex.one_re]
    rw [hzre]
    norm_num

/-- Exact partial-sum/remainder split of the dual Dirichlet series after
the functional equation.  This is the algebraic split at length `M` in
Jutila p.58; estimating the shifted tail is the next analytic leaf. -/
theorem dual_LSeries_eq_partialSum_add_tail
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {z : ℂ}
    (hzre : z.re = -(1 : ℝ) / 2) (M : ℕ) :
    LSeries (fun n : ℕ => chi⁻¹ n) (1 - z) =
      (∑ n ∈ Finset.range M,
        LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n) +
      ∑' n : ℕ,
        LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M) := by
  have hsum := dual_LSeries_summable_on_reflectedLine chi hzre
  unfold LSeriesSummable at hsum
  unfold LSeries
  exact (hsum.sum_add_tsum_nat_add M).symm

end

end JutilaReflectedFunctionalEquationIntegrand

#print axioms JutilaReflectedFunctionalEquationIntegrand.LFunction_eq_reflectedDualLFactor_on_reflectedLine
#print axioms JutilaReflectedFunctionalEquationIntegrand.twoScaleContourIntegrand_eq_reflected
#print axioms JutilaReflectedFunctionalEquationIntegrand.dual_LSeries_eq_partialSum_add_tail
