import KhaleZetaNearOneCore
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Exact source interface for the near-one zeta sum--integral comparison

The remaining proposition contains the two literal inequalities delivered by
the Dirichlet-series integral test.  It is not a reformulation of the desired
logarithmic-derivative bound.  The theorem below proves, kernel-checkably, that
these inequalities imply positivity of the normalized zeta derivative.
-/

namespace MAPKhaleZetaNearOneSourceReduction

open Complex

noncomputable section

abbrev NearOneZetaSumIntegralBounds : Prop :=
  ∀ sigma : ℝ, 1 < sigma → sigma ≤ 1.001 →
    1 + (2 : ℝ) ^ (-sigma : ℝ) +
        (3 : ℝ) ^ (1 - sigma : ℝ) / (sigma - 1) ≤
      (riemannZeta (sigma : ℂ)).re ∧
    -(deriv riemannZeta (sigma : ℂ)).re ≤
      Real.log 2 * (2 : ℝ) ^ (-sigma : ℝ) +
      Real.log 3 * (3 : ℝ) ^ (-sigma : ℝ) +
      (3 : ℝ) ^ (1 - sigma : ℝ) *
        (Real.log 3 / (sigma - 1) + 1 / (sigma - 1) ^ 2)

abbrev NormalizedRiemannZetaDerivativeNonnegativeNearOne : Prop :=
  ∀ sigma : ℝ, 1 < sigma → sigma - 1 ≤ 1 / 1000 →
    0 ≤ (deriv (fun s : ℂ => (s - 1) * riemannZeta s) (sigma : ℂ)).re

theorem normalizedRiemannZetaDerivativeNonnegativeNearOne_of_sumIntegral
    (hsource : NearOneZetaSumIntegralBounds) :
    NormalizedRiemannZetaDerivativeNonnegativeNearOne := by
  intro sigma hsigma hsigmaDelta
  have hsigmaTop : sigma ≤ 1.001 := by
    norm_num at hsigmaDelta ⊢
    linarith
  obtain ⟨hzeta, hderiv⟩ := hsource sigma hsigma hsigmaTop
  let delta : ℝ := sigma - 1
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hdeltaTop : delta ≤ 1 / 1000 := by simpa [delta] using hsigmaDelta
  have hzeta' : 1 + (2 : ℝ) ^ (-(1 + delta) : ℝ) +
      (3 : ℝ) ^ (-delta : ℝ) / delta ≤
        (riemannZeta (sigma : ℂ)).re := by
    simpa [delta] using hzeta
  have hderiv' : -(deriv riemannZeta (sigma : ℂ)).re ≤
      Real.log 2 * (2 : ℝ) ^ (-(1 + delta) : ℝ) +
      Real.log 3 * (3 : ℝ) ^ (-(1 + delta) : ℝ) +
      (3 : ℝ) ^ (-delta : ℝ) *
        (Real.log 3 / delta + 1 / delta ^ 2) := by
    simpa [delta] using hderiv
  have hreal :=
    MAPKhaleZetaNearOneCore.normalized_nonnegative_of_corrected_sum_integral_bounds
      hdelta hdeltaTop hzeta' hderiv'
  have hsne : (sigma : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzetaDiff : DifferentiableAt ℂ riemannZeta (sigma : ℂ) :=
    differentiableAt_riemannZeta hsne
  have hlinDiff : DifferentiableAt ℂ (fun s : ℂ => s - 1) (sigma : ℂ) :=
    differentiableAt_id.sub_const 1
  have hprod := deriv_mul hlinDiff hzetaDiff
  change 0 ≤ (deriv ((fun s : ℂ => s - 1) * riemannZeta) (sigma : ℂ)).re
  rw [hprod]
  simp only [deriv_sub_const, deriv_id'', one_mul, Complex.add_re]
  have hprodRe :
      (((sigma : ℂ) - 1) * deriv riemannZeta (sigma : ℂ)).re =
        delta * (deriv riemannZeta (sigma : ℂ)).re := by
    simp [delta]
  rw [hprodRe]
  dsimp only [delta] at hreal ⊢
  linarith

end
end MAPKhaleZetaNearOneSourceReduction

#print axioms MAPKhaleZetaNearOneSourceReduction.normalizedRiemannZetaDerivativeNonnegativeNearOne_of_sumIntegral
