import KhaleAppendixBLemma41NaturalScales
import KhaleZetaNearOneSourceReduction

/-!
# The sharp real-axis zeta leaf in Khale Appendix B

Khale's four-height argument needs the coefficient-sharp estimate

`-ζ'(σ) / ζ(σ) ≤ 1 / (σ - 1)` for `σ > 1`.

The exact von Mangoldt `L`-series identity is already in Mathlib.  The missing
analytic content is more cleanly exposed one step earlier: the normalized
real-axis zeta function `(σ - 1) ζ(σ)` has nonnegative derivative.  The theorem
below certifies the complete deterministic passage from that statement to the
exact Appendix-B interface.  No additive explicit-formula remainder is used.
-/

namespace MAPKhaleZetaLogDerivativeSharp

open Complex

noncomputable section

/-- Earliest exact analytic leaf in the monotonicity proof of Ford's sharp
real-axis zeta estimate.  This is a derivative statement about the normalized
zeta function, rather than a restatement involving its logarithmic derivative.

A zero-argument proof should establish this from the positive Dirichlet series
or an integral representation of zeta. -/
abbrev NormalizedRiemannZetaDerivativeNonnegative : Prop :=
  ∀ sigma : ℝ, 1 < sigma →
    0 ≤ (deriv (fun s : ℂ => (s - 1) * riemannZeta s) (sigma : ℂ)).re

/-- The corresponding restricted leaf for the only range used by the Khale
natural-scale application.  The current parameter inequalities actually give
a smaller upper bound than `1 / 1000`; this round value leaves ample slack. -/
abbrev NormalizedRiemannZetaDerivativeNonnegativeNearOne : Prop :=
  ∀ sigma : ℝ, 1 < sigma → sigma - 1 ≤ 1 / 1000 →
    0 ≤ (deriv (fun s : ℂ => (s - 1) * riemannZeta s) (sigma : ℂ)).re

/-- The Appendix-B auxiliary point lies inside the restricted zeta range.
This is the exact numerical bridge needed to replace the unnecessarily global
zeta premise in the natural-scale constructor. -/
theorem appendixB_sigmaAux_sub_one_le_one_thousandth
    {delta eta : ℝ} (heta : 0 < eta)
    (hetaTop : eta ≤ 0.06) (hdeltaEta : delta / eta ≤ 0.0029) :
    (1 + 3.238 * delta) - 1 ≤ 1 / 1000 := by
  have hdelta : delta ≤ 0.0029 * eta :=
    (div_le_iff₀ heta).mp hdeltaEta
  have hscaled : 3.238 * delta ≤ 3.238 * (0.0029 * eta) :=
    mul_le_mul_of_nonneg_left hdelta (by norm_num)
  have hetaScaled : 3.238 * (0.0029 * eta) ≤
      3.238 * (0.0029 * 0.06) := by
    gcongr
  norm_num at hscaled hetaScaled ⊢
  linarith

/-- Pointwise product-rule adapter from normalized-zeta derivative positivity
to the sharp logarithmic-derivative estimate. -/
theorem sharp_zeta_logDerivative_of_normalized_derivative_at
    {sigma : ℝ} (hsigma : 1 < sigma)
    (hnonneg :
      0 ≤ (deriv (fun s : ℂ => (s - 1) * riemannZeta s) (sigma : ℂ)).re) :
    (-logDeriv riemannZeta (sigma : ℂ)).re ≤ 1 / (sigma - 1) := by
  have hsne : (sigma : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzetaDiff : DifferentiableAt ℂ riemannZeta (sigma : ℂ) :=
    differentiableAt_riemannZeta hsne
  have hlinDiff : DifferentiableAt ℂ (fun s : ℂ => s - 1) (sigma : ℂ) :=
    differentiableAt_id.sub_const 1
  have hderiv := deriv_mul hlinDiff hzetaDiff
  change 0 ≤
    (deriv ((fun s : ℂ => s - 1) * riemannZeta) (sigma : ℂ)).re at hnonneg
  rw [hderiv] at hnonneg
  simp only [deriv_sub_const, deriv_id'', one_mul] at hnonneg
  have hzetaPos : 0 < (riemannZeta (sigma : ℂ)).re := by
    simpa using riemannZeta_re_pos_of_one_lt hsigma
  have hzetaReal : (riemannZeta (sigma : ℂ)).im = 0 := by
    simpa using riemannZeta_im_eq_zero_of_one_lt hsigma
  have hprodRe :
      (((sigma : ℂ) - 1) * deriv riemannZeta (sigma : ℂ)).re =
        (sigma - 1) * (deriv riemannZeta (sigma : ℂ)).re := by
    simp
  simp only [Complex.add_re] at hnonneg
  rw [hprodRe] at hnonneg
  have hlog :
      (-logDeriv riemannZeta (sigma : ℂ)).re =
        -(deriv riemannZeta (sigma : ℂ)).re /
          (riemannZeta (sigma : ℂ)).re := by
    rw [logDeriv_apply]
    simp only [Complex.neg_re]
    rw [Complex.div_re, hzetaReal, Complex.normSq_apply, hzetaReal]
    norm_num
    field_simp [hzetaPos.ne']
  rw [hlog]
  rw [div_le_iff₀ hzetaPos, one_div_mul_eq_div]
  have hsig : 0 < sigma - 1 := by linarith
  apply (le_div_iff₀ hsig).2
  nlinarith

/-- Exact global adapter to Ford's sharp real-axis estimate. -/
theorem sharp_zeta_logDerivative_of_normalized_derivative
    (hmono : NormalizedRiemannZetaDerivativeNonnegative) :
    ∀ sigma : ℝ, 1 < sigma →
      (-logDeriv riemannZeta (sigma : ℂ)).re ≤ 1 / (sigma - 1) := by
  intro sigma hsigma
  exact sharp_zeta_logDerivative_of_normalized_derivative_at hsigma
    (hmono sigma hsigma)

/-- Restricted version of the same deterministic adapter. -/
theorem sharp_zeta_logDerivative_nearOne_of_normalized_derivative
    (hmono : NormalizedRiemannZetaDerivativeNonnegativeNearOne) :
    ∀ sigma : ℝ, 1 < sigma → sigma - 1 ≤ 1 / 1000 →
      (-logDeriv riemannZeta (sigma : ℂ)).re ≤ 1 / (sigma - 1) := by
  intro sigma hsigma hsigmaTop
  exact sharp_zeta_logDerivative_of_normalized_derivative_at hsigma
    (hmono sigma hsigma hsigmaTop)

/-- Source-facing completion from the global normalized-zeta statement. -/
theorem fordLemma31ZetaLogDerivativeBound_of_normalized_derivative
    (hmono : NormalizedRiemannZetaDerivativeNonnegative) :
    MAPKhaleAppendixBLemma41NaturalScales.FordLemma31ZetaLogDerivativeBound := by
  intro sigma hsigma _hsigmaTop
  exact sharp_zeta_logDerivative_of_normalized_derivative hmono sigma hsigma

/-- Source-facing completion from only the near-one statement actually used
by the Appendix-B natural-scale constructor. -/
theorem fordLemma31ZetaLogDerivativeBound_of_normalized_derivative_nearOne
    (hmono : NormalizedRiemannZetaDerivativeNonnegativeNearOne) :
    MAPKhaleAppendixBLemma41NaturalScales.FordLemma31ZetaLogDerivativeBound := by
  intro sigma hsigma hsigmaTop
  apply sharp_zeta_logDerivative_nearOne_of_normalized_derivative hmono sigma hsigma
  linarith

/-- End-to-end deterministic adapter from the two literal sum--integral
inequalities to the exact zeta input consumed by Appendix B. -/
theorem fordLemma31ZetaLogDerivativeBound_of_sumIntegral
    (hsource :
      MAPKhaleZetaNearOneSourceReduction.NearOneZetaSumIntegralBounds) :
    MAPKhaleAppendixBLemma41NaturalScales.FordLemma31ZetaLogDerivativeBound :=
  fordLemma31ZetaLogDerivativeBound_of_normalized_derivative_nearOne
    (MAPKhaleZetaNearOneSourceReduction.normalizedRiemannZetaDerivativeNonnegativeNearOne_of_sumIntegral
      hsource)

end

end MAPKhaleZetaLogDerivativeSharp

#print axioms MAPKhaleZetaLogDerivativeSharp.sharp_zeta_logDerivative_of_normalized_derivative
#print axioms MAPKhaleZetaLogDerivativeSharp.fordLemma31ZetaLogDerivativeBound_of_normalized_derivative
#print axioms MAPKhaleZetaLogDerivativeSharp.fordLemma31ZetaLogDerivativeBound_of_normalized_derivative_nearOne
#print axioms MAPKhaleZetaLogDerivativeSharp.fordLemma31ZetaLogDerivativeBound_of_sumIntegral
