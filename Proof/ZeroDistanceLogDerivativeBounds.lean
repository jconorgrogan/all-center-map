import PrimitiveContourComponentBounds
import ZeroFreeSiegelBorelBridge

/-!
# Logarithmic derivative bounds with explicit zero distance

The selected Perron rectangle only supplies nonvanishing.  Quantitative
contour bounds also need to record how close a side is to the finite divisor.
This file proves the exact deterministic conversion: the logarithmic
derivative is bounded by the multiplicity mass divided by that explicit
distance, plus the logarithmic derivative of the concrete zero-deflated
function.  No uniform analytic majorant is hidden in a new proposition.
-/

namespace ZeroDistanceLogDerivativeBounds

open Set
open scoped BigOperators
open DirichletZeros PrimitiveExplicitFormulaSpine

noncomputable section

/-- The regularized L-function with the literal compact divisor removed. -/
def compactZeroDeflatedRegularizedLFunction
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (a H : ℝ) (s : ℂ) : ℂ :=
  regularizedLFunction chi s / zeroFactorProduct chi a H s

/-- Literal pole-mass contribution at a certified divisor distance. -/
def compactPoleDistanceMajorant
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (a H d : ℝ) : ℝ :=
  ∑ rho ∈ zeroSupport chi a H,
    (zeroMultiplicity chi a H rho : ℝ) / d

/-- Exact finite-divisor logarithmic-derivative decomposition at any
nonzero point, with no restriction on its real part. -/
theorem neg_logDeriv_regularizedLFunction_eq_compactZeroSum_add_deflated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (a H : ℝ) {s : ℂ}
    (hL : regularizedLFunction chi s ≠ 0) :
    -logDeriv (regularizedLFunction chi) s =
      -(∑ rho ∈ zeroSupport chi a H,
          (zeroMultiplicity chi a H rho : ℂ) / (s - rho)) -
        logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s := by
  have hsupp : s ∉ zeroSupport chi a H := by
    intro hs
    exact hL (regularizedLFunction_eq_zero_of_mem_zeroSupport chi a H hs)
  have hP : zeroFactorProduct chi a H s ≠ 0 :=
    zeroFactorProduct_ne_zero_of_not_mem chi a H hsupp
  have hPdiff : DifferentiableAt ℂ (zeroFactorProduct chi a H) s := by
    change DifferentiableAt ℂ
      (fun z => ∏ rho ∈ zeroSupport chi a H,
        (z - rho) ^ zeroMultiplicity chi a H rho) s
    fun_prop
  have hdiv := logDeriv_div s hL hP
    (differentiable_regularizedLFunction chi).differentiableAt hPdiff
  rw [logDeriv_zeroFactorProduct chi a H hsupp] at hdiv
  change logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s = _ at hdiv
  rw [hdiv]
  ring

/-- The finite pole sum is controlled by its literal multiplicity mass and a
pointwise lower bound for the distance to every divisor point. -/
theorem norm_compactZeroPoleSum_le_of_distance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (a H : ℝ) {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hdist : ∀ rho ∈ zeroSupport chi a H, d ≤ ‖s - rho‖) :
    ‖∑ rho ∈ zeroSupport chi a H,
        (zeroMultiplicity chi a H rho : ℂ) / (s - rho)‖ ≤
      ∑ rho ∈ zeroSupport chi a H,
        (zeroMultiplicity chi a H rho : ℝ) / d := by
  calc
    ‖∑ rho ∈ zeroSupport chi a H,
        (zeroMultiplicity chi a H rho : ℂ) / (s - rho)‖
        ≤ ∑ rho ∈ zeroSupport chi a H,
            ‖(zeroMultiplicity chi a H rho : ℂ) / (s - rho)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ rho ∈ zeroSupport chi a H,
          (zeroMultiplicity chi a H rho : ℝ) / d := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [norm_div, norm_natCast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (hdist rho hrho)

/-- Distance-explicit norm bound for the actual regularized logarithmic
derivative.  The sole remaining analytic quantity is the displayed concrete
zero-deflated logarithmic derivative. -/
theorem norm_logDeriv_regularizedLFunction_le_zeroDistance_add_deflated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (a H : ℝ) {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hL : regularizedLFunction chi s ≠ 0)
    (hdist : ∀ rho ∈ zeroSupport chi a H, d ≤ ‖s - rho‖) :
    ‖logDeriv (regularizedLFunction chi) s‖ ≤
      (∑ rho ∈ zeroSupport chi a H,
          (zeroMultiplicity chi a H rho : ℝ) / d) +
        ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖ := by
  have heq :=
    neg_logDeriv_regularizedLFunction_eq_compactZeroSum_add_deflated
      chi a H hL
  have hpole := norm_compactZeroPoleSum_le_of_distance chi a H hd hdist
  rw [← norm_neg (logDeriv (regularizedLFunction chi) s), heq]
  calc
    ‖-(∑ rho ∈ zeroSupport chi a H,
          (zeroMultiplicity chi a H rho : ℂ) / (s - rho)) -
        logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖
        ≤ ‖∑ rho ∈ zeroSupport chi a H,
              (zeroMultiplicity chi a H rho : ℂ) / (s - rho)‖ +
            ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖ := by
          simpa only [norm_neg] using
            (norm_sub_le
              (-(∑ rho ∈ zeroSupport chi a H,
                (zeroMultiplicity chi a H rho : ℂ) / (s - rho)))
              (logDeriv
                (compactZeroDeflatedRegularizedLFunction chi a H) s))
    _ ≤ (∑ rho ∈ zeroSupport chi a H,
          (zeroMultiplicity chi a H rho : ℝ) / d) +
        ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖ :=
      add_le_add_left hpole _

/-- Nonprincipal specialization for the source L-function itself. -/
theorem norm_logDeriv_LFunction_le_zeroDistance_add_deflated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (a H : ℝ) {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hL : DirichletCharacter.LFunction chi s ≠ 0)
    (hdist : ∀ rho ∈ zeroSupport chi a H, d ≤ ‖s - rho‖) :
    ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤
      (∑ rho ∈ zeroSupport chi a H,
          (zeroMultiplicity chi a H rho : ℝ) / d) +
        ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖ := by
  have hLreg : regularizedLFunction chi s ≠ 0 := by
    simpa [regularizedLFunction, hchi] using hL
  have hbound :=
    norm_logDeriv_regularizedLFunction_le_zeroDistance_add_deflated
      chi a H hd hLreg hdist
  simpa [regularizedLFunction, hchi] using hbound

/-- A selected nonprincipal left edge has an exact contour bound in terms of
its certified distance from the compact divisor and the displayed deflated
logarithmic derivative. -/
theorem norm_leftLineIntegral_le_zeroDistance_add_deflated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {x sigma T a H d R : ℝ} (hx : 0 < x) (hsigma : 0 < sigma)
    (hT : 0 ≤ T) (hd : 0 < d)
    (hL : ∀ u ∈ Set.Icc (-T) T,
      DirichletCharacter.LFunction chi
        ((sigma : ℂ) + Complex.I * u) ≠ 0)
    (hdist : ∀ u ∈ Set.Icc (-T) T,
      ∀ rho ∈ zeroSupport chi a H,
        d ≤ ‖((sigma : ℂ) + Complex.I * u) - rho‖)
    (hdeflated : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ R) :
    ‖PrimitiveTruncatedExplicitFormulaBridge.leftLineIntegral
        chi x sigma T‖ ≤
      T / Real.pi *
        ((compactPoleDistanceMajorant chi a H d + R) *
          x ^ sigma / sigma) := by
  apply PrimitiveContourComponentBounds.norm_leftLineIntegral_le_of_logDeriv
    chi hx hsigma hT
  intro u hu
  exact (norm_logDeriv_LFunction_le_zeroDistance_add_deflated
    chi hchi a H hd (hL u hu) (hdist u hu)).trans
      (by
        simpa [compactPoleDistanceMajorant] using
          add_le_add_right (hdeflated u hu)
            (∑ rho ∈ zeroSupport chi a H,
              (zeroMultiplicity chi a H rho : ℝ) / d))

/-- The same distance-explicit estimate for the selected top and bottom
horizontal sides.  A single `d` is stated explicitly because the finite
aperture selection must provide a family-compatible distance before this
lemma is used in an AP square sum. -/
theorem norm_horizontalBoundaryIntegral_le_zeroDistance_add_deflated
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {x sigma c T a H d R : ℝ} (hx : 1 ≤ x) (hsigmac : sigma ≤ c)
    (hT : 0 < T) (hd : 0 < d)
    (hLtop : ∀ r ∈ Set.Icc sigma c,
      DirichletCharacter.LFunction chi
        ((r : ℂ) + Complex.I * T) ≠ 0)
    (hLbottom : ∀ r ∈ Set.Icc sigma c,
      DirichletCharacter.LFunction chi
        ((r : ℂ) - Complex.I * T) ≠ 0)
    (hdistTop : ∀ r ∈ Set.Icc sigma c,
      ∀ rho ∈ zeroSupport chi a H,
        d ≤ ‖((r : ℂ) + Complex.I * T) - rho‖)
    (hdistBottom : ∀ r ∈ Set.Icc sigma c,
      ∀ rho ∈ zeroSupport chi a H,
        d ≤ ‖((r : ℂ) - Complex.I * T) - rho‖)
    (hdeflatedTop : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H)
        ((r : ℂ) + Complex.I * T)‖ ≤ R)
    (hdeflatedBottom : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H)
        ((r : ℂ) - Complex.I * T)‖ ≤ R) :
    ‖PrimitiveTruncatedExplicitFormulaBridge.horizontalBoundaryIntegral
        chi x sigma c T‖ ≤
      (c - sigma) / Real.pi *
        ((compactPoleDistanceMajorant chi a H d + R) * x ^ c / T) := by
  apply
    PrimitiveContourComponentBounds.norm_horizontalBoundaryIntegral_le_of_logDeriv
      chi hx hsigmac hT
  · intro r hr
    exact (norm_logDeriv_LFunction_le_zeroDistance_add_deflated
      chi hchi a H hd (hLtop r hr) (hdistTop r hr)).trans
        (by
          simpa [compactPoleDistanceMajorant] using
            add_le_add_right (hdeflatedTop r hr)
              (∑ rho ∈ zeroSupport chi a H,
                (zeroMultiplicity chi a H rho : ℝ) / d))
  · intro r hr
    exact (norm_logDeriv_LFunction_le_zeroDistance_add_deflated
      chi hchi a H hd (hLbottom r hr) (hdistBottom r hr)).trans
        (by
          simpa [compactPoleDistanceMajorant] using
            add_le_add_right (hdeflatedBottom r hr)
              (∑ rho ∈ zeroSupport chi a H,
                (zeroMultiplicity chi a H rho : ℝ) / d))

/-- Exact principal-pole correction for the source logarithmic derivative.
It is obtained from the already certified regularized/source Perron-integrand
identity at `x = 1`. -/
theorem neg_logDeriv_LFunction_eq_regularized_add_principalCorrection
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hL : DirichletCharacter.LFunction chi s ≠ 0) :
    -logDeriv (DirichletCharacter.LFunction chi) s =
      -logDeriv (regularizedLFunction chi) s +
        if chi = 1 then (s - 1)⁻¹ else 0 := by
  have hper :=
    PrimitiveTruncatedExplicitFormulaBridge.perronContourIntegrand_eq_regularized_add_principal
      chi (x := (1 : ℝ)) hs1 hL
  by_cases hchi : chi = 1
  · simp only [PrimitiveTruncatedExplicitFormulaBridge.perronContourIntegrand,
      PrimitiveTruncatedExplicitFormulaBridge.regularizedPerronContourIntegrand,
      PrimitiveTruncatedExplicitFormulaBridge.principalPoleIntegrand,
      hchi, if_true] at hper ⊢
    field_simp [hs0, hs1] at hper ⊢
    linear_combination hper
  · simp only [PrimitiveTruncatedExplicitFormulaBridge.perronContourIntegrand,
      PrimitiveTruncatedExplicitFormulaBridge.regularizedPerronContourIntegrand,
      PrimitiveTruncatedExplicitFormulaBridge.principalPoleIntegrand,
      hchi, if_false, add_zero] at hper ⊢
    field_simp [hs0] at hper
    exact hper

/-- All-character distance-explicit logarithmic-derivative bound.  For the
principal character the only extra term is the literal distance to its pole
at `s = 1`; no principal loss is hidden in the deflated remainder. -/
theorem norm_logDeriv_LFunction_le_zeroDistance_add_deflated_add_principal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (a H : ℝ) {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hL : DirichletCharacter.LFunction chi s ≠ 0)
    (hdist : ∀ rho ∈ zeroSupport chi a H, d ≤ ‖s - rho‖) :
    ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤
      compactPoleDistanceMajorant chi a H d +
        ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖ +
      (if chi = 1 then ‖(s - 1)⁻¹‖ else 0) := by
  have hreg : regularizedLFunction chi s ≠ 0 := by
    by_cases hchi : chi = 1
    · subst chi
      simp only [regularizedLFunction, if_pos]
      unfold DirichletCharacter.LFunctionTrivChar₁
      rw [Function.update_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) hL
    · simpa [regularizedLFunction, hchi] using hL
  have hregularized :=
    norm_logDeriv_regularizedLFunction_le_zeroDistance_add_deflated
      chi a H hd hreg hdist
  have heq :=
    neg_logDeriv_LFunction_eq_regularized_add_principalCorrection
      chi hs0 hs1 hL
  have hregularizedNeg :
      ‖-logDeriv (regularizedLFunction chi) s‖ ≤
        compactPoleDistanceMajorant chi a H d +
          ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi a H) s‖ := by
    simpa only [norm_neg, compactPoleDistanceMajorant] using hregularized
  have hcorrection :
      ‖if chi = 1 then (s - 1)⁻¹ else 0‖ =
        if chi = 1 then ‖(s - 1)⁻¹‖ else 0 := by
    by_cases hchi : chi = 1 <;> simp [hchi]
  rw [← norm_neg (logDeriv (DirichletCharacter.LFunction chi) s), heq]
  refine (norm_add_le _ _).trans ?_
  rw [hcorrection]
  exact add_le_add_left hregularizedNeg _

end

end ZeroDistanceLogDerivativeBounds
