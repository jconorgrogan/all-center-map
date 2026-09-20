import KoukTheorem113NegativeRectangle

/-!
# Exact endpoint-contour decomposition for Koukoulopoulos Theorem 11.3

This file is deliberately estimate-free.  It replaces the ordinary Perron
kernel on the right edge by the endpoint-regularized kernel, records the
resulting correction as a literal integral, and solves the rectangle identity
for the right edge.  The output is the exact algebraic skeleton of (11.5),
before the far-left, horizontal, Perron, and trivial-zero estimates.
-/

namespace KoukTheorem113ExactFormula

open Set MeasureTheory Complex
open scoped Interval BigOperators
open PrimitiveExplicitFormulaSpine PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron FinitePoleRectangle DirichletZeros
open KoukTheorem113EndpointKernel KoukTheorem113Residues
open KoukTheorem113NegativeRectangle

noncomputable section

/-- Normalized upward endpoint-kernel integral on a vertical line. -/
def endpointVerticalLineIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x a T : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I *
    ∫ t in (-T)..T,
      endpointDecomposedContourIntegrand chi x
        ((a : ℂ) + Complex.I * t)

/-- Normalized positively oriented endpoint-kernel horizontal pair. -/
def endpointHorizontalBoundaryIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x sigma c T : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ((∫ u in sigma..c,
        endpointDecomposedContourIntegrand chi x
          ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ u in sigma..c,
        endpointDecomposedContourIntegrand chi x
          ((u : ℂ) + (T : ℂ) * Complex.I)))

/-- Literal correction incurred by replacing `x^s/s` with `(x^s-1)/s`
on the Perron line. -/
def endpointRightReplacementCorrection {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (c T : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I *
    ∫ t in (-T)..T,
      (-logDeriv (DirichletCharacter.LFunction chi)
        ((c : ℂ) + Complex.I * t)) /
          ((c : ℂ) + Complex.I * t)

private theorem contourNormalization_mul_I :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp [hpi, hI]
  push_cast
  ring

private theorem endpointDecomposed_eq_source_on_rightLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x c t : ℝ} (hc : 1 < c) :
    endpointDecomposedContourIntegrand chi x
        ((c : ℂ) + Complex.I * t) =
      endpointPerronContourIntegrand chi x
        ((c : ℂ) + Complex.I * t) := by
  let s : ℂ := (c : ℂ) + Complex.I * t
  have hsre : 1 < s.re := by
    dsimp only [s]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    exact hc
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hsre
    norm_num at hsre
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsre
    norm_num at hsre
  have hL : DirichletCharacter.LFunction chi s ≠ 0 :=
    LFunction_ne_zero_of_one_lt_re chi hsre
  have h :=
    KoukTheorem113Residues.endpointPerronContourIntegrand_eq_regularized_add_principal
      (x := x) chi hs0 hs1 hL
  simpa only [s, endpointDecomposedContourIntegrand] using h.symm

/-- On the absolute-convergence line the original and endpoint integrands
differ by exactly `-(L'/L)(s)/s`. -/
theorem perronContourIntegrand_eq_endpointDecomposed_add_correction
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x c t : ℝ} (hc : 1 < c) :
    perronContourIntegrand chi x ((c : ℂ) + Complex.I * t) =
      endpointDecomposedContourIntegrand chi x
          ((c : ℂ) + Complex.I * t) +
        (-logDeriv (DirichletCharacter.LFunction chi)
          ((c : ℂ) + Complex.I * t)) /
            ((c : ℂ) + Complex.I * t) := by
  let s : ℂ := (c : ℂ) + Complex.I * t
  have hsre : 1 < s.re := by
    dsimp only [s]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    exact hc
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hsre
    norm_num at hsre
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsre
    norm_num at hsre
  have hL : DirichletCharacter.LFunction chi s ≠ 0 :=
    LFunction_ne_zero_of_one_lt_re chi hsre
  have hendpoint :=
    KoukTheorem113Residues.endpointPerronContourIntegrand_eq_regularized_add_principal
      (x := x) chi hs0 hs1 hL
  have hker := endpointPerronKernel_of_ne (x := x) hs0
  change perronContourIntegrand chi x s =
    endpointDecomposedContourIntegrand chi x s +
      (-logDeriv (DirichletCharacter.LFunction chi) s) / s
  unfold endpointDecomposedContourIntegrand
  rw [← hendpoint]
  unfold perronContourIntegrand endpointPerronContourIntegrand
  rw [hker]
  field_simp [hs0]
  ring

/-- Exact right-line kernel replacement, with no asymptotic estimate. -/
theorem rightLineIntegral_eq_endpointVertical_add_replacement
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) :
    rightLineIntegral chi x c T =
      endpointVerticalLineIntegral chi x c T +
        endpointRightReplacementCorrection chi c T := by
  rw [rightLineIntegral_eq_contourIntegrand chi hx c T]
  unfold endpointVerticalLineIntegral endpointRightReplacementCorrection
  rw [contourNormalization_mul_I]
  rw [← mul_add]
  congr 1
  have hendpointContinuous : Continuous
      (fun t : ℝ => endpointDecomposedContourIntegrand chi x
        ((c : ℂ) + Complex.I * t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    let s : ℂ := (c : ℂ) + Complex.I * t
    have hsre : 1 < s.re := by
      dsimp only [s]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      exact hc
    have hs0 : s ≠ 0 := by
      intro hs
      rw [hs] at hsre
      norm_num at hsre
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at hsre
      norm_num at hsre
    have hL : DirichletCharacter.LFunction chi s ≠ 0 :=
      LFunction_ne_zero_of_one_lt_re chi hsre
    have hsource :=
      differentiableAt_endpointPerronContourIntegrand_of_L_ne_zero
        chi hx (Or.inl hs1) hL
    have hinner : ContinuousAt
        (fun u : ℝ => (c : ℂ) + Complex.I * u) t := by fun_prop
    rw [show (fun u : ℝ => endpointDecomposedContourIntegrand chi x
        ((c : ℂ) + Complex.I * u)) =
          fun u : ℝ => endpointPerronContourIntegrand chi x
            ((c : ℂ) + Complex.I * u) by
      funext u
      exact endpointDecomposed_eq_source_on_rightLine
        (x := x) chi (t := u) hc]
    exact ContinuousAt.comp_of_eq (f := fun u : ℝ =>
      (c : ℂ) + Complex.I * u) (g := endpointPerronContourIntegrand chi x)
        hsource.continuousAt hinner rfl
  have hcorrectionContinuous : Continuous
      (fun t : ℝ =>
        (-logDeriv (DirichletCharacter.LFunction chi)
          ((c : ℂ) + Complex.I * t)) /
            ((c : ℂ) + Complex.I * t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    let s : ℂ := (c : ℂ) + Complex.I * t
    have hsre : 1 < s.re := by
      dsimp only [s]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      exact hc
    have hs0 : s ≠ 0 := by
      intro hs
      rw [hs] at hsre
      norm_num at hsre
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at hsre
      norm_num at hsre
    have hL : DirichletCharacter.LFunction chi s ≠ 0 :=
      LFunction_ne_zero_of_one_lt_re chi hsre
    have hLa : AnalyticAt ℂ (DirichletCharacter.LFunction chi) s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [eventually_ne_nhds hs1] with z hz
      exact DirichletCharacter.differentiableAt_LFunction chi z (.inl hz)
    have hlog : DifferentiableAt ℂ
        (logDeriv (DirichletCharacter.LFunction chi)) s := by
      simpa only [logDeriv, Pi.div_apply] using
        (hLa.deriv.div hLa hL).differentiableAt
    have hquot : DifferentiableAt ℂ
        (fun z => (-logDeriv (DirichletCharacter.LFunction chi) z) / z) s :=
      hlog.neg.div differentiableAt_id hs0
    have hinner : ContinuousAt
        (fun u : ℝ => (c : ℂ) + Complex.I * u) t := by fun_prop
    exact ContinuousAt.comp_of_eq (f := fun u : ℝ =>
        (c : ℂ) + Complex.I * u)
        (g := fun z : ℂ =>
          (-logDeriv (DirichletCharacter.LFunction chi) z) / z)
        hquot.continuousAt hinner rfl
  have hendpointInt : IntervalIntegrable
      (fun t : ℝ => endpointDecomposedContourIntegrand chi x
        ((c : ℂ) + Complex.I * t)) volume (-T) T :=
    hendpointContinuous.intervalIntegrable (-T) T
  have hcorrectionInt : IntervalIntegrable
      (fun t : ℝ =>
        (-logDeriv (DirichletCharacter.LFunction chi)
          ((c : ℂ) + Complex.I * t)) /
            ((c : ℂ) + Complex.I * t)) volume (-T) T :=
    hcorrectionContinuous.intervalIntegrable (-T) T
  rw [← intervalIntegral.integral_add hendpointInt hcorrectionInt]
  apply intervalIntegral.integral_congr
  intro t _ht
  exact perronContourIntegrand_eq_endpointDecomposed_add_correction
    (x := x) chi (t := t) hc

/-- The geometric rectangle convention is exactly right minus left plus the
positively oriented horizontal pair. -/
theorem normalizedEndpointRectangleBoundary_eq_vertical_sub_add_horizontal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x sigma c T : ℝ) :
    normalizedEndpointRectangleBoundary chi x sigma c T =
      endpointVerticalLineIntegral chi x c T -
        endpointVerticalLineIntegral chi x sigma T +
        endpointHorizontalBoundaryIntegral chi x sigma c T := by
  unfold normalizedEndpointRectangleBoundary rectangleBoundaryIntegral
    endpointVerticalLineIntegral endpointHorizontalBoundaryIntegral
  simp only [mul_comm (Complex.I : ℂ)]
  ring

/-- Solve the exact endpoint rectangle identity for its right edge. -/
theorem endpointVerticalLineIntegral_eq_main_sub_zero_add_left_sub_horizontal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T : ℝ} (hx : 0 < x) (hsigma1 : sigma < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    endpointVerticalLineIntegral chi x c T =
      (if chi = 1 then endpointPerronKernel x 1 else 0) -
        ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℂ) *
            endpointPerronKernel x rho +
        endpointVerticalLineIntegral chi x sigma T -
        endpointHorizontalBoundaryIntegral chi x sigma c T := by
  have hres := normalizedEndpointRectangleBoundary_eq_main_sub_zeroSum
    chi hx hsigma1 hc hT hleftNonzero hbottomNonzero htopNonzero
  rw [normalizedEndpointRectangleBoundary_eq_vertical_sub_add_horizontal] at hres
  linear_combination hres

/-- Primitive prefix identity on an arbitrary negative-left legal rectangle.
All unestimated pieces are retained literally. -/
theorem twistedMangoldtPrefix_eq_endpoint_negativeRectangle
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (N : ℕ) {sigma c T : ℝ} (hsigma1 : sigma < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    APFoundation.twistedMangoldtSum chi (Finset.Icc 1 N) =
      (if chi = 1 then endpointPerronKernel (halfIntegerPoint N) 1 else 0) -
        ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℂ) *
            endpointPerronKernel (halfIntegerPoint N) rho +
        endpointVerticalLineIntegral chi (halfIntegerPoint N) sigma T -
        endpointHorizontalBoundaryIntegral chi
          (halfIntegerPoint N) sigma c T +
        endpointRightReplacementCorrection chi c T +
        insideKernelError chi N c T -
        coefficientTail chi (halfIntegerPoint N) c T (Finset.Icc 1 N) := by
  rw [twistedMangoldtPrefix_eq_rightLine_add_errors chi N hc]
  rw [rightLineIntegral_eq_endpointVertical_add_replacement
    chi (halfIntegerPoint_pos N) hc]
  rw [endpointVerticalLineIntegral_eq_main_sub_zero_add_left_sub_horizontal
    chi (halfIntegerPoint_pos N) hsigma1 hc hT hleftNonzero
      hbottomNonzero htopNonzero]

end
end KoukTheorem113ExactFormula

#print axioms KoukTheorem113ExactFormula.perronContourIntegrand_eq_endpointDecomposed_add_correction
#print axioms KoukTheorem113ExactFormula.normalizedEndpointRectangleBoundary_eq_vertical_sub_add_horizontal
#print axioms KoukTheorem113ExactFormula.twistedMangoldtPrefix_eq_endpoint_negativeRectangle
