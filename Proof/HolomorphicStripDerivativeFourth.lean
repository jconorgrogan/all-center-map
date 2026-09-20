import HolomorphicSubmeanSampling

/-!
# Integrated Cauchy fourth-moment estimate on a vertical strip
-/
namespace HolomorphicStripDerivativeFourth

open Complex MeasureTheory
open scoped BigOperators
noncomputable section

/-- Real/imaginary coordinate form of a translated circle. -/
theorem circleMap_vertical_coordinates (sigma t R theta : ℝ) :
    circleMap ((sigma : ℂ) + t * I) R theta =
      (((sigma + R * Real.cos theta : ℝ) : ℂ) +
        (t + R * Real.sin theta) * I) := by
  apply Complex.ext
  · simp [circleMap, Complex.exp_mul_I]
  · simp [circleMap, Complex.exp_mul_I]

/-- Translation of the inner ordinate integral after writing a circle in
real/imaginary coordinates. -/
theorem circleSlice_integral_translate
    {F : ℂ → ℂ} (sigma R theta A B : ℝ) :
    (∫ t in A..B,
      ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4) =
    ∫ u in A + R * Real.sin theta..B + R * Real.sin theta,
      ‖F (((sigma + R * Real.cos theta : ℝ) : ℂ) + u * I)‖ ^ 4 := by
  simp_rw [circleMap_vertical_coordinates]
  convert intervalIntegral.integral_comp_add_right
    (fun u : ℝ => ‖F (((sigma + R * Real.cos theta : ℝ) : ℂ) + u * I)‖ ^ 4)
    (R * Real.sin theta) using 1 <;> push_cast <;> ring

/-- Integrated Cauchy estimate after swapping the circle parameter and the
vertical ordinate.  This is the exact analytic bridge from a horizontally
uniform fourth moment to a fourth moment of the vertical derivative. -/
theorem verticalDerivFourthIntegral_le_circleSlices
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {sigma A B R : ℝ} (hAB : A ≤ B) (hR : 0 < R) :
    (∫ t in A..B, ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
      R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
        ∫ theta in 0..2 * Real.pi,
          ∫ t in A..B,
            ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4 := by
  let g : ℝ → ℝ → ℝ := fun t theta =>
    ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4
  have hg : Continuous (Function.uncurry g) := by
    have hFc : Continuous F := hF.continuous
    dsimp [g, Function.uncurry, circleMap]
    fun_prop
  have hswap := HolomorphicSubmeanSampling.continuous_intervalIntegral_swap
    hg hAB (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
  have hleftCont : Continuous (fun t : ℝ =>
      ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) := by
    have han : AnalyticOnNhd ℂ F Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
    have hdcont : Continuous (deriv F) := han.deriv.continuous
    fun_prop
  have hcompact : IsCompact (Set.Icc A B ×ˢ Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hprodClosed : IntegrableOn (Function.uncurry g)
      (Set.Icc A B ×ˢ Set.Icc 0 (2 * Real.pi)) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact hcompact hg.continuousOn
  have hprodOpen : IntegrableOn (Function.uncurry g)
      (Set.Ioc A B ×ˢ Set.Ioc 0 (2 * Real.pi)) (volume.prod volume) :=
    hprodClosed.mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hprod : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Ioc A B)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hprodOpen
  have hinnerInt : Integrable
      (fun t => ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta)
      (volume.restrict (Set.Ioc A B)) := hprod.integral_prod_left
  have hrightInt : Integrable
      (fun t => R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
        ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta)
      (volume.restrict (Set.Ioc A B)) :=
    by
      have hh := (hinnerInt.const_mul ((2 * Real.pi)⁻¹)).const_mul (R⁻¹ ^ 4)
      convert hh using 1 <;> simp only [inv_pow] <;> ring
  have hleftInt : Integrable
      (fun t : ℝ => ‖deriv F ((sigma : ℂ) + (t : ℂ) * I)‖ ^ 4)
      (volume.restrict (Set.Ioc A B)) := by
    exact (hleftCont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  have hpoint : ∀ t : ℝ,
      ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4 ≤
        R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
          ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta := by
    intro t
    have hc := HolomorphicSubmeanSampling.norm_deriv_pow_four_le_invRadius_circleAverage
      hF (c := ((sigma : ℂ) + t * I)) hR
    rw [Real.circleAverage_def] at hc
    simp only [smul_eq_mul] at hc
    simpa [g, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity), mul_assoc] using hc
  have hmono :
      (∫ t in Set.Ioc A B,
        ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
      ∫ t in Set.Ioc A B,
        R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
          ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta := by
    exact integral_mono hleftInt hrightInt hpoint
  rw [← intervalIntegral.integral_of_le hAB] at hmono
  have hscalar :
      (∫ t in Set.Ioc A B,
        R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
          ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta) =
      R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
        ∫ t in A..B, ∫ theta in 0..2 * Real.pi, g t theta := by
    simp only [intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
    rw [← MeasureTheory.integral_const_mul]
  rw [hscalar, hswap] at hmono
  simpa [g, mul_assoc] using hmono

/-- Local-disk version of the integrated Cauchy estimate.  This is used for
the principal zeta function, which is holomorphic on the relevant circles but
has a pole elsewhere. -/
theorem verticalDerivFourthIntegral_le_circleSlices_on
    {F : ℂ → ℂ} {sigma A B R : ℝ} (hAB : A ≤ B) (hR : 0 < R)
    (hcircle : Continuous (Function.uncurry (fun t theta : ℝ =>
      ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4)))
    (hderiv : Continuous (fun t : ℝ =>
      ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4))
    (hdisk : ∀ t : ℝ, DifferentiableOn ℂ F
      (Metric.closedBall ((sigma : ℂ) + t * I) R)) :
    (∫ t in A..B, ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
      R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
        ∫ theta in 0..2 * Real.pi,
          ∫ t in A..B,
            ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4 := by
  let g : ℝ → ℝ → ℝ := fun t theta =>
    ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4
  have hg : Continuous (Function.uncurry g) := hcircle
  have hswap := HolomorphicSubmeanSampling.continuous_intervalIntegral_swap
    hg hAB (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
  have hcompact : IsCompact (Set.Icc A B ×ˢ Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hprodClosed : IntegrableOn (Function.uncurry g)
      (Set.Icc A B ×ˢ Set.Icc 0 (2 * Real.pi)) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact hcompact hg.continuousOn
  have hprodOpen : IntegrableOn (Function.uncurry g)
      (Set.Ioc A B ×ˢ Set.Ioc 0 (2 * Real.pi)) (volume.prod volume) :=
    hprodClosed.mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hprod : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Ioc A B)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hprodOpen
  have hinnerInt : Integrable
      (fun t => ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta)
      (volume.restrict (Set.Ioc A B)) := hprod.integral_prod_left
  have hrightInt : Integrable
      (fun t => R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
        ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta)
      (volume.restrict (Set.Ioc A B)) := by
    have hh := (hinnerInt.const_mul ((2 * Real.pi)⁻¹)).const_mul (R⁻¹ ^ 4)
    convert hh using 1 <;> simp only [inv_pow] <;> ring
  have hleftInt : Integrable
      (fun t : ℝ => ‖deriv F ((sigma : ℂ) + (t : ℂ) * I)‖ ^ 4)
      (volume.restrict (Set.Ioc A B)) :=
    hderiv.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ t : ℝ,
      ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4 ≤
        R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
          ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta := by
    intro t
    have hc :=
      HolomorphicSubmeanSampling.norm_deriv_pow_four_le_invRadius_circleAverage_on
        hR (hdisk t)
    rw [Real.circleAverage_def] at hc
    simp only [smul_eq_mul] at hc
    simpa [g, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity), mul_assoc] using hc
  have hmono := integral_mono hleftInt hrightInt hpoint
  rw [← intervalIntegral.integral_of_le hAB] at hmono
  have hscalar :
      (∫ t in Set.Ioc A B,
        R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
          ∫ theta in Set.Ioc 0 (2 * Real.pi), g t theta) =
      R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
        ∫ t in A..B, ∫ theta in 0..2 * Real.pi, g t theta := by
    simp only [intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
    rw [← MeasureTheory.integral_const_mul]
  rw [hscalar, hswap] at hmono
  simpa [g, mul_assoc] using hmono

/-- A horizontally uniform fourth-moment bound on the radius-`R` collar
implies the corresponding one-separated discrete fourth moment.  The only
loss is the explicit Cauchy factor `R⁻⁴`. -/
theorem sum_verticalTrace_fourth_le_of_circleSlices
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {sigma A B R M : ℝ} {W : Finset ℝ}
    (hAB : A ≤ B) (hR : 0 < R) (hM : 0 ≤ M)
    (hsep : CGLProofDAG.OneSeparated W)
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B)
    (hcentral :
      (∫ t in A..B + 1,
        ‖F ((sigma : ℂ) + t * I)‖ ^ 4) ≤ M)
    (hslices : ∀ theta : ℝ,
      (∫ u in A + R * Real.sin theta..B + 1 + R * Real.sin theta,
        ‖F (((sigma + R * Real.cos theta : ℝ) : ℂ) + u * I)‖ ^ 4) ≤ M) :
    (∑ t ∈ W, ‖F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
      (4 + 2 * R⁻¹ ^ 4) * M := by
  have hsample :=
    HolomorphicSubmeanSampling.sum_verticalTrace_fourth_le_continuous_and_deriv
      hF (sigma := sigma) hAB hsep hheight
  have hderiv := verticalDerivFourthIntegral_le_circleSlices hF
    (A := A) (B := B + 1) (sigma := sigma) (by linarith) hR
  have htheta :
      (∫ theta in 0..2 * Real.pi,
        ∫ t in A..B + 1,
          ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4) ≤
        (2 * Real.pi) * M := by
    let g : ℝ → ℝ → ℝ := fun t theta =>
      ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4
    have hg : Continuous (Function.uncurry g) := by
      have hFc : Continuous F := hF.continuous
      dsimp [g, Function.uncurry, circleMap]
      fun_prop
    have hcompact : IsCompact
        (Set.Icc A (B + 1) ×ˢ Set.Icc 0 (2 * Real.pi)) :=
      isCompact_Icc.prod isCompact_Icc
    have hprodClosed : IntegrableOn (Function.uncurry g)
        (Set.Icc A (B + 1) ×ˢ Set.Icc 0 (2 * Real.pi))
        (volume.prod volume) :=
      ContinuousOn.integrableOn_compact hcompact hg.continuousOn
    have hprodOpen : IntegrableOn (Function.uncurry g)
        (Set.Ioc A (B + 1) ×ˢ Set.Ioc 0 (2 * Real.pi))
        (volume.prod volume) :=
      hprodClosed.mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    have hprod : Integrable (Function.uncurry g)
        ((volume.restrict (Set.Ioc A (B + 1))).prod
          (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
      rw [Measure.prod_restrict]
      exact hprodOpen
    have hinnerInt : Integrable
        (fun theta => ∫ t in Set.Ioc A (B + 1), g t theta)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      hprod.integral_prod_right
    have hinnerInterval : IntervalIntegrable
        (fun theta => ∫ t in A..B + 1,
          ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4)
        volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff,
        Set.uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
      simpa [g, intervalIntegral.integral_of_le (by linarith : A ≤ B + 1)]
        using hinnerInt
    have hconst : Continuous (fun _theta : ℝ => M) := continuous_const
    calc
      (∫ theta in 0..2 * Real.pi,
          ∫ t in A..B + 1,
            ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4) ≤
          ∫ _theta in 0..2 * Real.pi, M := by
            exact intervalIntegral.integral_mono_on
              (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
              hinnerInterval (hconst.intervalIntegrable _ _)
              (fun theta _ => by
                rw [circleSlice_integral_translate]
                exact hslices theta)
      _ = (2 * Real.pi) * M := by
        rw [intervalIntegral.integral_const]
        simp
  have hderiv' :
      (∫ t in A..B + 1,
        ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) ≤ R⁻¹ ^ 4 * M := by
    calc
      (∫ t in A..B + 1,
          ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
          R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
            ∫ theta in 0..2 * Real.pi,
              ∫ t in A..B + 1,
                ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4 := hderiv
      _ ≤ R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ * ((2 * Real.pi) * M) := by
        exact mul_le_mul_of_nonneg_left htheta (by positivity)
      _ = R⁻¹ ^ 4 * M := by field_simp [Real.pi_ne_zero]
  calc
    (∑ t ∈ W, ‖F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
        4 * (∫ t in A..B + 1,
          ‖F ((sigma : ℂ) + t * I)‖ ^ 4) +
        2 * ∫ t in A..B + 1,
          ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4 := hsample
    _ ≤ 4 * M + 2 * (R⁻¹ ^ 4 * M) := by gcongr
    _ = (4 + 2 * R⁻¹ ^ 4) * M := by ring

/-- Local-holomorphy sampling theorem, allowing a meromorphic function whose
pole lies outside every disk used in the argument. -/
theorem sum_verticalTrace_fourth_le_of_circleSlices_on
    {F : ℂ → ℂ} {sigma A B R M : ℝ} {W : Finset ℝ}
    (hAB : A ≤ B) (hR : 0 < R)
    (htrace : ∀ t : ℝ, HasDerivAt (fun u : ℝ =>
      F ((sigma : ℂ) + u * I))
      (deriv F ((sigma : ℂ) + t * I) * I) t)
    (htraceDeriv : Continuous (fun t : ℝ =>
      deriv F ((sigma : ℂ) + t * I) * I))
    (hcircle : Continuous (Function.uncurry (fun t theta : ℝ =>
      ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4)))
    (hdisk : ∀ t : ℝ, DifferentiableOn ℂ F
      (Metric.closedBall ((sigma : ℂ) + t * I) R))
    (hsep : CGLProofDAG.OneSeparated W)
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B)
    (hcentral : (∫ t in A..B + 1,
      ‖F ((sigma : ℂ) + t * I)‖ ^ 4) ≤ M)
    (hslices : ∀ theta : ℝ,
      (∫ u in A + R * Real.sin theta..B + 1 + R * Real.sin theta,
        ‖F (((sigma + R * Real.cos theta : ℝ) : ℂ) + u * I)‖ ^ 4) ≤ M) :
    (∑ t ∈ W, ‖F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
      (4 + 2 * R⁻¹ ^ 4) * M := by
  have hsample :=
    HolomorphicSubmeanSampling.sum_norm_fourth_le_interval_collar_fourth_deriv
      hAB htrace htraceDeriv hsep hheight
  have hderiv := verticalDerivFourthIntegral_le_circleSlices_on
    (F := F) (sigma := sigma) (A := A) (B := B + 1) (R := R)
    (by linarith) hR hcircle
    (by simpa only [norm_mul, Complex.norm_I, mul_one] using htraceDeriv.norm.pow 4)
    hdisk
  have htheta :
      (∫ theta in 0..2 * Real.pi,
        ∫ t in A..B + 1,
          ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4) ≤
        (2 * Real.pi) * M := by
    let g : ℝ → ℝ → ℝ := fun t theta =>
      ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4
    have hcompact : IsCompact
        (Set.Icc A (B + 1) ×ˢ Set.Icc 0 (2 * Real.pi)) :=
      isCompact_Icc.prod isCompact_Icc
    have hprodClosed : IntegrableOn (Function.uncurry g)
        (Set.Icc A (B + 1) ×ˢ Set.Icc 0 (2 * Real.pi))
        (volume.prod volume) :=
      ContinuousOn.integrableOn_compact hcompact hcircle.continuousOn
    have hprodOpen : IntegrableOn (Function.uncurry g)
        (Set.Ioc A (B + 1) ×ˢ Set.Ioc 0 (2 * Real.pi))
        (volume.prod volume) :=
      hprodClosed.mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    have hprod : Integrable (Function.uncurry g)
        ((volume.restrict (Set.Ioc A (B + 1))).prod
          (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
      rw [Measure.prod_restrict]
      exact hprodOpen
    have hinnerInt : Integrable
        (fun theta => ∫ t in Set.Ioc A (B + 1), g t theta)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      hprod.integral_prod_right
    have hinnerInterval : IntervalIntegrable
        (fun theta => ∫ t in A..B + 1,
          ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4)
        volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff,
        Set.uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
      simpa [g, intervalIntegral.integral_of_le (by linarith : A ≤ B + 1)]
        using hinnerInt
    calc
      _ ≤ ∫ _theta in 0..2 * Real.pi, M := by
        exact intervalIntegral.integral_mono_on
          (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
          hinnerInterval (continuous_const.intervalIntegrable _ _)
          (fun theta _ => by
            rw [circleSlice_integral_translate]
            exact hslices theta)
      _ = (2 * Real.pi) * M := by
        rw [intervalIntegral.integral_const]
        simp
  have hderiv' : (∫ t in A..B + 1,
      ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4) ≤ R⁻¹ ^ 4 * M := by
    calc
      _ ≤ R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ *
          ∫ theta in 0..2 * Real.pi,
            ∫ t in A..B + 1,
              ‖F (circleMap ((sigma : ℂ) + t * I) R theta)‖ ^ 4 := hderiv
      _ ≤ R⁻¹ ^ 4 * (2 * Real.pi)⁻¹ * ((2 * Real.pi) * M) := by
        exact mul_le_mul_of_nonneg_left htheta (by positivity)
      _ = R⁻¹ ^ 4 * M := by field_simp [Real.pi_ne_zero]
  have hsample' :
      (∑ t ∈ W, ‖F ((sigma : ℂ) + t * I)‖ ^ 4) ≤
        4 * (∫ t in A..B + 1,
          ‖F ((sigma : ℂ) + t * I)‖ ^ 4) +
        2 * ∫ t in A..B + 1,
          ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4 := by
    simpa only [norm_mul, Complex.norm_I, mul_one] using hsample
  calc
    _ ≤ 4 * (∫ t in A..B + 1,
        ‖F ((sigma : ℂ) + t * I)‖ ^ 4) +
      2 * ∫ t in A..B + 1,
        ‖deriv F ((sigma : ℂ) + t * I)‖ ^ 4 := hsample'
    _ ≤ 4 * M + 2 * (R⁻¹ ^ 4 * M) := by gcongr
    _ = (4 + 2 * R⁻¹ ^ 4) * M := by ring

end
end HolomorphicStripDerivativeFourth

#print axioms HolomorphicStripDerivativeFourth.circleMap_vertical_coordinates
#print axioms HolomorphicStripDerivativeFourth.circleSlice_integral_translate
#print axioms HolomorphicStripDerivativeFourth.verticalDerivFourthIntegral_le_circleSlices
#print axioms HolomorphicStripDerivativeFourth.verticalDerivFourthIntegral_le_circleSlices_on
#print axioms HolomorphicStripDerivativeFourth.sum_verticalTrace_fourth_le_of_circleSlices
#print axioms HolomorphicStripDerivativeFourth.sum_verticalTrace_fourth_le_of_circleSlices_on
