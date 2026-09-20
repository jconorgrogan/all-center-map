import KoukFunctionalEquationNonreal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The canonical negative-half left edge

At `Re s = -1/2` the endpoint kernel has integrable `1/(1+|t|)` decay.
This module isolates that geometry and turns a uniform logarithmic-derivative
bound on the edge into an explicit bound for the normalized vertical contour.
-/

namespace KoukEndpointLeftVerticalBound

open Set MeasureTheory Complex
open scoped Interval
open KoukTheorem113EndpointKernel KoukTheorem113Residues
open KoukTheorem113ExactFormula KoukEndpointContourBounds

noncomputable section

/-- The elementary even weight used on the canonical left edge has an exact
logarithmic integral. -/
theorem integral_one_div_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (-T)..T, 1 / (1 + |t|)) = 2 * Real.log (T + 1) := by
  have hcont : Continuous fun t : ℝ => 1 / (1 + |t|) := by
    apply Continuous.div continuous_const (continuous_const.add continuous_abs)
    intro t
    change 1 + |t| ≠ 0
    positivity
  have hintNeg : IntervalIntegrable (fun t : ℝ => 1 / (1 + |t|))
      volume (-T) 0 := hcont.intervalIntegrable _ _
  have hintPos : IntervalIntegrable (fun t : ℝ => 1 / (1 + |t|))
      volume 0 T := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hintNeg hintPos]
  have hneg : (∫ t in (-T)..0, 1 / (1 + |t|)) =
      ∫ t in 0..T, 1 / (1 + |t|) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (fun t : ℝ => 1 / (1 + |t|)) (a := 0) (b := T)
    simpa only [neg_zero, abs_neg] using hcomp.symm
  rw [hneg]
  have hpos : (∫ t in 0..T, 1 / (1 + |t|)) = Real.log (T + 1) := by
    have hcongr : (∫ t in 0..T, 1 / (1 + |t|)) =
        ∫ t in 0..T, 1 / (1 + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc 0 T := by
        simpa [Set.uIcc_of_le hT] using ht
      change 1 / (1 + |t|) = 1 / (1 + t)
      rw [abs_of_nonneg htIcc.1]
    rw [hcongr]
    calc
      (∫ t in 0..T, 1 / (1 + t)) =
          ∫ t in (1 + 0)..(1 + T), 1 / t := by
        simpa only using intervalIntegral.integral_comp_add_left
          (fun u : ℝ => 1 / u) 1 (a := 0) (b := T)
      _ = Real.log ((1 + T) / (1 + 0)) :=
        integral_one_div_of_pos (by norm_num) (by linarith)
      _ = Real.log (T + 1) := by ring_nf
  rw [hpos]
  ring

/-- On `Re s = -1/2`, the endpoint kernel decays like
`1/(1+|Im s|)`, uniformly for every `x ≥ 1`. -/
theorem norm_endpointPerronKernel_negativeHalf_le
    {x t : ℝ} (hx : 1 ≤ x) :
    ‖endpointPerronKernel x
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
      6 / (1 + |t|) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let s : ℂ := ((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t
  have hsre : s.re = -(1 / 2 : ℝ) := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp [s] at this
  have hsNormHalf : (1 / 2 : ℝ) ≤ ‖s‖ := by
    have hre := Complex.abs_re_le_norm s
    rw [hsre, abs_neg, abs_of_nonneg (by norm_num)] at hre
    exact hre
  have hsNormPos : 0 < ‖s‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsNormHalf
  have hsNormT : |t| ≤ ‖s‖ := by
    simpa only [hsim] using Complex.abs_im_le_norm s
  have hsum : 1 + |t| ≤ 3 * ‖s‖ := by
    have hone : 1 ≤ 2 * ‖s‖ := by linarith
    linarith
  have hpow : x ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hnum : ‖(x : ℂ) ^ s - 1‖ ≤ 2 := by
    calc
      ‖(x : ℂ) ^ s - 1‖ ≤ ‖(x : ℂ) ^ s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = x ^ (-(1 / 2 : ℝ)) + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp [hsre]
      _ ≤ 2 := by linarith
  have hdenWeight : 0 < 1 + |t| := by positivity
  rw [show (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t) = s by rfl,
    endpointPerronKernel_of_ne hs0, norm_div]
  calc
    ‖(x : ℂ) ^ s - 1‖ / ‖s‖ ≤ 2 / ‖s‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg s)
    _ ≤ 6 / (1 + |t|) := by
      rw [div_le_div_iff₀ hsNormPos hdenWeight]
      nlinarith

/-- Source-integrand form of the canonical left-edge bound. -/
theorem norm_endpointPerronContourIntegrand_negativeHalf_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t M : ℝ} (hx : 1 ≤ x)
    (hlog : ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤ M) :
    ‖endpointPerronContourIntegrand chi x
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
      6 * M / (1 + |t|) := by
  unfold endpointPerronContourIntegrand
  rw [norm_mul, norm_neg]
  have hker := norm_endpointPerronKernel_negativeHalf_le hx (t := t)
  calc
    ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ *
        ‖endpointPerronKernel x
          (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
      M * (6 / (1 + |t|)) :=
        mul_le_mul hlog hker (norm_nonneg _) (le_trans (norm_nonneg _) hlog)
    _ = 6 * M / (1 + |t|) := by ring

/-- A uniform logarithmic-derivative bound on the canonical left edge gives
an explicit logarithmic vertical-contour bound. -/
theorem norm_endpointVerticalLineIntegral_negativeHalf_le_of_logDeriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x T M : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T) (_hM : 0 ≤ M)
    (hL : ∀ t ∈ Set.Icc (-T) T,
      DirichletCharacter.LFunction chi
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc (-T) T,
      t ≠ 0 →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤ M) :
    ‖endpointVerticalLineIntegral chi x (-(1 / 2 : ℝ)) T‖ ≤
      (6 * M / Real.pi) * Real.log (T + 1) := by
  let f : ℝ → ℂ := fun t => endpointDecomposedContourIntegrand chi x
    (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)
  let g : ℝ → ℝ := fun t => 6 * M / (1 + |t|)
  have hgcont : Continuous g := by
    dsimp only [g]
    apply Continuous.div continuous_const (continuous_const.add continuous_abs)
    intro t
    change 1 + |t| ≠ 0
    positivity
  have hgint : IntervalIntegrable g volume (-T) T :=
    hgcont.intervalIntegrable _ _
  have hnorm : ‖∫ t in (-T)..T, f t‖ ≤ ∫ t in (-T)..T, g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hae] with t ht0 ht
      have htIcc : t ∈ Set.Icc (-T) T :=
        ⟨ht.1.le, ht.2⟩
      let s : ℂ := ((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t
      have hs0 : s ≠ 0 := by
        intro hs
        have hre := congrArg Complex.re hs
        simp [s] at hre
      have hs1 : s ≠ 1 := by
        intro hs
        have hre := congrArg Complex.re hs
        simp [s] at hre
        norm_num at hre
      have heq : endpointDecomposedContourIntegrand chi x s =
          endpointPerronContourIntegrand chi x s :=
        (endpointPerronContourIntegrand_eq_regularized_add_principal
          chi hs0 hs1 (hL t htIcc)).symm
      dsimp only [f, g]
      rw [show (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t) = s by rfl,
        heq]
      exact norm_endpointPerronContourIntegrand_negativeHalf_le chi hx
        (hlog t htIcc ht0)
    · exact hgint
  have hnorm' :
      ‖∫ t in (-T)..T,
          endpointDecomposedContourIntegrand chi x
    ((↑ (-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
        ∫ t in (-T)..T, g t := by
    simpa only [f, Complex.ofReal_neg] using hnorm
  unfold endpointVerticalLineIntegral
  rw [norm_mul]
  have hnormConst : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I‖ =
      (2 * Real.pi)⁻¹ := by
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_I]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnormConst]
  have hgExact : (∫ t in (-T)..T, g t) =
      (6 * M) * (2 * Real.log (T + 1)) := by
    dsimp only [g]
    have hfun : (fun t : ℝ => 6 * M / (1 + |t|)) =
        fun t : ℝ => (6 * M) * (1 / (1 + |t|)) := by
      funext t
      ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_one_div_one_add_abs hT]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ t in (-T)..T,
          endpointDecomposedContourIntegrand chi x
            ((↑ (-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
        (2 * Real.pi)⁻¹ * (∫ t in (-T)..T, g t) :=
      mul_le_mul_of_nonneg_left hnorm' (by positivity)
    _ = (6 * M / Real.pi) * Real.log (T + 1) := by
      rw [hgExact]
      field_simp [Real.pi_ne_zero]

end

end KoukEndpointLeftVerticalBound

#print axioms KoukEndpointLeftVerticalBound.integral_one_div_one_add_abs
#print axioms KoukEndpointLeftVerticalBound.norm_endpointPerronKernel_negativeHalf_le
#print axioms KoukEndpointLeftVerticalBound.norm_endpointVerticalLineIntegral_negativeHalf_le_of_logDeriv
