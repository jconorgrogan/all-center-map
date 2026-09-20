import KoukEndpointContourBounds

/-!
# Almost-everywhere horizontal endpoint contour bound

Koukoulopoulos' full-support contour crosses `Re s = 0`.  The two certified
pointwise logarithmic-derivative bounds naturally cover the open positive and
negative halves; the single seam point has zero Lebesgue measure.  This is the
source-faithful integral interface, avoiding an artificial pointwise premise at
the seam.
-/

namespace KoukEndpointHorizontalAEBound

open Complex Set MeasureTheory
open KoukTheorem113ExactFormula KoukTheorem113Residues
open KoukEndpointContourBounds

noncomputable section

/-- Horizontal endpoint contour estimate from an a.e. source log-derivative
bound.  This is the exact a.e. companion of
`norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv`. -/
theorem norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv_ae
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T M : ℝ} (hx : 1 ≤ x) (hc0 : 0 ≤ c)
    (hsigma : sigma ≤ c) (hT : 0 < T) (hM : 0 ≤ M)
    (hLtop : ∀ᵐ r : ℝ, r ∈ Set.uIoc sigma c →
      DirichletCharacter.LFunction chi
        ((r : ℂ) + Complex.I * T) ≠ 0)
    (hLbottom : ∀ᵐ r : ℝ, r ∈ Set.uIoc sigma c →
      DirichletCharacter.LFunction chi
        ((r : ℂ) - Complex.I * T) ≠ 0)
    (htop : ∀ᵐ r : ℝ, r ∈ Set.uIoc sigma c →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ᵐ r : ℝ, r ∈ Set.uIoc sigma c →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖endpointHorizontalBoundaryIntegral chi x sigma c T‖ ≤
      2 * (c - sigma) / Real.pi * (M * x ^ c / T) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have habsT : |T| = T := abs_of_pos hT
  have habsNegT : |-T| = T := by simp [abs_of_pos hT]
  have htopPoint : ∀ᵐ r : ℝ, r ∈ Set.uIoc sigma c →
      ‖endpointDecomposedContourIntegrand chi x
        ((r : ℂ) + (T : ℂ) * Complex.I)‖ ≤ 2 * M * x ^ c / T := by
    filter_upwards [hLtop, htop] with r hL hlog hr
    have hr' : r ∈ Set.Icc sigma c := by
      have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
      simpa [Set.uIcc_of_le hsigma] using hru
    rw [show (T : ℂ) * Complex.I = Complex.I * (T : ℂ) by ring]
    rw [endpointDecomposed_eq_source_horizontal chi hT.ne' (hL hr)]
    simpa only [habsT] using
      norm_endpointPerronContourIntegrand_horizontal_le chi hx hc0 hr'.2
        (by simpa [habsT] using hT) (hlog hr)
  have hbottomPoint : ∀ᵐ r : ℝ, r ∈ Set.uIoc sigma c →
      ‖endpointDecomposedContourIntegrand chi x
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤
          2 * M * x ^ c / T := by
    filter_upwards [hLbottom, hbottom] with r hL hlog hr
    have hr' : r ∈ Set.Icc sigma c := by
      have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
      simpa [Set.uIcc_of_le hsigma] using hru
    rw [show ((-T : ℝ) : ℂ) * Complex.I =
      Complex.I * ((-T : ℝ) : ℂ) by ring]
    rw [endpointDecomposed_eq_source_horizontal chi
      (neg_ne_zero.mpr hT.ne') (by simpa [sub_eq_add_neg] using hL hr)]
    have hp := norm_endpointPerronContourIntegrand_horizontal_le chi hx hc0
      hr'.2 (tau := -T) (M := M)
      (by simpa [habsNegT] using hT)
      (by simpa [sub_eq_add_neg, mul_comm] using hlog hr)
    simpa only [habsNegT] using hp
  have htopint :
      ‖∫ r in sigma..c,
          endpointDecomposedContourIntegrand chi x
            ((r : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        (2 * M * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae htopPoint
  have hbottomint :
      ‖∫ r in sigma..c,
          endpointDecomposedContourIntegrand chi x
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤
        (2 * M * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hbottomPoint
  let A : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹
  let Ibottom : ℂ := ∫ r in sigma..c,
    endpointDecomposedContourIntegrand chi x
      ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  let Itop : ℂ := ∫ r in sigma..c,
    endpointDecomposedContourIntegrand chi x
      ((r : ℂ) + (T : ℂ) * Complex.I)
  have hA : ‖A‖ = (2 * Real.pi)⁻¹ := by
    dsimp [A]
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one]
    congr 1
    rw [norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  change ‖A * (Ibottom - Itop)‖ ≤ _
  rw [norm_mul, hA]
  have hdiff : ‖Ibottom - Itop‖ ≤
      2 * ((2 * M * x ^ c / T) * |c - sigma|) := by
    calc
      ‖Ibottom - Itop‖ ≤ ‖Ibottom‖ + ‖Itop‖ := norm_sub_le _ _
      _ ≤ (2 * M * x ^ c / T) * |c - sigma| +
          (2 * M * x ^ c / T) * |c - sigma| :=
        add_le_add (by simpa [Ibottom] using hbottomint)
          (by simpa [Itop] using htopint)
      _ = 2 * ((2 * M * x ^ c / T) * |c - sigma|) := by ring
  calc
    (2 * Real.pi)⁻¹ * ‖Ibottom - Itop‖ ≤
        (2 * Real.pi)⁻¹ *
          (2 * ((2 * M * x ^ c / T) * |c - sigma|)) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = 2 * (c - sigma) / Real.pi * (M * x ^ c / T) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsigma)]
      field_simp [ne_of_gt hpi]

end

end KoukEndpointHorizontalAEBound

#print axioms KoukEndpointHorizontalAEBound.norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv_ae
