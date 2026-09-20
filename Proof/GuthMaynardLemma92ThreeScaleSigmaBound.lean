import GuthMaynardLemma92EllTailPowerAbsorption

/-!
# Literal three-scale Sigma-II endpoint

This is the source-facing composition of the unequal-scale Lemma 9.2 producer
with the now-certified three-scale first-Poisson cover and its `T^-100` ell
tail.  The three dyadic scales remain independent throughout.
-/

open scoped BigOperators Real FourierTransform

noncomputable section
namespace GuthMaynardJIteration

/-- The literal right-hand side produced by the three-scale `SigmaII`
estimate.  Naming it keeps the subsequent whole-frequency instantiation
readable without hiding any coefficient or scale. -/
def sourceThreeScaleSigmaBound
    (T F delta R Csecond : ℝ) (f : ℝ → ℝ)
    (M2 : ℕ) (mRange : Finset ℤ) (hT : 0 < T) : ℝ :=
  ((2 * Real.rpow T delta *
      (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
      (2 : ℝ) ^ 2 * (M2 : ℝ)) *
      Real.sqrt ((∫ u : ℝ, f u ^ 2) *
        sourceAffineJ
          (sourceAffineConfigs (sourcePositiveDyadicRange M2)
            (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
          (affineSmoothing T
            (fun z => sourceBump (Real.rpow T delta)
              (Real.rpow_pos_of_pos hT delta) z) f)) +
    ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
      |(m2 : ℝ) * (m2' : ℝ)| *
        (((∫ u : ℝ, |f u|) ^ 2 * (2 * Real.rpow T delta)) *
          (Csecond / T ^ 100)) +
    T⁻¹ ^ 100

/-- The complete selected-range `SigmaII` bound for the literal first-Poisson
cover.  Its discarded-ell term has been replaced by the certified
`T^-100` bound, not left as an assumption. -/
theorem sigmaIIFinite_threeScale_selectedPositiveDyadic_le
    {T S F delta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (mRange : Finset ℤ) (hmRange : mRange ⊆ sourcePositiveDyadicRange M2)
    (q j : ℕ) {R Csecond etaTail Ctail kappa : ℝ}
    (hR : R = Real.rpow T kappa)
    (hRone : 1 ≤ R) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hS1 : S ≤ 1)
    (hM2hi : (M2 : ℝ) ≤ T ^ 4)
    (hM2T : (M2 : ℝ) ≤ T)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa)
    (hCsecond : 0 ≤ Csecond) (hCtail : 0 ≤ Ctail)
    (hFourierTail : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Ctail * T ^ etaTail * (T / |z|) ^ j * S)
    (hsecondBudget :
      ((T / (M2 : ℝ)) *
          (R * sourceBumpFourierConstant 1 zero_lt_one (q + 2)) *
          ((1 + (4 * (M2 : ℝ) * F) / ((M2 : ℝ) / T)) ^ 2 *
            max 1 (((M2 : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        Csecond * (T ^ delta) ^ q))
    (hconstant : 2744 * Ctail ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * etaTail ≤
      2 * kappa * (j : ℝ)) :
    sigmaIIFinite
        (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
        mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M2 : ℝ) T (M3 : ℝ) (Real.rpow T delta) ≤
      ((2 * Real.rpow T delta *
          (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M2 : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M2)
                (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
              (affineSmoothing T
                (fun z => sourceBump (Real.rpow T delta)
                  (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) delta) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * Real.rpow T delta)) *
              (Csecond / T ^ 100)) +
        T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < R := by
    rw [hR]
    exact Real.rpow_pos_of_pos hTpos kappa
  have hM3one : (1 : ℝ) ≤ (M3 : ℝ) := by exact_mod_cast hM3
  have hgap : Real.rpow T delta / (M3 : ℝ) <
      R * T / (M2 : ℝ) := by
    have hM2pos : 0 < (M2 : ℝ) := Nat.cast_pos.mpr hM2
    have hM3pos : 0 < (M3 : ℝ) := Nat.cast_pos.mpr hM3
    have hBpos : 0 < Real.rpow T delta :=
      Real.rpow_pos_of_pos hTpos delta
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
    have hleft : Real.rpow T delta / (M3 : ℝ) ≤
        Real.rpow T delta := div_le_self hBpos.le hM3one
    have hBltR : Real.rpow T delta < R := by
      rw [hR]
      nlinarith
    have hright : R ≤ R * T / (M2 : ℝ) := by
      rw [le_div_iff₀ hM2pos]
      exact mul_le_mul_of_nonneg_left hM2T hRpos.le
    calc
      Real.rpow T delta / (M3 : ℝ) ≤ Real.rpow T delta := hleft
      _ < R := hBltR
      _ ≤ R * T / (M2 : ℝ) := hright
  have hraw :=
    sigmaIIFinite_largeEll_selectedPositiveDyadic_variableRadius_unequalScale_le
      hf hM2 mRange
      (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
      hmRange q j hRpos hRone (Nat.cast_pos.mpr hM3)
      hT hF0 hF hM2hi hgap hCsecond hCtail hFourierTail hsecondBudget
  have htail := sourceLemma92ThreeScaleEllTail_le_time_neg100_of_scale_le_time
    hM1 hM2 hM3 j hT hM2T hf.bound_nonneg hS1 hCtail
    hM2hi hB6 hhalf hconstant hexponent
  have htailR : sourceLemma92EllTailCostRadiusUnequal
      (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
      M2 (M3 : ℝ) T S etaTail Ctail delta R j ≤ T⁻¹ ^ 100 := by
    simpa [hR] using htail
  calc
    sigmaIIFinite
        (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
        mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M2 : ℝ) T (M3 : ℝ) (Real.rpow T delta) ≤
      ((2 * Real.rpow T delta *
          (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M2 : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M2)
                (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
              (affineSmoothing T
                (fun z => sourceBump (Real.rpow T delta)
                  (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) delta) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * Real.rpow T delta)) *
              (Csecond / T ^ 100)) +
        sourceLemma92EllTailCostRadiusUnequal
          (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
          M2 (M3 : ℝ) T S etaTail Ctail delta R j := hraw
    _ ≤ ((2 * Real.rpow T delta *
          (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M2 : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M2)
                (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
              (affineSmoothing T
                (fun z => sourceBump (Real.rpow T delta)
                  (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) delta) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * Real.rpow T delta)) *
              (Csecond / T ^ 100)) +
        T⁻¹ ^ 100 := by
      gcongr

/-- Named-RHS form consumed by the whole-frequency source specialization. -/
theorem sigmaIIFinite_threeScale_selectedPositiveDyadic_le_named
    {T S F delta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (mRange : Finset ℤ) (hmRange : mRange ⊆ sourcePositiveDyadicRange M2)
    (q j : ℕ) {R Csecond etaTail Ctail kappa : ℝ}
    (hR : R = Real.rpow T kappa)
    (hRone : 1 ≤ R) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hS1 : S ≤ 1)
    (hM2hi : (M2 : ℝ) ≤ T ^ 4)
    (hM2T : (M2 : ℝ) ≤ T)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa)
    (hCsecond : 0 ≤ Csecond) (hCtail : 0 ≤ Ctail)
    (hFourierTail : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Ctail * T ^ etaTail * (T / |z|) ^ j * S)
    (hsecondBudget :
      ((T / (M2 : ℝ)) *
          (R * sourceBumpFourierConstant 1 zero_lt_one (q + 2)) *
          ((1 + (4 * (M2 : ℝ) * F) / ((M2 : ℝ) / T)) ^ 2 *
            max 1 (((M2 : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        Csecond * (T ^ delta) ^ q))
    (hconstant : 2744 * Ctail ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * etaTail ≤
      2 * kappa * (j : ℝ)) :
    sigmaIIFinite
        (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
        mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M2 : ℝ) T (M3 : ℝ) (Real.rpow T delta) ≤
      sourceThreeScaleSigmaBound T F delta R Csecond f M2 mRange
        (lt_of_lt_of_le zero_lt_one hT) := by
  exact sigmaIIFinite_threeScale_selectedPositiveDyadic_le
    hf hM1 hM2 hM3 mRange hmRange q j hR hRone hT hF0 hF hS1 hM2hi
    hM2T hB6 hhalf hCsecond hCtail hFourierTail hsecondBudget
    hconstant hexponent

#print axioms GuthMaynardJIteration.sigmaIIFinite_threeScale_selectedPositiveDyadic_le
#print axioms GuthMaynardJIteration.sigmaIIFinite_threeScale_selectedPositiveDyadic_le_named

end GuthMaynardJIteration
