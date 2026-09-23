import GuthMaynardLemma92UnequalScaleWeld
import GuthMaynardS3NormalizedBump
import GuthMaynardLemma92SecondPoissonAbsorption

set_option maxHeartbeats 3000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3UnequalScaleSecondPoisson

open GuthMaynardJIteration

/-! The expanding detector radius costs `eta` powers in the Fourier
constant.  The raw canonical consumer costs a further `107` powers, so the
displayed budget is uniform once `eta + 107 ≤ delta*q`.  The coefficient
`25*c*sourceLemma92Decay q*integerQuadraticMass` is fixed before `T`. -/
theorem sourceLemma92_secondPoissonBudget_scaled_uniform
    {T F c eta delta : ℝ} {M q : ℕ}
    (hT : 1 ≤ T) (hM : 0 < M) (hMhi : (M : ℝ) ≤ T ^ 4)
    (hF0 : 0 ≤ F) (hF : F ≤ T) (hc : 0 ≤ c)
    (hreserve : eta + 107 ≤ delta * (q : ℝ)) :
    (T / (M : ℝ)) *
        ((c * Real.rpow T eta) * sourceLemma92Decay q) *
        ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
          max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
      (25 * c * sourceLemma92Decay q * integerQuadraticMass) *
        (Real.rpow T delta) ^ q := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTpow : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hTpos.le _
  have hRnonneg : 0 ≤ c * Real.rpow T eta :=
    mul_nonneg hc hTpow
  have hnum := sourceLemma92SecondPoissonNumerator_le
    hT hM hMhi hF0 hF
    (mul_nonneg hRnonneg (sourceLemma92Decay_nonneg q))
  have hexp : Real.rpow T (eta + 107) ≤
      Real.rpow T (delta * (q : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le hT hreserve
  have hpow : Real.rpow T (eta + 107) ≤
      (Real.rpow T delta) ^ q := by
    calc
      Real.rpow T (eta + 107) ≤ Real.rpow T (delta * (q : ℝ)) := hexp
      _ = (Real.rpow T delta) ^ q := by
        have hmul := Real.rpow_mul (le_trans zero_le_one hT) delta (q : ℝ)
        norm_num [Real.rpow_natCast] at hmul ⊢
        exact hmul
  have hcoef : 0 ≤ 25 * c * sourceLemma92Decay q *
      integerQuadraticMass :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc)
      (sourceLemma92Decay_nonneg q)) integerQuadraticMass_nonneg
  calc
    _ ≤ (25 * ((c * Real.rpow T eta) * sourceLemma92Decay q) *
        integerQuadraticMass) * T ^ 107 := hnum
    _ = (25 * c * sourceLemma92Decay q * integerQuadraticMass) *
        Real.rpow T (eta + 107) := by
      calc
        _ = (25 * c * sourceLemma92Decay q * integerQuadraticMass) *
            (Real.rpow T eta * T ^ 107) := by ring
        _ = _ := by
          have hadd : Real.rpow T eta * T ^ 107 =
              Real.rpow T (eta + (107 : ℝ)) := by
            simpa only [Nat.cast_ofNat] using!
              (Real.rpow_add_natCast hTpos.ne' eta 107).symm
          rw [hadd]
    _ ≤ (25 * c * sourceLemma92Decay q * integerQuadraticMass) *
        (Real.rpow T delta) ^ q :=
      mul_le_mul_of_nonneg_left hpow hcoef

/-! Unequal-scale consumer with the actual expanding detector bump.  The
canonical theorem is run with the raw bump first: its support and Fourier
package are literal, and its smoothing orbit uses the raw bump.  The final
step rewrites the common affine collar to the normalized bump and keeps the
exact `(4*B)^2` factor. -/
theorem sigmaIIFinite_selectedPositiveDyadic_scaledRadius_unequalScale_normalizedJcoll_le
    {T S F c eta delta M3 Ctau R B : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (q : ℕ) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4) (hCtau : 0 ≤ Ctau)
    (hc : 0 ≤ c) (heta : 0 ≤ eta)
    (hRscale : R = c * Real.rpow T eta)
    (hRpos : 0 < R) (hRone : 1 ≤ R)
    (hBscale : B = Real.rpow T delta) (hBpos : 0 < B)
    (hM3lo : (M : ℝ) ≤ M3) (hM3hi : M3 ≤ 16 * (M : ℝ))
    (hreserve : eta + 107 ≤ delta * (q : ℝ)) :
    sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hRpos x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 Ctau ≤
        ((2 * Ctau *
            (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            ((4 * B) ^ 2 *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F (2 * B)))
                (affineSmoothing T
                  (sourceBumpNormalized B
                    hBpos) f))) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau)) *
              ((25 * c * sourceLemma92Decay q * integerQuadraticMass) /
                T ^ 100)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hM3pos : 0 < M3 := lt_of_lt_of_le hMreal hM3lo
  have hCtail : 0 ≤ 25 * c * sourceLemma92Decay q * integerQuadraticMass :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc)
      (sourceLemma92Decay_nonneg q)) integerQuadraticMass_nonneg
  have hbudget :
      ((T / (M : ℝ)) *
          (R *
            sourceBumpFourierConstant 1 zero_lt_one (q + 2)) *
          ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
            max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        (25 * c * sourceLemma92Decay q * integerQuadraticMass) *
          B ^ q) := by
    rw [hRscale, hBscale]
    simpa only [sourceLemma92Decay] using
      sourceLemma92_secondPoissonBudget_scaled_uniform hT hM hMhi hF0 hF hc
        hreserve
  have hbudget' :
      ((T / (M : ℝ)) *
          (R * sourceBumpFourierConstant 1 zero_lt_one (q + 2)) *
          ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
            max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        (25 * c * sourceLemma92Decay q * integerQuadraticMass) *
          (Real.rpow T delta) ^ q) := by
    simpa only [hBscale] using hbudget
  have hraw :=
    sigmaIIFinite_selectedPositiveDyadic_variableEllRadius_unequalScale_le
      (delta := delta) (M3 := M3) (R := R)
      (Ctail := 25 * c * sourceLemma92Decay q * integerQuadraticMass)
      hf hM mRange hmRange q hRpos hRone hM3pos hT hF0 hF hMhi hCtau
      hCtail hbudget'
  have hraw' :
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hRpos x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 Ctau ≤
        ((2 * Ctau * (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F (2 * B)))
              (affineSmoothing T (fun z => sourceBump B hBpos z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau)) *
              ((25 * c * sourceLemma92Decay q * integerQuadraticMass) /
                T ^ 100)) := by
    simpa only [hBscale] using! hraw
  have hJscale := sourceAffineJ_sourceBump_eq_scale_normalized hTpos hBpos
    (sourcePositiveDyadicRange M)
    (sourceLemma92JRange M T F (2 * B)) f
  rw [hJscale] at hraw'
  exact hraw'

end GuthMaynardS3UnequalScaleSecondPoisson

#print axioms GuthMaynardS3UnequalScaleSecondPoisson.sourceLemma92_secondPoissonBudget_scaled_uniform
#print axioms GuthMaynardS3UnequalScaleSecondPoisson.sigmaIIFinite_selectedPositiveDyadic_scaledRadius_unequalScale_normalizedJcoll_le
