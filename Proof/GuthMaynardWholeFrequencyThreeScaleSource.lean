import GuthMaynardJIterationFrequencyCompleteV2
import GuthMaynardLemma92ThreeScaleSigmaBound
import GuthMaynardWholeFrequencyDyadicStructuralInputs
import GuthMaynardHighFrequencyBudget
import GuthMaynardLowFrequencyPairBudget

/-!
# Literal three-scale whole-frequency source theorem

This instantiates every finite range in the corrected low/medium/high theorem:
`M₁` controls the signed numerator block and first-Poisson ell cover, `M₂`
controls the positive detector block, and `M₃` controls the affine shift and
literal bump-support window.  No equality of these scales is imposed.
-/

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def sourceDyadicN1 (M1 : ℕ) : ℝ := 4 * (M1 : ℝ) + 3
def sourceDyadicN2 (M2 : ℕ) : ℝ := 4 * (M2 : ℝ) + 3
def sourceDyadicN3 (M3 : ℕ) : ℝ := 4 * (M3 : ℝ) + 3

def sourceDyadicRlo (M1 M2 : ℕ) : ℝ :=
  (M2 : ℝ) / (2 * (M1 : ℝ))
def sourceDyadicRhi (M1 M2 : ℕ) : ℝ :=
  (2 * (M2 : ℝ)) / (M1 : ℝ)

def sourceThreeScaleHinner (f : ℝ → ℝ) (M1 M2 : ℕ) : ℝ :=
  sourceDyadicN2 M2 * sourceDyadicRhi M1 M2 *
    (∫ u : ℝ, ‖(f u : ℂ)‖)

def sourceThreeScaleHighConstant (S Cdec : ℝ) : ℝ :=
  ((686 * Cdec * S) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass

/-- The radius-two `m₃` support has cardinality `7T` rather than the `5T`
plateau range.  With this corrected constant, the published order `77`
still pays the complete high-frequency tail. -/
theorem sourceHighFrequencyBudget_of_literalWholeSupportScaleBounds
    {T N1 N2 N3 P1 Rhi Cdec S Rlo : ℝ}
    (hT : 1 ≤ T)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi) (hCdec : 0 ≤ Cdec)
    (hS : 0 ≤ S) (hRlo : 0 < Rlo)
    (hN1scale : N1 ≤ 7 * T) (hN2scale : N2 ≤ 7 * T)
    (hN3scale : N3 ≤ 7 * T) (hP1scale : P1 ≤ 1)
    (hRhiscale : Rhi ≤ 2 * T)
    (hratio : T / Rlo ≤ 2 * T ^ 5) :
    ((N1 * N2 * N3 * P1 * Rhi *
          (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S)) /
        (sourceHighFrequencyCutoff T) ^ 77) ^ 2 *
          quarticDecayMass * T ^ 100 ≤
      ((686 * Cdec * S) * 2 ^ 79 * 2 ^ 79) ^ 2 * quarticDecayMass := by
  have hprefix : N1 * N2 * N3 * P1 * Rhi * Cdec * S ≤
      (686 * Cdec * S) * T ^ 16 := by
    calc
      N1 * N2 * N3 * P1 * Rhi * Cdec * S ≤
          (7 * T) * (7 * T) * (7 * T) * 1 * (2 * T) * Cdec * S := by
        gcongr
      _ = (686 * Cdec * S) * T ^ 4 := by ring
      _ ≤ (686 * Cdec * S) * T ^ 16 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (show 4 ≤ 16 by omega)) (by positivity)
  have henv := sourceHighFrequencyEnvelope_polynomialGrowth 0 hT
    hN1 hN2 hN3 hP1 hRhi hCdec hS hRlo
    (by positivity : 0 ≤ 686 * Cdec * S) (by norm_num : 0 ≤ (2 : ℝ))
    hprefix hratio
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hratio0 : 0 ≤ T / Rlo := div_nonneg hT0 hRlo.le
  have hfront : 0 ≤ N1 * N2 * N3 * P1 * Rhi :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hN1 hN2) hN3) hP1) hRhi
  have hinside : 0 ≤
      Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCdec (Real.rpow_nonneg hT0 1))
          (pow_nonneg hratio0 79))
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 79))
      hS
  have hK0 : 0 ≤ N1 * N2 * N3 * P1 * Rhi *
      (Cdec * Real.rpow T 1 * (T / Rlo) ^ 79 * 2 ^ 79 * S) := by
    exact mul_nonneg hfront hinside
  have hbudget := sourceHighFrequencyBudget_of_polynomialGrowth 27 hT
    hK0
    (by positivity : 0 ≤ (686 * Cdec * S) * 2 ^ 79 * 2 ^ 79)
    (le_rfl : quarticDecayMass ≤ quarticDecayMass)
    (by
      norm_num at henv ⊢
      simpa [mul_assoc] using henv)
  norm_num at hbudget ⊢
  exact hbudget

/-- The exact right-hand side after all source ranges and elementary
cardinality envelopes are inserted. -/
def sourceThreeScaleWholeFrequencyBound
    (T etaFreq etaPair B C Kpsi Cdiv sigmaBound CIII : ℝ)
    (M1 M3 : ℕ) (P N1 Hinner : ℝ) : ℝ :=
  (4 * sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ) *
      (P ^ 2 * ((M3 : ℝ) * Kpsi) ^ 2 * Hinner ^ 2) +
    4 * sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ) *
      ((C / T ^ 100) * (N1 * Hinner)) ^ 2) +
  ((2 * (((14 * B + 3) * Cdiv *
      Real.rpow (sourceHighFrequencyCutoff T +
        7 * (M1 : ℝ) / (M3 : ℝ) * B) etaPair) *
      7 * Kpsi ^ 2 * ((M1 : ℝ) + (M3 : ℝ)))) * sigmaBound +
    2 * volume.real (mediumFrequencyRegion
      (sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
      (sourceHighFrequencyCutoff T)) *
      ((C / T ^ 100) * (N1 * Hinner)) ^ 2) +
  CIII / T ^ 100

set_option maxHeartbeats 800000 in
/-- Literal whole-frequency v2 specialization.  The only remaining premises
are scalar scale separations and the already source-facing Fourier-tail and
second-Poisson budgets used by the certified three-scale `SigmaII` theorem.
All range, support, pair-count, integrability, and high-frequency inputs are
constructed in the proof. -/
theorem exists_sourceDyadic_threeScale_wholeFrequency_bound
    {T S F delta etaFreq etaPair : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (qPoisson qSigma j : ℕ)
    {Csecond etaTail Ctail kappa : ℝ}
    (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T) (hS1 : S ≤ 1)
    (hM1T : (M1 : ℝ) ≤ T) (hM2T : (M2 : ℝ) ≤ T)
    (hM3T : (M3 : ℝ) ≤ T)
    (hM2hi : (M2 : ℝ) ≤ T ^ 4)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
    (hcut : sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ) ≤
      sourceHighFrequencyCutoff T)
    (hwindowBelowMedium :
      7 * (M1 : ℝ) / (M3 : ℝ) * Real.rpow T delta <
        sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
    (hetaPair : 0 < etaPair)
    (hRone : 1 ≤ Real.rpow T kappa)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa)
    (hCsecond : 0 ≤ Csecond) (hCtail : 0 ≤ Ctail)
    (hFourierTail : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Ctail * T ^ etaTail * (T / |z|) ^ j * S)
    (hsecondBudget :
      ((T / (M2 : ℝ)) *
          (Real.rpow T kappa *
            sourceBumpFourierConstant 1 zero_lt_one (qSigma + 2)) *
          ((1 + (4 * (M2 : ℝ) * F) / ((M2 : ℝ) / T)) ^ 2 *
            max 1 (((M2 : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        Csecond * (T ^ delta) ^ qSigma))
    (hconstant : 2744 * Ctail ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * etaTail ≤
      2 * kappa * (j : ℝ)) :
    ∃ Kpsi C Cdec Cdiv : ℝ,
      0 ≤ Kpsi ∧ 0 ≤ C ∧ 0 ≤ Cdec ∧ 0 < Cdiv ∧
      (∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2)
            (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
        sourceThreeScaleWholeFrequencyBound T etaFreq etaPair
          (Real.rpow T delta) C Kpsi Cdiv
          (sourceThreeScaleSigmaBound T F delta (Real.rpow T kappa)
            Csecond f M2 (sourcePositiveDyadicRange M2)
            (lt_of_lt_of_le zero_lt_one hT))
          (sourceThreeScaleHighConstant S Cdec)
          M1 M3
          (sourceLowLocalizedPairBudget (sourceDyadicN1 M1)
            (sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
            (M1 : ℝ) (Real.rpow T delta) (M3 : ℝ))
          (sourceDyadicN1 M1)
          (sourceThreeScaleHinner f M1 M2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hBpos : 0 < Real.rpow T delta := Real.rpow_pos_of_pos hTpos delta
  have hB0 : 0 ≤ Real.rpow T delta := hBpos.le
  have hM1R : 0 < (M1 : ℝ) := Nat.cast_pos.mpr hM1
  have hM2R : 0 < (M2 : ℝ) := Nat.cast_pos.mpr hM2
  have hM3R : 0 < (M3 : ℝ) := Nat.cast_pos.mpr hM3
  have hrange := sourceDyadic_wholeFrequency_rangeFacts hM1 hM2
  rcases hrange with ⟨hm1ne, hm1lo, hm1hi2, hm2pos, hratioLo, hratioHi⟩
  have hm2ne : ∀ m2 ∈ sourcePositiveDyadicRange M2, m2 ≠ 0 :=
    fun m2 hm2 => (hm2pos m2 hm2).ne'
  have hN1card := card_sourceSignedDyadicRange_cast_le M1
  have hN2card := card_sourcePositiveDyadicRange_cast_le M2
  have hN3card := card_centeredTwoScale_cast_le M3
  have hN1zero : 0 ≤ sourceDyadicN1 M1 := by unfold sourceDyadicN1; positivity
  have hN2zero : 0 ≤ sourceDyadicN2 M2 := by unfold sourceDyadicN2; positivity
  have hN3zero : 0 ≤ sourceDyadicN3 M3 := by unfold sourceDyadicN3; positivity
  have hRlo : 0 < sourceDyadicRlo M1 M2 := by
    unfold sourceDyadicRlo
    positivity
  have hRhi0 : 0 ≤ sourceDyadicRhi M1 M2 := by
    unfold sourceDyadicRhi
    positivity
  have hcard1 : ((sourceSignedDyadicRange M1).card : ℝ) ≤
      sourceDyadicN1 M1 := by simpa [sourceDyadicN1] using hN1card
  have hcard2 : ((sourcePositiveDyadicRange M2).card : ℝ) ≤
      sourceDyadicN2 M2 := by simpa [sourceDyadicN2] using hN2card
  have hcard3 : ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) ≤
      sourceDyadicN3 M3 := by simpa [sourceDyadicN3] using hN3card
  have hcard1scale : sourceDyadicN1 M1 ≤ 7 * (M1 : ℝ) := by
    unfold sourceDyadicN1
    have hM1one : (1 : ℝ) ≤ (M1 : ℝ) := by exact_mod_cast hM1
    nlinarith
  have hm1hi : ∀ m1 ∈ sourceSignedDyadicRange M1,
      |(m1 : ℝ)| ≤ 7 * (M1 : ℝ) := by
    intro m1 hm1
    have hM1zero : 0 ≤ (M1 : ℝ) := Nat.cast_nonneg M1
    exact (hm1hi2 m1 hm1).trans (by nlinarith)
  have hsupport : ∀ m3 : ℤ,
      m3 ∉ sourceIntegerWindow 0 (2 * (M3 : ℝ)) →
        (sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ) = 0 := by
    intro m3 hm3
    rw [sourceBump_eq_zero_outside_centeredTwoScale hM3 hm3]
    norm_num
  let Y : ℝ := sourceHighFrequencyCutoff T / (M1 : ℝ)
  have hY : 0 ≤ Y := by
    dsimp only [Y]
    unfold sourceHighFrequencyCutoff
    positivity
  obtain ⟨K0, K, Kpsi, C, hK, hKpsi, hC,
      hbumpCompact, hbumpSmooth, hbumpBounded, hbumpDecay2,
      hbumpDecay, hfirstBudget⟩ :=
    exists_sourceBump_firstPoissonPackage hTpos hY hM3R hBpos qPoisson
  obtain ⟨Cdec, hCdec, hfdecay⟩ :=
    sourceFourierRapidDecay_at_dyadicRatio
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
      hf.rapidDecay zero_lt_one 79
  have hfrequency := sourceLemma92ThreeScale_frequency_inputs
    (sourceSignedDyadicRange M1) hM1 hM3 (by intro m hm; exact hm)
    hT hB0 hB6 hcut hcard1
  rcases hfrequency with ⟨_, hcoverLow, hcoverMedium⟩
  have hpairCardLow : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ)),
      ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
        (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
        (M3 : ℝ) (Real.rpow T delta) xi).card : ℝ) ≤
        sourceLowLocalizedPairBudget (sourceDyadicN1 M1)
          (sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
          (M1 : ℝ) (Real.rpow T delta) (M3 : ℝ) := by
    intro xi hxi
    exact card_sourceMediumLocalizedPairs_low_le_sourceBudget
      (sourceSignedDyadicRange M1)
      (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
      hM1 hM3 (by intro m hm; exact hm) hcut0 hB0 hcard1 hxi
  have hphase := sourceLowMedium_abs_div_le_highCutoff
    (sourceSignedDyadicRange M1) hM1R hcut hm1lo
  rcases hphase with ⟨hxiLow, hxiMedium⟩
  have hinner := sourceCorrectedM2FourierInner_lowMedium_le_integral_norm
    (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2) f
    (a := sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
    (b := sourceHighFrequencyCutoff T)
    hcard2 hRhi0 hratioHi
  rcases hinner with ⟨hinnerLow, hinnerMedium⟩
  have hpsi : ∀ m3 ∈ sourceIntegerWindow 0 (2 * (M3 : ℝ)),
      ‖(sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ)‖ ≤ 1 := by
    intro m3 hm3
    exact norm_sourceBump_unit_le_one _
  have hghat := integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
    (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
    (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
    (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    hf zero_lt_one hTpos.le hRlo hN1zero hN2zero hN3zero
    (by norm_num : 0 ≤ (1 : ℝ)) hRhi0 hcard1 hcard2 hcard3
    hm1ne hm2ne hpsi hratioLo hratioHi
  have hbumpInt : Integrable
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) :=
    (sourceBump 1 zero_lt_one).integrable.ofReal
  have hbumpFourierCont : Continuous
      (FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hbumpInt
  have hfFourierCont := continuous_fourier_of_integrable f hf.integrable
  have hlocalized := sourceFirstPoissonLocalizedPairSum_regionIntegrable
    (sourceSignedDyadicRange M1)
    (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
    (sourcePositiveDyadicRange M2)
    (FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)))
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
    hbumpFourierCont hfFourierCont
    (a := sourceLowFrequencyCutoff T etaFreq (M1 : ℝ) (M3 : ℝ))
    (b := sourceHighFrequencyCutoff T) hM3R hB0
  rcases hlocalized with ⟨hlowLocalizedInt, hmediumLocalizedInt⟩
  have hsigma :=
    sigmaIIFinite_threeScale_selectedPositiveDyadic_le_named
      hf hM1 hM2 hM3 (sourcePositiveDyadicRange M2)
      (by intro m hm; exact hm) qSigma j rfl hRone hT hF0 hF hS1
      hM2hi hM2T hB6 hhalf hCsecond hCtail hFourierTail
      hsecondBudget hconstant hexponent
  have hN1scale : sourceDyadicN1 M1 ≤ 7 * T :=
    hcard1scale.trans (mul_le_mul_of_nonneg_left hM1T (by norm_num))
  have hN2scale : sourceDyadicN2 M2 ≤ 7 * T := by
    unfold sourceDyadicN2
    have hM2one : (1 : ℝ) ≤ (M2 : ℝ) := by exact_mod_cast hM2
    nlinarith
  have hN3scale : sourceDyadicN3 M3 ≤ 7 * T := by
    unfold sourceDyadicN3
    have hM3one : (1 : ℝ) ≤ (M3 : ℝ) := by exact_mod_cast hM3
    nlinarith
  have hRhiscale : sourceDyadicRhi M1 M2 ≤ 2 * T := by
    unfold sourceDyadicRhi
    have hM1one : (1 : ℝ) ≤ (M1 : ℝ) := by exact_mod_cast hM1
    calc
      2 * (M2 : ℝ) / (M1 : ℝ) ≤ 2 * (M2 : ℝ) :=
        div_le_self (by positivity) hM1one
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hM2T (by norm_num)
  have hratioBudget : T / sourceDyadicRlo M1 M2 ≤ 2 * T ^ 5 := by
    unfold sourceDyadicRlo
    exact sourceDyadic_reciprocal_ratio_le_two_mul_time_pow_five
      hM1 hM2 hT hM1T
  let CIII : ℝ := sourceThreeScaleHighConstant S Cdec
  have hCIII :
      ((sourceDyadicN1 M1 * sourceDyadicN2 M2 * sourceDyadicN3 M3 * 1 *
          sourceDyadicRhi M1 M2 *
          (Cdec * Real.rpow T 1 * (T / sourceDyadicRlo M1 M2) ^ 79 *
            2 ^ 79 * S)) /
        (sourceHighFrequencyCutoff T) ^ 77) ^ 2 *
          quarticDecayMass * T ^ 100 ≤ CIII := by
    simpa only [CIII, sourceThreeScaleHighConstant] using
      sourceHighFrequencyBudget_of_literalWholeSupportScaleBounds
        hT hN1zero hN2zero hN3zero (by norm_num : 0 ≤ (1 : ℝ))
        hRhi0 hCdec hf.bound_nonneg hRlo hN1scale hN2scale hN3scale
        (le_rfl : (1 : ℝ) ≤ 1) hRhiscale hratioBudget
  obtain ⟨Cdiv, hCdiv, hwhole⟩ :=
    exists_sourceGFinite_frequencyIntegral_le_correctedSigmaII_v2
      (sourceSignedDyadicRange M1)
      (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
      (sourcePositiveDyadicRange M2)
      (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) f hf.integrable
      (fun _ => 1)
      T etaFreq etaPair (M1 : ℝ) (M2 : ℝ) (M3 : ℝ)
      (Real.rpow T delta)
      (sourceThreeScaleSigmaBound T F delta (Real.rpow T kappa)
        Csecond f M2 (sourcePositiveDyadicRange M2) hTpos)
      qPoisson 77
      hbumpCompact hbumpSmooth hM1R hM3R hBpos hY hK hKpsi hC
      (by
        unfold sourceLowLocalizedPairBudget
        positivity)
      hN1zero
      (by
        have hint : 0 ≤ ∫ u : ℝ, ‖(f u : ℂ)‖ :=
          integral_nonneg fun _ => norm_nonneg _
        exact mul_nonneg (mul_nonneg hN2zero hRhi0) hint)
      (by norm_num : 0 ≤ (7 : ℝ))
      (by positivity : 0 ≤ 14 * Real.rpow T delta + 3)
      hetaPair hT hcut0 hcut (by nlinarith)
      (by nlinarith : 2 * 7 * Real.rpow T delta ≤
        14 * Real.rpow T delta + 3)
      hwindowBelowMedium hbumpBounded hbumpDecay2 hbumpDecay hfirstBudget
      hm1ne hm1lo hm1hi hm2pos hsupport hcard1 hcard1scale
      hpairCardLow hcoverLow hxiLow hinnerLow hcoverMedium
      (by intro ell hell; norm_num)
      hxiMedium hinnerMedium hghat hlowLocalizedInt hmediumLocalizedInt hsigma
      hf.bound_nonneg hCdec hRlo hN1zero hN2zero hN3zero
      (by norm_num : 0 ≤ (1 : ℝ)) hRhi0 hcard1 hcard2 hcard3 hpsi
      hratioLo hratioHi hfdecay hCIII
  refine ⟨Kpsi, C, Cdec, Cdiv, hKpsi, hC, hCdec, hCdiv, ?_⟩
  simpa only [sourceThreeScaleWholeFrequencyBound,
    sourceThreeScaleHinner, sourceDyadicN1, sourceDyadicN2,
    sourceThreeScaleHighConstant, CIII] using hwhole

#print axioms GuthMaynardJIteration.exists_sourceDyadic_threeScale_wholeFrequency_bound

end GuthMaynardJIteration
