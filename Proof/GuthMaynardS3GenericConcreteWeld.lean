import GuthMaynardS3MediumFullActual
import GuthMaynardS3MediumActualUnequalSplit
import GuthMaynardS3LiteralLemma92NonzeroMedium

set_option maxHeartbeats 3000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3GenericConcreteWeld

open GuthMaynardJIteration
open GuthMaynardS3MediumFullActual
open GuthMaynardS3MediumActualUnequalSplit
open GuthMaynardS3LiteralLemma84Outer
open GuthMaynardS3LiteralLemma92NonzeroMedium
open GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardHeathBrownInterface

/-! Generic concrete weld for the central medium term.  All profile-specific
Fourier work is supplied through `hinner`, `hfullInt`, `hfhat`, and the
explicit discarded-tail bound `htail`; this theorem only factors the exact
full-Sigma-II insertion, unequal-radius normalized J consumer, and scalar
coefficient.  In particular, `F` remains in the J range and is not replaced
by a hard-coded wide-profile radius. -/
theorem sourceGFinite_mediumIntegral_le_Ceta_actualNormalizedSigmaII_genericConcrete
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hF0 : 0 ≤ F) (hF : F ≤ T)
    {M M1 M2 M3 : ℕ} (hM : 0 ≤ (M : ℝ))
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM3 : 1 ≤ M3)
    (hM1M : (M1 : ℝ) ≤ M) (hM2M : (M2 : ℝ) ≤ M)
    (hM3M : (M3 : ℝ) ≤ M)
    {eta delta Ceta Hinner Y C Ctail : ℝ} (hT : 1 ≤ T)
    (heta : 0 < eta)
    (heta1 : eta ≤ 1) (hdelta : 0 ≤ delta)
    (hM1T : (M1 : ℝ) ≤ T) (hM3T : (M3 : ℝ) ≤ T)
    (hCeta : 0 < Ceta) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (hHinner : 0 ≤ Hinner) (q : ℕ) (ellRange m3Range : Finset ℤ)
    (hsupport : ∀ m3 : ℤ, m3 ∉ m3Range →
      (sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ) = 0)
    (hcount : ∀ ellRange : Finset ℤ, ∀ xi ∈
      mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T),
      ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
        (nonzeroEllRange ellRange) (M3 : ℝ) (Real.rpow T eta) xi).card : ℝ) ≤
        Ceta * Real.rpow T (2 * eta) *
          (1 + (M1 : ℝ) / (M3 : ℝ)))
    (hbudget : (M3 : ℝ) * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        ((1 + Y / (1 / (M3 : ℝ))) ^ 2 *
          max 1 ((1 / (M3 : ℝ)) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        C * (Real.rpow T eta) ^ q)
    (hcover : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ sourceSignedDyadicRange M1, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
          (|(m1 : ℝ)| / (M3 : ℝ)) * Real.rpow T eta →
        ell ∈ ellRange)
    (hxi : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ sourceSignedDyadicRange M1,
        |xi / (m1 : ℝ)| ≤ Y)
    (hinner : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T), ∀ m1 ∈ sourceSignedDyadicRange M1,
      ‖sourceCorrectedM2FourierInner (sourcePositiveDyadicRange M2)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤ Hinner)
    (hfullInt : IntegrableOn (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2) m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2)
      (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T)))
    (hM2M3 : (M2 : ℝ) ≤ M3)
    (hM3lo : (M2 : ℝ) ≤ M3) (hM3hi : (M3 : ℝ) ≤ 16 * (M2 : ℝ))
    (hM2hiT : (M2 : ℝ) ≤ T ^ (4 : ℝ))
    (hEllCard :
      ((ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / (M2 : ℝ))).card : ℝ) ≤
        T ^ (11 : ℝ))
    (hm2lo : ∀ m2' ∈ sourcePositiveDyadicRange M2,
      (M2 : ℝ) ≤ |(m2' : ℝ)|)
    (hm2hi : ∀ m2' ∈ sourcePositiveDyadicRange M2,
      |(m2' : ℝ)| ≤ 2 * (M2 : ℝ))
    (hcard : ((sourcePositiveDyadicRange M2).card : ℝ) ≤ T ^ (4 : ℝ))
    (hSgrowth : S ≤ T ^ (4 : ℝ))
    (hdeltaB : 0 < Real.rpow T delta)
    (hreserve : eta + 107 ≤ delta * (q : ℝ))
    (hqtail : (300 : ℝ) ≤ eta * q)
    (htail : sigmaIIEllTailFiniteLE ellRange
        (sourcePositiveDyadicRange M2)
        ((4 * Real.rpow T eta) * T / (M2 : ℝ)) (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M2 : ℝ) T M3 (Real.rpow T eta) ≤
      (2 * Real.rpow T eta) *
        (4 * Ctail ^ 2 * Real.rpow T (-229 : ℝ)))
    (hfhat : Continuous
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))) :
    (∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2) m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      16 * Ceta * Real.rpow T (2 * eta) *
          (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
          ((M1 : ℝ) + (M3 : ℝ)) *
        ((((2 * (Real.rpow T eta) *
          ((4 * (Real.rpow T eta)) *
            sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M2 : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            ((4 * (Real.rpow T delta)) ^ 2 *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M2)
                  (sourceLemma92JRange M2 T F
                    (2 * Real.rpow T delta)))
                (affineSmoothing T
                  (sourceBumpNormalized (Real.rpow T delta)
                    hdeltaB) f))) +
        (∑ m2 ∈ sourcePositiveDyadicRange M2,
          ∑ m2' ∈ sourcePositiveDyadicRange M2,
            |(m2 : ℝ) * (m2' : ℝ)| *
              (((∫ u : ℝ, |f u|) ^ 2 *
                  (2 * (Real.rpow T eta))) *
                ((25 * 4 * sourceLemma92Decay q * integerQuadraticMass) /
                  T ^ 100))) +
        (2 * Real.rpow T eta) *
          (4 * Ctail ^ 2 * Real.rpow T (-229 : ℝ)))) +
      9216 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
          Real.rpow T eta * (M : ℝ) ^ 6 *
          (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 +
      2 * volume.real (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T)) *
        ((C / T ^ 100) * (4 * (M1 : ℝ) * Hinner)) ^ 2 := by
  have hM2pos : 0 < (M2 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM2)
  have hM3pos : 0 < (M3 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM3)
  have hM2hiTN : (M2 : ℝ) ≤ T ^ (4 : ℕ) := by
    convert hM2hiT using 1 <;> norm_num [Real.rpow_natCast]
  have hSigma :=
    sourceGFinite_mediumIntegral_le_Ceta_fullSigmaII_add_zero_tail
      (T := T) (S := S) (F := F) (f := f) hf hM hM1 hM2 hM3 hM1M hM2M hM3M
      hT heta heta1 hM1T hM3T hCeta hY hC hHinner q ellRange m3Range
      hsupport hcount hbudget hcover hxi hinner hfullInt
      (fun _ => 1) (M2 : ℝ)
      (by intro ell hell; norm_num)
      (by intro ell hell; norm_num)
      hfhat
  have hsplit :=
    sigmaIIFinite_const_one_le_scaledSourceBump_add_literalEllTail
      (T := T) (S := S) (F := F) (eta := eta) (delta := delta)
      (M3 := (M3 : ℝ)) (f := f) hf (M := M2)
      (mRange := sourcePositiveDyadicRange M2)
      (ellRange := ellRange) (by exact_mod_cast hM2)
      (by exact Finset.Subset.rfl) q hT hF0 hF hM2hiTN hM3lo hM3hi heta hdelta
      hdeltaB hreserve
  have htail_replace : ∀ {x y z z' : ℝ},
      x ≤ y + z → z ≤ z' → x ≤ y + z' := by
    intro x y z z' hxy hz
    linarith
  have hSigmaBound := htail_replace hsplit htail
  have hK0 : 0 ≤ sourceBumpFourierConstant 1 zero_lt_one 0 :=
    sourceBumpFourierConstant_nonneg 1 zero_lt_one 0
  have hA : 0 ≤ 16 * Ceta * Real.rpow T (2 * eta) *
      (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
      ((M1 : ℝ) + (M3 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCeta.le)
          (Real.rpow_nonneg (le_trans zero_le_one hT) _))
        (sq_nonneg _))
      (by positivity)
  calc
    _ ≤ 16 * Ceta * Real.rpow T (2 * eta) *
        (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
        ((M1 : ℝ) + (M3 : ℝ)) *
          sigmaIIFinite ellRange (sourcePositiveDyadicRange M2) (fun _ => 1)
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            (M2 : ℝ) T (M3 : ℝ) (Real.rpow T eta) +
        9216 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
            Real.rpow T eta * (M : ℝ) ^ 6 *
            (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 +
        2 * volume.real (mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T)) *
          ((C / T ^ 100) * (4 * (M1 : ℝ) * Hinner)) ^ 2 := hSigma
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hSigmaBound hA
      have hadd3 : ∀ {x y e r : ℝ}, x ≤ y → x + e + r ≤ y + e + r := by
        intro x y e r hxy
        linarith
      simpa only [mul_assoc] using (hadd3 hmul)

end GuthMaynardS3GenericConcreteWeld

#print axioms GuthMaynardS3GenericConcreteWeld.sourceGFinite_mediumIntegral_le_Ceta_actualNormalizedSigmaII_genericConcrete
