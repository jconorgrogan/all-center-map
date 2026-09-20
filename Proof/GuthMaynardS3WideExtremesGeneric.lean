import GuthMaynardSourceGGeneralPlancherel
import ownnewLemma92RegionHighCommonCdec
import GuthMaynardLemma92EllWindowSupport
import GuthMaynardWholeFrequencyDyadicStructuralInputs

set_option maxHeartbeats 4000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3WideExtremesGeneric

open GuthMaynardJIteration

theorem profile_lowFrequencyIntegral_le
    {T eta S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (L1 : ℝ) (hL1 : 0 ≤ L1)
    (hL1bound : ∀ z : ℝ,
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤ L1)
    (hT : 1 ≤ T) (heta : 0 < eta)
    {M M1 M2 M3 : ℕ}
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM3 : 1 ≤ M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M) :
    (∫ xi in lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ)),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceBumpEllRange 1 (M3 : ℝ) 1)
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM1pos : 0 < M1 := lt_of_lt_of_le Nat.zero_lt_one hM1
  have hM2pos : 0 < M2 := lt_of_lt_of_le Nat.zero_lt_one hM2
  have hM3pos : 0 < M3 := lt_of_lt_of_le Nat.zero_lt_one hM3
  let m1Range := sourceSignedDyadicRange M1
  let m2Range := sourcePositiveDyadicRange M2
  let m3Range := sourceBumpEllRange 1 (M3 : ℝ) 1
  let fhat : ℝ → ℂ := FourierTransform.fourier
    (fun u : ℝ => (f u : ℂ))
  let ghat : ℝ → ℂ := FourierTransform.fourier
    (sourceGFinite m1Range m2Range m3Range
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      (fun u : ℝ => (f u : ℂ)) (M3 : ℝ))
  have hL10 : 0 ≤ L1 := hL1
  have hN1 : (m1Range.card : ℝ) ≤ 7 * (M1 : ℝ) := by
    dsimp [m1Range]
    have hc := card_sourceSignedDyadicRange_cast_le M1
    nlinarith [show (1 : ℝ) ≤ (M1 : ℝ) by exact_mod_cast hM1]
  have hN2 : (m2Range.card : ℝ) ≤ 7 * (M2 : ℝ) := by
    dsimp [m2Range]
    have hc := card_sourcePositiveDyadicRange_cast_le M2
    nlinarith [show (1 : ℝ) ≤ (M2 : ℝ) by exact_mod_cast hM2]
  have hN3 : (m3Range.card : ℝ) ≤ 7 * (M3 : ℝ) := by
    have heq : m3Range = sourceIntegerWindow 0 (2 * (M3 : ℝ)) := by
      ext m3
      simp [m3Range, sourceBumpEllRange]
    rw [heq]
    have hc := card_sourceIntegerWindow_cast_le 0 (2 * (M3 : ℝ))
      (by positivity : (0 : ℝ) ≤ 2 * (M3 : ℝ))
    nlinarith [show (1 : ℝ) ≤ (M3 : ℝ) by exact_mod_cast hM3]
  have hcard1 : (m1Range.card : ℝ) ≤ 7 * (M : ℝ) :=
    hN1.trans (by gcongr)
  have hcard2 : (m2Range.card : ℝ) ≤ 7 * (M : ℝ) :=
    hN2.trans (by gcongr)
  have hcard3 : (m3Range.card : ℝ) ≤ 7 * (M : ℝ) :=
    hN3.trans (by gcongr)
  have hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0 := by
    intro m1 hm
    exact sourceSignedDyadicRange_ne_zero hM1pos hm
  have hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0 := by
    intro m2 hm
    exact sourcePositiveDyadicRange_ne_zero hM2pos hm
  have hpsi : ∀ m3 ∈ m3Range,
      ‖(sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ)‖ ≤ 1 := by
    intro m3 hm
    exact norm_sourceBump_unit_le_one _
  have hRlo : 0 < (M2 : ℝ) / (2 * (M1 : ℝ)) := by positivity
  have hRhi : 0 ≤ (2 * (M2 : ℝ)) / (M1 : ℝ) := by positivity
  have hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      (M2 : ℝ) / (2 * (M1 : ℝ)) ≤ |((m2 : ℝ) / (m1 : ℝ))| := by
    intro m1 hm1' m2 hm2'
    exact (sourceDyadic_ratio_bounds hM1pos hM2pos hm1' hm2').1
  have hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ (2 * (M2 : ℝ)) / (M1 : ℝ) := by
    intro m1 hm1' m2 hm2'
    exact (sourceDyadic_ratio_bounds hM1pos hM2pos hm1' hm2').2
  have hL1bound' : ∀ z : ℝ, ‖fhat z‖ ≤ L1 := by
    intro z
    dsimp [fhat]
    exact hL1bound z
  have hghat : Integrable (fun xi : ℝ =>
      ‖ghat (xi)‖ ^ 2) := by
    dsimp [ghat]
    exact integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
      m1Range m2Range m3Range
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      (fReal := f) (T := T)
      (S := S) (F := F) (M3 := (M3 : ℝ))
      (N1 := 7 * (M : ℝ)) (N2 := 7 * (M : ℝ)) (N3 := 7 * (M : ℝ))
      (P1 := 1) (Rhi := (2 * (M2 : ℝ)) / (M1 : ℝ))
      hf (eta := (1 : ℝ)) (heta := by norm_num) (hT := hT0) (hRlo := hRlo)
      (hN1 := by positivity) (hN2 := by positivity) (hN3 := by positivity)
      (hP1 := by positivity) (hRhi := hRhi)
      (hcard1 := hcard1) (hcard2 := hcard2) (hcard3 := hcard3)
      (hm1 := hm1) (hm2 := hm2) (hpsi := hpsi)
      (hratioLo := hratioLo) (hratioHi := hratioHi)
  have hpoint : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ)),
      ‖ghat (xi)‖ ^ 2 ≤
        ((7 * (M1 : ℝ)) * (7 * (M2 : ℝ)) * (7 * (M3 : ℝ)) *
          (2 * (M2 : ℝ) / (M1 : ℝ)) * L1) ^ 2 := by
    intro xi hxi
    have hnorm := norm_fourier_sourceGFinite_le_of_fhat_bound
      m1Range m2Range m3Range
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      (fun u : ℝ => (f u : ℂ))
      hf.integrable.ofReal (M3 : ℝ) xi
      (N1 := 7 * (M1 : ℝ)) (N2 := 7 * (M2 : ℝ))
      (N3 := 7 * (M3 : ℝ)) (P1 := 1)
      (Rhi := (2 * (M2 : ℝ)) / (M1 : ℝ)) (D := L1)
      (hN1 := by positivity) (hN2 := by positivity) (hN3 := by positivity)
      (hP1 := by positivity) (hRhi := hRhi) (hD0 := hL10)
      (hcard1 := hN1) (hcard2 := hN2) (hcard3 := hN3)
      (hm1 := hm1) (hm2 := hm2) (hpsi := hpsi)
      (hratio := hratioHi) (hfhat := fun _ _ _ _ => hL1bound _)
    dsimp [ghat]
    have hnorm' : ‖ghat xi‖ ≤
        (7 * (M1 : ℝ)) * (7 * (M2 : ℝ)) * (7 * (M3 : ℝ)) *
          (2 * (M2 : ℝ) / (M1 : ℝ)) * L1 := by
      simpa [one_mul] using hnorm
    have hbound0 : 0 ≤
        (7 * (M1 : ℝ)) * (7 * (M2 : ℝ)) * (7 * (M3 : ℝ)) *
          (2 * (M2 : ℝ) / (M1 : ℝ)) * L1 := by positivity
    exact (sq_le_sq₀ (norm_nonneg _) hbound0).2 hnorm'
  have hcut0 : 0 ≤ sourceLowFrequencyCutoff T eta
      (M1 : ℝ) (M3 : ℝ) := by
    have hpowpos : 0 < Real.rpow T eta := Real.rpow_pos_of_pos hTpos eta
    unfold sourceLowFrequencyCutoff
    positivity
  have hlow := sourceLowFrequencyIntegral_le ghat hcut0 hghat.integrableOn hpoint
  have hM1R : (M1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1M
  have hM2R : (M2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2M
  have hM3R : (M3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3M
  dsimp [ghat, fhat] at hlow ⊢
  have hmain :
      2 * sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ) *
        ((7 * (M1 : ℝ)) * (7 * (M2 : ℝ)) * (7 * (M3 : ℝ)) *
          (2 * (M2 : ℝ) / (M1 : ℝ)) *
          L1) ^ 2 ≤
      941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 *
        L1 ^ 2 := by
    unfold sourceLowFrequencyCutoff
    have hpow : Real.rpow T eta ≤ Real.rpow T (3 * eta) := by
      apply Real.rpow_le_rpow_of_exponent_le hT
      linarith
    have hMprod : (M1 : ℝ) * (M2 : ℝ) ^ 4 * (M3 : ℝ) ≤
        (M : ℝ) ^ 6 := by
      have hM0 : 0 ≤ (M : ℝ) := by positivity
      calc
        (M1 : ℝ) * (M2 : ℝ) ^ 4 * (M3 : ℝ) ≤
            (M : ℝ) * (M2 : ℝ) ^ 4 * (M3 : ℝ) := by
              simpa [mul_assoc] using
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hM1R (by positivity)) (by positivity))
        _ ≤ (M : ℝ) * (M : ℝ) ^ 4 * (M3 : ℝ) := by
          have h := mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hM2R 4) (by positivity : 0 ≤ (M : ℝ) * (M3 : ℝ))
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
        _ ≤ (M : ℝ) * (M : ℝ) ^ 4 * (M : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hM3R
            (by positivity : 0 ≤ (M : ℝ) * (M : ℝ) ^ 4)
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
        _ = (M : ℝ) ^ 6 := by ring
    have hM1posR : 0 < (M1 : ℝ) := by exact_mod_cast hM1pos
    have hM3posR : 0 < (M3 : ℝ) := by exact_mod_cast hM3pos
    have hL1sq : 0 ≤ L1 ^ 2 := sq_nonneg _
    calc
      _ = 2 * 7 ^ 6 * 2 ^ 2 * Real.rpow T eta *
          ((M1 : ℝ) * (M2 : ℝ) ^ 4 * (M3 : ℝ)) *
          L1 ^ 2 := by
        field_simp [ne_of_gt hM1posR, ne_of_gt hM3posR]
      _ ≤ 2 * 7 ^ 6 * 2 ^ 2 * Real.rpow T eta *
          (M : ℝ) ^ 6 *
          L1 ^ 2 := by
        have h' :
            (2 * 7 ^ 6 * 2 ^ 2 * Real.rpow T eta) *
                ((M1 : ℝ) * (M2 : ℝ) ^ 4 * (M3 : ℝ)) ≤
              (2 * 7 ^ 6 * 2 ^ 2 * Real.rpow T eta) * (M : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_left hMprod
            (mul_nonneg (by positivity) (Real.rpow_nonneg hT0 eta))
        have h'' := mul_le_mul_of_nonneg_right h' hL1sq
        simpa [mul_assoc, mul_left_comm, mul_comm] using h''
      _ ≤ 2 * 7 ^ 6 * 2 ^ 2 * Real.rpow T (3 * eta) *
          (M : ℝ) ^ 6 *
          L1 ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hpow
          (by positivity : 0 ≤ 2 * 7 ^ 6 * 2 ^ 2 * (M : ℝ) ^ 6 *
            L1 ^ 2)
        simpa [mul_assoc, mul_left_comm, mul_comm] using h
      _ = 941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 *
          L1 ^ 2 := by norm_num
  simpa [m1Range, m2Range, m3Range, sourceBumpEllRange] using hlow.trans hmain

theorem profile_lowFrequencyIntegral_le_l1
    {T eta S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hT : 1 ≤ T) (heta : 0 < eta)
    {M M1 M2 M3 : ℕ}
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM3 : 1 ≤ M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M) :
    (∫ xi in lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ)),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceBumpEllRange 1 (M3 : ℝ) 1)
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 *
        (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 := by
  let L1 : ℝ := ∫ u : ℝ, ‖(f u : ℂ)‖
  have hL1 : 0 ≤ L1 := by
    dsimp [L1]
    positivity
  have hbound : ∀ z : ℝ,
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤ L1 := by
    intro z
    dsimp [L1]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) z
  simpa [L1] using profile_lowFrequencyIntegral_le hf L1 hL1 hbound
    hT heta hM1 hM2 hM3 hM1M hM2M hM3M

theorem profile_highFrequencyIntegral_le_time_neg100
    (Cdec : ℝ) (hCdec : 0 ≤ Cdec)
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hdecayProfile : ∀ {z : ℝ}, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Cdec * T ^ (1 : ℝ) * (T / |z|) ^ (83 : ℕ) * S)
    (hT : 1 ≤ T) (hSgrowth : S ≤ T ^ (4 : ℝ))
    {M M1 M2 M3 : ℕ}
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M)
    (hMT : (M : ℝ) ≤ T) :
    (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceBumpEllRange 1 (M3 : ℝ) 1)
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      (((686 * Cdec) * 2 ^ 83 * 2 ^ 83) ^ 2 * quarticDecayMass) /
        T ^ 100 := by
  have hS0 : 0 ≤ S := hf.bound_nonneg
  have hSgrowthNat : S ≤ T ^ (4 : ℕ) := by
    simpa [Real.rpow_natCast] using hSgrowth
  have hbudget := ownnewLemma92RegionHigh_growth_budget 4
    Cdec hCdec hT hS0 hSgrowthNat
    hM1 hM2 hM3 hM1M hM2M hM3M hMT
  have hM1Mreal : (M1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1M
  have hM2Mreal : (M2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2M
  have hM3Mreal : (M3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3M
  have hM1T : (M1 : ℝ) ≤ T := hM1Mreal.trans hMT
  have hM2T : (M2 : ℝ) ≤ T := hM2Mreal.trans hMT
  have hM3T : (M3 : ℝ) ≤ T := hM3Mreal.trans hMT
  let m1Range := sourceSignedDyadicRange M1
  let m2Range := sourcePositiveDyadicRange M2
  let m3Range := sourceIntegerWindow 0 (2 * (M3 : ℝ))
  have hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0 := by
    intro m1 hm
    exact sourceSignedDyadicRange_ne_zero hM1 hm
  have hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0 := by
    intro m2 hm
    exact sourcePositiveDyadicRange_ne_zero hM2 hm
  have hpsi : ∀ m3 ∈ m3Range,
      ‖(sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) : ℂ)‖ ≤ 1 := by
    intro m3 hm
    exact norm_sourceBump_unit_le_one _
  have hRlo : 0 < (M2 : ℝ) / (2 * (M1 : ℝ)) := by positivity
  have hRhi : 0 ≤ 2 * T := by positivity
  have hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      (M2 : ℝ) / (2 * (M1 : ℝ)) ≤ |((m2 : ℝ) / (m1 : ℝ))| := by
    intro m1 hm1' m2 hm2'
    exact (sourceDyadic_ratio_bounds hM1 hM2 hm1' hm2').1
  have hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ 2 * T := by
    intro m1 hm1' m2 hm2'
    exact sourceDyadic_ratio_upper_le_two_mul_time hM1 hM2 hM2T hm1' hm2'
  have hcard1 : (m1Range.card : ℝ) ≤ 7 * T := by
    dsimp [m1Range]
    exact card_sourceSignedDyadicRange_cast_le_seven_mul_time hT hM1T
  have hcard2 : (m2Range.card : ℝ) ≤ 7 * T := by
    dsimp [m2Range]
    exact card_sourcePositiveDyadicRange_cast_le_seven_mul_time hT hM2T
  have hcard3 : (m3Range.card : ℝ) ≤ 7 * T := by
    dsimp [m3Range]
    have hc := card_centeredTwoScale_cast_le M3
    nlinarith
  have hghat : IntegrableOn
      (fun xi => ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2)
      (highFrequencyRegion (sourceHighFrequencyCutoff T)) := by
    have hglobal := integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
      m1Range m2Range m3Range
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      (fReal := f) (T := T)
      (S := S) (F := F) (M3 := (M3 : ℝ))
      (N1 := (m1Range.card : ℝ)) (N2 := (m2Range.card : ℝ))
      (N3 := (m3Range.card : ℝ))
      (P1 := 1) (Rhi := 2 * T)
      hf (eta := (1 : ℝ)) (heta := by norm_num)
        (hT := le_trans zero_le_one hT) (hRlo := hRlo)
      (hN1 := by positivity) (hN2 := by positivity) (hN3 := by positivity)
      (hP1 := by positivity) (hRhi := hRhi)
      (hcard1 := by exact le_rfl) (hcard2 := by exact le_rfl)
      (hcard3 := by exact le_rfl)
      (hm1 := hm1) (hm2 := hm2) (hpsi := hpsi)
      (hratioLo := hratioLo) (hratioHi := hratioHi)
    exact hglobal.integrableOn
  have hbound : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier
        (fun u : ℝ => (f u : ℂ))
        ((m2 / m1) * xi)‖ ≤
      Cdec * T ^ (1 : ℝ) *
        (T / (|m2 / m1| * |xi|)) ^ (81 + 2 : ℕ) *
          S := by
    intro m1 m2 xi hm1R hm2R hxi
    have hz : (m2 / m1) * xi ≠ 0 :=
      mul_ne_zero (div_ne_zero hm2R hm1R) hxi
    simpa only [abs_mul] using hdecayProfile hz
  have hhigh := sourceGFinite_highFrequencyIntegral_le_time_neg100
    m1Range m2Range m3Range
    (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    (fun u : ℝ => (f u : ℂ)) hf.integrable.ofReal (M3 : ℝ) 81
    (T := T) (S := S) (eta := (1 : ℝ))
    (Cdec := Cdec)
    (Rlo := (M2 : ℝ) / (2 * M1 : ℝ))
    (N1 := (m1Range.card : ℝ)) (N2 := (m2Range.card : ℝ))
    (N3 := (m3Range.card : ℝ))
    (P1 := (1 : ℝ)) (Rhi := 2 * T)
    (CIII := ((686 * Cdec) * 2 ^ 83 * 2 ^ 83) ^ 2 * quarticDecayMass)
    hT hf.bound_nonneg hCdec hRlo (by positivity) (by positivity) (by positivity)
    (by norm_num) (by positivity)
    (by exact le_rfl) (by exact le_rfl) (by exact le_rfl)
    hm1 hm2 hpsi hratioLo hratioHi hbound hghat
    (by simpa [Nat.add_assoc, mul_assoc] using hbudget)
  simpa [m1Range, m2Range, m3Range, sourceBumpEllRange] using hhigh


#print axioms GuthMaynardS3WideExtremesGeneric.profile_lowFrequencyIntegral_le
#print axioms GuthMaynardS3WideExtremesGeneric.profile_lowFrequencyIntegral_le_l1
#print axioms GuthMaynardS3WideExtremesGeneric.profile_highFrequencyIntegral_le_time_neg100

end GuthMaynardS3WideExtremesGeneric
