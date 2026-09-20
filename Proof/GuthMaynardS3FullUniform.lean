import GuthMaynardS3GenericUniformMedium
import GuthMaynardS3WideExtremesGeneric

set_option maxHeartbeats 4000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3FullUniform

open GuthMaynardJIteration
open GuthMaynardS3GenericUniformMedium
open GuthMaynardS3WideExtremesGeneric

/-- Full source-frequency weld.  The medium estimate is supplied by the
generic uniform theorem, while the low and high estimates are constructed
inside this theorem from the literal Fourier data. -/
theorem source_fullFrequencyIntegral_uniform
    (Cdec : ℕ → ℝ) (hCdec_nonneg : ∀ q, 0 ≤ Cdec q)
    {eta delta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) :
    ∃ Cfinal : ℝ, 0 < Cfinal ∧
      ∀ (T S F : ℝ) (f : ℝ → ℝ) (M M1 M2 M3 : ℕ)
        (hT7 : (7 : ℝ) ≤ T) (hT : 1 ≤ T)
        (hF0 : 0 ≤ F) (hFT : F ≤ T) (hF8 : F ≤ 8)
        (hS0 : 0 ≤ S) (hSgrowth : S ≤ T ^ (4 : ℝ))
        (hM : 1 ≤ M) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM3 : 1 ≤ M3)
        (hM1M : (M1 : ℝ) ≤ M) (hM2M : (M2 : ℝ) ≤ M)
        (hM3M : (M3 : ℝ) ≤ M) (hMT : (M : ℝ) ≤ T)
        (hM2M3 : M2 ≤ M3) (hM3hi : (M3 : ℝ) ≤ 16 * (M2 : ℝ))
        (hf : SourceAdmissibleProfile T S F f)
        (hdecay : ∀ q : ℕ, ∀ z : ℝ, z ≠ 0 →
          ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
            Cdec q * T ^ eta * (T / |z|) ^ q * S),
        (∫ xi : ℝ,
          ‖FourierTransform.fourier
            (sourceGFinite (sourceSignedDyadicRange M1)
              (sourcePositiveDyadicRange M2)
              (sourceBumpEllRange 1 (M3 : ℝ) 1)
              (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
              (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
        Cfinal *
          (Real.rpow T (3 * eta) * (M : ℝ) ^ 6 *
              (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 +
            Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
              Real.sqrt ((∫ u : ℝ, f u ^ 2) *
                sourceAffineJ
                  (sourceAffineConfigs (sourcePositiveDyadicRange M2)
                    (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
                  (affineSmoothing T
                    (sourceBumpNormalized (Real.rpow T delta)
                      (Real.rpow_pos_of_pos (by linarith [hT7]) delta)) f))) +
          Cfinal / T ^ 100 := by
  obtain ⟨Cmed, hCmed, hmediumUniform⟩ :=
    generic_medium_uniform Cdec hCdec_nonneg heta heta1 hdelta
  let H : ℝ := (((686 * Cdec 83) * 2 ^ 83 * 2 ^ 83) ^ 2 * quarticDecayMass)
  let Cfinal : ℝ := 941192 + Cmed + H + 1
  have hH : 0 ≤ H := by
    dsimp [H]
    have hmass0 : 0 ≤ quarticDecayMass := by
      unfold quarticDecayMass
      exact integral_nonneg (fun xi => by
        unfold quarticDecayEnvelope
        positivity)
    positivity
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    linarith
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro T S F f M M1 M2 M3 hT7 hT hF0 hFT hF8 hS0 hSgrowth
    hM hM1 hM2 hM3 hM1M hM2M hM3M hMT hM2M3 hM3hi hf hdecay
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM1T : (M1 : ℝ) ≤ T := hM1M.trans hMT
  have hM3T : (M3 : ℝ) ≤ T := hM3M.trans hMT
  have hM1pos : 0 < M1 := lt_of_lt_of_le Nat.zero_lt_one hM1
  have hM2pos : 0 < M2 := lt_of_lt_of_le Nat.zero_lt_one hM2
  have hM3pos : 0 < M3 := lt_of_lt_of_le Nat.zero_lt_one hM3
  have hcut : sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ) ≤
      sourceHighFrequencyCutoff T := by
    unfold sourceLowFrequencyCutoff sourceHighFrequencyCutoff
    have hpow : Real.rpow T eta ≤ T := by
      calc
        Real.rpow T eta ≤ Real.rpow T (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT heta1
        _ = T := Real.rpow_one T
    have hratio : (M1 : ℝ) / (M3 : ℝ) ≤ T := by
      apply (div_le_iff₀ (by exact_mod_cast hM3pos)).2
      have hM3one : (1 : ℝ) ≤ M3 := by exact_mod_cast hM3
      calc
        (M1 : ℝ) ≤ T := hM1T
        _ ≤ T * (M3 : ℝ) := by nlinarith
    have hprod : Real.rpow T eta * ((M1 : ℝ) / (M3 : ℝ)) ≤ T * T := by
      exact mul_le_mul hpow hratio (by positivity) (by positivity)
    have hT2 : T * T ≤ T ^ (6 : ℕ) := by
      calc
        T * T = T ^ (2 : ℕ) := by ring
        _ ≤ T ^ (6 : ℕ) := pow_le_pow_right₀ hT (by omega)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprod.trans hT2
  let L1 : ℝ := ∫ u : ℝ, ‖(f u : ℂ)‖
  have hL1 : 0 ≤ L1 := by
    dsimp [L1]
    positivity
  have hL1bound : ∀ z : ℝ,
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤ L1 := by
    intro z
    dsimp [L1]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) z
  let F2 : ℝ := ∫ u : ℝ, f u ^ 2
  let J : ℝ := sourceAffineJ
      (sourceAffineConfigs (sourcePositiveDyadicRange M2)
        (sourceLemma92JRange M2 T F (2 * Real.rpow T delta)))
      (affineSmoothing T (sourceBumpNormalized (Real.rpow T delta)
        (Real.rpow_pos_of_pos hTpos delta)) f)
  have hF2 : 0 ≤ F2 := by
    dsimp [F2]
    positivity
  let m1Range := sourceSignedDyadicRange M1
  let m2Range := sourcePositiveDyadicRange M2
  let m3Range := sourceBumpEllRange 1 (M3 : ℝ) 1
  have hN1 : (m1Range.card : ℝ) ≤ 7 * (M : ℝ) := by
    dsimp [m1Range]
    have hc := card_sourceSignedDyadicRange_cast_le M1
    nlinarith [show (1 : ℝ) ≤ (M1 : ℝ) by exact_mod_cast hM1]
  have hN2 : (m2Range.card : ℝ) ≤ 7 * (M : ℝ) := by
    dsimp [m2Range]
    have hc := card_sourcePositiveDyadicRange_cast_le M2
    nlinarith [show (1 : ℝ) ≤ (M2 : ℝ) by exact_mod_cast hM2]
  have hN3 : (m3Range.card : ℝ) ≤ 7 * (M : ℝ) := by
    have heq : m3Range = sourceIntegerWindow 0 (2 * (M3 : ℝ)) := by
      ext m3
      simp [m3Range, sourceBumpEllRange]
    rw [heq]
    have hc := card_sourceIntegerWindow_cast_le 0 (2 * (M3 : ℝ))
      (by positivity : (0 : ℝ) ≤ 2 * (M3 : ℝ))
    nlinarith [show (1 : ℝ) ≤ (M3 : ℝ) by exact_mod_cast hM3]
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
  have hghat : Integrable (fun xi : ℝ =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) := by
    exact integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
      m1Range m2Range m3Range
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      (fReal := f) (T := T) (S := S) (F := F) (M3 := (M3 : ℝ))
      (N1 := 7 * (M : ℝ)) (N2 := 7 * (M : ℝ)) (N3 := 7 * (M : ℝ))
      (P1 := 1) (Rhi := (2 * (M2 : ℝ)) / (M1 : ℝ)) hf
      (eta := (1 : ℝ)) (heta := by norm_num)
      (hT := le_trans zero_le_one hT) (hRlo := hRlo)
      (hN1 := by positivity) (hN2 := by positivity) (hN3 := by positivity)
      (hP1 := by positivity) (hRhi := hRhi)
      (hcard1 := hN1) (hcard2 := hN2) (hcard3 := hN3)
      (hm1 := hm1) (hm2 := hm2) (hpsi := hpsi)
      (hratioLo := hratioLo) (hratioHi := hratioHi)
  have hdecayThreshold : ∀ q : ℕ, (300 : ℝ) ≤ eta * q → ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Cdec q * T ^ eta * (T / |z|) ^ q * S := by
    intro q hq z hz
    exact hdecay q z hz
  have hmedium := hmediumUniform T S F f M M1 M2 M3 hT7 hT hF0 hFT hF8
      hS0 hSgrowth (by exact_mod_cast hM) hM1 hM2 hM3 hM1M hM2M hM3M hMT
      hM2M3 hM3hi hf hdecayThreshold
  have hdecay83 : ∀ {z : ℝ}, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Cdec 83 * T ^ (1 : ℝ) * (T / |z|) ^ (83 : ℕ) * S := by
    intro z hz
    have hh := hdecay 83 z hz
    have hT0 : 0 ≤ T := le_trans zero_le_one hT
    have hpow : Real.rpow T eta ≤ T := by
      calc
        Real.rpow T eta ≤ Real.rpow T (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT heta1
        _ = T := Real.rpow_one T
    have hfac : 0 ≤ Cdec 83 * (T / |z|) ^ (83 : ℕ) * S := by
      exact mul_nonneg
        (mul_nonneg (hCdec_nonneg 83)
          (pow_nonneg (div_nonneg hT0 (abs_nonneg z)) 83)) hS0
    calc
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
          Cdec 83 * T ^ eta * (T / |z|) ^ (83 : ℕ) * S := hh
      _ ≤ Cdec 83 * T ^ (1 : ℝ) * (T / |z|) ^ (83 : ℕ) * S := by
        have hx := mul_le_mul_of_nonneg_right hpow hfac
        calc
          Cdec 83 * T ^ eta * (T / |z|) ^ (83 : ℕ) * S =
              T ^ eta * (Cdec 83 * (T / |z|) ^ (83 : ℕ) * S) := by ring
          _ ≤ T * (Cdec 83 * (T / |z|) ^ (83 : ℕ) * S) := hx
          _ = Cdec 83 * T ^ (1 : ℝ) * (T / |z|) ^ (83 : ℕ) * S := by
            norm_num [Real.rpow_one]
            ring
  have hhigh := profile_highFrequencyIntegral_le_time_neg100
    (Cdec 83) (hCdec_nonneg 83) hf hdecay83 hT hSgrowth
    (M := M) (M1 := M1) (M2 := M2) (M3 := M3)
    (by exact_mod_cast hM1) (by exact_mod_cast hM2) (by exact_mod_cast hM3)
    (by exact_mod_cast hM1M) (by exact_mod_cast hM2M) (by exact_mod_cast hM3M) hMT
  have hlow := profile_lowFrequencyIntegral_le hf L1 hL1 hL1bound hT heta
    (by exact_mod_cast hM1) (by exact_mod_cast hM2) (by exact_mod_cast hM3)
    (by exact_mod_cast hM1M) (by exact_mod_cast hM2M) (by exact_mod_cast hM3M)
  have hassembled := sourceFrequencyIntegral_le_of_region_bounds
    (FourierTransform.fourier
      (sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceBumpEllRange 1 (M3 : ℝ) 1)
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun u : ℝ => (f u : ℂ)) (M3 : ℝ))) hghat T eta (M1 : ℝ) (M3 : ℝ)
    (941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2)
    (Cmed * (Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 +
      Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 * Real.sqrt (F2 * J)) +
      Cmed / T ^ 100) (H / T ^ 100) hcut hlow hmedium hhigh
  let AB : ℝ := Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 +
      Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 * Real.sqrt (F2 * J)
  have hAB : 0 ≤ AB := by
    have h1 : 0 ≤ Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one hT) _)
          (pow_nonneg (by positivity) 6)) (sq_nonneg _)
    have h2 : 0 ≤ Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
        Real.sqrt (F2 * J) := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one hT) _)
          (sq_nonneg _)) (Real.sqrt_nonneg _)
    dsimp [AB]
    exact add_nonneg h1 h2
  have hcoef : 0 ≤ 941192 + Cmed := by linarith
  have hcoef' : 941192 + Cmed ≤ Cfinal := by
    dsimp [Cfinal]
    linarith
  have htailcoef : Cmed + H ≤ Cfinal := by
    dsimp [Cfinal]
    linarith
  have hassembled' :
      (∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2)
            (sourceBumpEllRange 1 (M3 : ℝ) 1)
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      (941192 + Cmed) * AB + (Cmed + H) / T ^ 100 := by
    have hB : 0 ≤ Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
        Real.sqrt (F2 * J) := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one hT) _)
          (sq_nonneg _)) (Real.sqrt_nonneg _)
    calc
      _ ≤ 941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 +
          Cmed * AB + Cmed / T ^ 100 + H / T ^ 100 := by
            simpa [AB, add_assoc, add_left_comm, add_comm] using hassembled
      _ ≤ (941192 + Cmed) * AB + (Cmed + H) / T ^ 100 := by
        have hi : 0 ≤ (941192 : ℝ) *
            (Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
              Real.sqrt (F2 * J)) := by
          exact mul_nonneg (by norm_num) hB
        calc
          941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 +
                Cmed * AB + Cmed / T ^ 100 + H / T ^ 100 ≤
              941192 * Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 +
                Cmed * AB + Cmed / T ^ 100 + H / T ^ 100 +
                  941192 * (Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 *
                    Real.sqrt (F2 * J)) := le_add_of_nonneg_right hi
          _ = (941192 + Cmed) * AB + (Cmed + H) / T ^ 100 := by
            dsimp [AB]
            ring
  calc
    _ ≤ (941192 + Cmed) * AB + (Cmed + H) / T ^ 100 := hassembled'
    _ ≤ Cfinal *
          AB +
        Cfinal / T ^ 100 := by
      have hfirst := mul_le_mul_of_nonneg_right hcoef' hAB
      have hinv : 0 ≤ (T ^ 100)⁻¹ := by positivity
      have hsecond : (Cmed + H) / T ^ 100 ≤ Cfinal / T ^ 100 := by
        exact mul_le_mul_of_nonneg_right htailcoef hinv
      simpa [div_eq_mul_inv] using add_le_add hfirst hsecond
    _ = Cfinal *
          (Real.rpow T (3 * eta) * (M : ℝ) ^ 6 * L1 ^ 2 +
            Real.rpow T (4 * eta + delta) * (M : ℝ) ^ 2 * Real.sqrt (F2 * J)) +
        Cfinal / T ^ 100 := by rfl

end GuthMaynardS3FullUniform

#print axioms GuthMaynardS3FullUniform.source_fullFrequencyIntegral_uniform
