import GuthMaynardS3MediumNonzeroActual
import GuthMaynardS3ZeroEllProfile
import GuthMaynardJIterationFirstPoissonGhatLocalization
import GuthMaynardLocalizedPairIntegrability
import GuthMaynardLemma92EllWindowSupport

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3MediumFullActual

open GuthMaynardJIteration
open GuthMaynardS3ZeroEllSupport
open GuthMaynardS3MediumLiteralWeld
open GuthMaynardS3MediumNonzeroActual
open GuthMaynardS3LiteralLemma92NonzeroMedium
open GuthMaynardS3ZeroEllProfile

/-! Whole medium-region insertion with the literal signed mask.  The raw
source bump is used for the first-Poisson field; its Fourier field is the
`F` entering the zero/nonzero split.  The second-Poisson consumer is kept
for the next weld, so this theorem exposes the exact full `Sigma_II` term. -/
theorem sourceGFinite_mediumIntegral_le_Ceta_fullSigmaII_add_zero_tail
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M M1 M2 M3 : ℕ} (hM : 0 ≤ (M : ℝ))
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM3 : 1 ≤ M3)
    (hM1M : (M1 : ℝ) ≤ M) (hM2M : (M2 : ℝ) ≤ M)
    (hM3M : (M3 : ℝ) ≤ M)
    {eta Ceta Hinner Y C : ℝ} (hT : 1 ≤ T)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hM1T : (M1 : ℝ) ≤ T) (hM3T : (M3 : ℝ) ≤ T)
    (hCeta : 0 < Ceta) (hY : 0 ≤ Y)
    (hC : 0 ≤ C) (hHinner : 0 ≤ Hinner)
    (q : ℕ) (ellRange m3Range : Finset ℤ)
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
    (psi2 : ℝ → ℝ) (M2R : ℝ)
    (hpsi2nonneg : ∀ ell ∈ ellRange,
      0 ≤ psi2 (M2R * (ell : ℝ) / T))
    (hpsi2majorant : ∀ ell ∈ nonzeroEllRange ellRange,
      1 ≤ psi2 (M2R * (ell : ℝ) / T))
    (hfhat : Continuous (FourierTransform.fourier
      (fun u : ℝ => (f u : ℂ)))) :
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
          sigmaIIFinite ellRange (sourcePositiveDyadicRange M2) psi2
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            M2R T (M3 : ℝ) (Real.rpow T eta) +
      9216 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
          Real.rpow T eta * (M : ℝ) ^ 6 *
          (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 +
      2 * volume.real (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T)) *
        ((C / T ^ 100) * (4 * (M1 : ℝ) * Hinner)) ^ 2 := by
  let Smed : Set ℝ := mediumFrequencyRegion
    (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
    (sourceHighFrequencyCutoff T)
  let B : ℝ := Real.rpow T eta
  let m1Range : Finset ℤ := sourceSignedDyadicRange M1
  let m2Range : Finset ℤ := sourcePositiveDyadicRange M2
  let Funit : ℝ → ℂ := fun x : ℝ =>
    FourierTransform.fourier (fun y : ℝ => (sourceBump 1 zero_lt_one y : ℂ)) x
  let fhat : ℝ → ℂ := FourierTransform.fourier
    (fun u : ℝ => (f u : ℂ))
  let Sigma : ℝ := sigmaIIFinite ellRange m2Range psi2 fhat
    M2R T (M3 : ℝ) B
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM1pos : 0 < (M1 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hM2pos : 0 < (M2 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM2)
  have hM3pos : 0 < (M3 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM3)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact Real.rpow_pos_of_pos hTpos _
  have hB0 : 0 ≤ B := hBpos.le
  have hFcont : Continuous Funit := by
    dsimp only [Funit]
    exact (unit_bump_fourier_bound).2
  have hKdec : 0 ≤ sourceBumpFourierConstant 1 zero_lt_one (q + 2) :=
    sourceBumpFourierConstant_nonneg 1 zero_lt_one (q + 2)
  have hdecay2 : ∀ z, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) z‖ ≤
      sourceBumpFourierConstant 1 zero_lt_one 2 / (1 + |z|) ^ 2 := by
    intro z
    exact sourceBump_fourier_decay 1 zero_lt_one 2 z
  have hdecay : ∀ z, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) z‖ ≤
      sourceBumpFourierConstant 1 zero_lt_one (q + 2) /
        (1 + |z|) ^ (q + 2) := by
    intro z
    exact sourceBump_fourier_decay 1 zero_lt_one (q + 2) z
  have hfhat' : Continuous fhat := by
    exact hfhat
  have hpairInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        Funit fhat (M3 : ℝ) B xi‖ ^ 2) Smed := by
    have h := integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
      m1Range ellRange m2Range Funit fhat hFcont hfhat' hM3pos hB0
    exact h.integrableOn
  have hzeroEq : (fun xi =>
        sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi) =
        (fun xi => sourceFirstPoissonLocalizedPairSum m1Range
          (ellRange.filter (fun e : ℤ => e = 0)) m2Range Funit fhat
            (M3 : ℝ) B xi) := by
      funext xi
      unfold sourceMediumZeroEllSum sourceFirstPoissonLocalizedPairSum
        sourceMediumLocalizedPairs
      have hprod : m1Range ×ˢ (ellRange.filter (fun e : ℤ => e = 0)) =
          (m1Range ×ˢ ellRange).filter (fun p : ℤ × ℤ => p.2 = 0) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨hp1, ⟨hp2, hpzero⟩⟩
          exact ⟨⟨hp1, hp2⟩, hpzero⟩
        · rintro ⟨⟨hp1, hp2⟩, hpzero⟩
          exact ⟨hp1, ⟨hp2, hpzero⟩⟩
      rw [hprod]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hlocal : |xi - (p.1 : ℝ) * (p.2 : ℝ)| <
          |(p.1 : ℝ)| / (M3 : ℝ) * B <;>
        by_cases hzero : p.2 = 0 <;>
        simp [hlocal, hzero]
  have hzeroGlobal : Integrable (fun xi =>
        ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi‖ ^ 2) := by
    have h := integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
      m1Range (ellRange.filter (fun e : ℤ => e = 0)) m2Range
      Funit fhat hFcont hfhat' hM3pos hB0
    rw [show (fun xi =>
          ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
            (M3 : ℝ) B xi‖ ^ 2) =
          (fun xi => ‖sourceFirstPoissonLocalizedPairSum m1Range
            (ellRange.filter (fun e : ℤ => e = 0)) m2Range Funit fhat
              (M3 : ℝ) B xi‖ ^ 2) by
          funext xi; rw [congrFun hzeroEq xi]]
    exact h
  have hzeroInt : IntegrableOn (fun xi =>
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
        (M3 : ℝ) B xi‖ ^ 2) Smed := hzeroGlobal.integrableOn
  have hnonzeroInt : IntegrableOn (fun xi =>
      ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range Funit fhat
        (M3 : ℝ) B xi‖ ^ 2) Smed := by
    have h := integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
      m1Range (nonzeroEllRange ellRange) m2Range Funit fhat
      hFcont hfhat' hM3pos hB0
    have heq := sourceMediumNonzeroEllSum_eq_nonzeroRange_sum
      m1Range ellRange m2Range Funit fhat (M3 : ℝ) B
    rw [show (fun xi =>
        ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi‖ ^ 2) =
        (fun xi => ‖sourceFirstPoissonLocalizedPairSum m1Range
          (nonzeroEllRange ellRange) m2Range Funit fhat
            (M3 : ℝ) B xi‖ ^ 2) by
          funext xi; rw [heq]]
    exact h.integrableOn
  have hzeroWhole := actualZeroEllProfile hf (M3 := (M3 : ℝ)) (B := B)
    ellRange hM hM1 hM2 hM3pos hM1M hM2M hM3M hB0
  have hzeroBound : (∫ xi in Smed,
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
        (M3 : ℝ) B xi‖ ^ 2) ≤
      2304 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 * B *
        (M : ℝ) ^ 6 * (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 := by
    have hnonneg : ∀ xi, 0 ≤
        ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi‖ ^ 2 := fun xi => sq_nonneg _
    have hle := setIntegral_le_integral (s := Smed) hzeroGlobal
      (Filter.Eventually.of_forall hnonneg)
    calc
      (∫ xi in Smed, ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi‖ ^ 2) ≤
        ∫ xi : ℝ, ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi‖ ^ 2 := hle
      _ ≤ _ := by simpa only [m1Range, m2Range, Funit, fhat, B] using hzeroWhole
  have hpairEq : ∀ xi ∈ Smed,
      sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi =
        sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat (M3 : ℝ) B xi +
          sourceMediumNonzeroEllSum m1Range ellRange m2Range Funit fhat (M3 : ℝ) B xi := by
    intro xi _
    exact sourceFirstPoissonLocalizedPairSum_eq_zeroEll_add_nonzeroEll
      m1Range ellRange m2Range Funit fhat (M3 : ℝ) B xi
  have hsourceApprox :
      (∫ xi in Smed,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤
      2 * (∫ xi in Smed,
        ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range Funit fhat
          (M3 : ℝ) B xi‖ ^ 2) +
      2 * volume.real Smed * ((C / T ^ 100) * (4 * (M1 : ℝ) * Hinner)) ^ 2 := by
    exact setIntegral_norm_sq_le_of_uniform_approximation _ _ Smed
      (measurableSet_mediumFrequencyRegion _ _) hfullInt hpairInt
      (volume_mediumFrequencyRegion_ne_top (a := sourceLowFrequencyCutoff T eta
        (M1 : ℝ) (M3 : ℝ)) (b := sourceHighFrequencyCutoff T)) (by
        intro xi hxiS
        have hm1 : ∀ m1' ∈ m1Range, m1' ≠ 0 := by
          intro m1' hm1'mem
          exact sourceSignedDyadicRange_ne_zero
            (lt_of_lt_of_le Nat.zero_lt_one hM1) hm1'mem
        have hraw := norm_fourier_sourceGFinite_sub_retained_le_time_neg100
          m1Range m2Range m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (f x : ℂ)) (hf.integrable.ofReal) q
          (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
          (sourceBump_complex_contDiff 1 zero_lt_one) hKdec hM3pos hBpos hY hTpos
          hdecay2 hdecay (by simpa only [B] using hbudget) hm1
          (fun m2 hm2mem => ne_of_gt (sourcePositiveDyadicRange_pos hM2 hm2mem))
          hsupport
          xi (hxi xi hxiS)
        have hretEq := sourceFirstPoissonRetainedFinite_eq_localizedPairSum
          m1Range ellRange m2Range Funit fhat hM3pos hm1 xi
          (hcover xi hxiS)
        have hsum : (∑ m1' ∈ m1Range,
            ‖sourceCorrectedM2FourierInner m2Range fhat m1' xi‖) ≤
            (4 * (M1 : ℝ)) * Hinner := by
          calc
            _ ≤ ∑ _m1' ∈ m1Range, Hinner := by
              apply Finset.sum_le_sum
              intro m1' hm1'mem
              exact hinner xi hxiS m1' hm1'mem
            _ = (m1Range.card : ℝ) * Hinner := by simp
            _ ≤ (4 * (M1 : ℝ)) * Hinner := by
              gcongr
              exact actual_card_sourceSignedDyadicRange_cast_le_four_mul hM1
        have hrawLocal :
            ‖FourierTransform.fourier (sourceGFinite m1Range m2Range m3Range
              (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
              (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi -
              sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
                Funit fhat (M3 : ℝ) B xi‖ ≤
            (C / T ^ 100) * ∑ m1' ∈ m1Range,
              ‖sourceCorrectedM2FourierInner m2Range fhat m1' xi‖ := by
            rw [← hretEq]
            exact hraw
        calc
          ‖FourierTransform.fourier (sourceGFinite m1Range m2Range m3Range
              (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
              (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi -
              sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
                Funit fhat (M3 : ℝ) B xi‖ ≤
            (C / T ^ 100) * ∑ m1' ∈ m1Range,
              ‖sourceCorrectedM2FourierInner m2Range fhat m1' xi‖ := hrawLocal
          _ ≤ (C / T ^ 100) * ((4 * (M1 : ℝ)) * Hinner) := by
            exact mul_le_mul_of_nonneg_left hsum
              (div_nonneg hC (pow_pos hTpos _).le)
      )
  have hFbound : ∀ z, ‖Funit z‖ ≤
      sourceBumpFourierConstant 1 zero_lt_one 0 :=
    (unit_bump_fourier_bound).1
  have hm2pos : ∀ m2' ∈ m2Range, 0 < m2' := by
    intro m2' hm2'mem
    exact sourcePositiveDyadicRange_pos hM2 hm2'mem
  have hnonzeroPairInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range
        (nonzeroEllRange ellRange) m2Range Funit fhat (M3 : ℝ) B xi‖ ^ 2) Smed := by
    have h := integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
      m1Range (nonzeroEllRange ellRange) m2Range Funit fhat
      hFcont hfhat' hM3pos hB0
    exact h.integrableOn
  have hnonzeroBound :=
    sourceMediumNonzeroEllSum_integral_le_Ceta_actual
      (T := T) (eta := eta) (M1 := M1) (M3 := M3)
      (Ceta := Ceta) (Kpsi := sourceBumpFourierConstant 1 zero_lt_one 0)
      hT heta heta1 hM1 hM3 hM1T hM3T hCeta
      (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0) hcount
      ellRange m2Range Funit fhat psi2 M2R hfhat' hFbound hm2pos
      hpsi2majorant hnonzeroPairInt
  have hSigmaFull0 : 0 ≤ Sigma := by
    dsimp only [Sigma]
    unfold sigmaIIFinite
    apply Finset.sum_nonneg
    intro ell hell
    exact mul_nonneg (hpsi2nonneg ell hell)
      (intervalIntegral.integral_nonneg (by linarith [hB0])
        (fun tau _ => sq_nonneg _))
  have hSigmaMon := sigmaIIFinite_nonzeroEllRange_le_full
    (ellRange := ellRange) (m2Range := m2Range)
    psi2 fhat M2R T (M3 : ℝ) B hB0 hpsi2nonneg
  let Nbound : ℝ :=
    4 * Ceta * Real.rpow T (2 * eta) *
      (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
      ((M1 : ℝ) + (M3 : ℝ)) * Sigma
  have hcoef0 : 0 ≤ 4 * Ceta * Real.rpow T (2 * eta) *
      (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
      ((M1 : ℝ) + (M3 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (Real.rpow_nonneg (le_trans zero_le_one hT) (2 * eta)))
        (sq_nonneg _))
      (by positivity)
  have hNbound : (∫ xi in Smed,
      ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range Funit fhat
        (M3 : ℝ) B xi‖ ^ 2) ≤ Nbound := by
    calc
      _ ≤ 4 * Ceta * Real.rpow T (2 * eta) *
          (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
          ((M1 : ℝ) + (M3 : ℝ)) *
          sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
            M2R T (M3 : ℝ) B := hnonzeroBound
      _ ≤ Nbound := by
        dsimp only [Nbound]
        exact mul_le_mul_of_nonneg_left hSigmaMon hcoef0
  have hNbound0 : 0 ≤ Nbound := by
    dsimp only [Nbound]
    exact mul_nonneg hcoef0 hSigmaFull0
  have hsplitBound := medium_integral_le_split_bounds
    Smed
    (FourierTransform.fourier
      (sourceGFinite m1Range m2Range m3Range
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)))
    (sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range Funit fhat
      (M3 : ℝ) B)
    (sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat (M3 : ℝ) B)
    (sourceMediumNonzeroEllSum m1Range ellRange m2Range Funit fhat (M3 : ℝ) B)
    (2 * volume.real Smed * ((C / T ^ 100) * (4 * (M1 : ℝ) * Hinner)) ^ 2)
    (2304 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 * B *
      (M : ℝ) ^ 6 * (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2)
    Nbound
    (measurableSet_mediumFrequencyRegion _ _)
    hfullInt hpairInt hzeroInt hnonzeroInt
    (fun xi hxiS => hpairEq xi hxiS)
    hsourceApprox hzeroBound hNbound (by positivity) hNbound0
  calc
    _ ≤ 4 * (2304 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 * B *
        (M : ℝ) ^ 6 * (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2) + 4 * Nbound +
        2 * volume.real Smed * ((C / T ^ 100) * (4 * (M1 : ℝ) * Hinner)) ^ 2 := by
      simpa [Nbound, add_assoc, add_comm, add_left_comm] using hsplitBound
    _ = _ := by
      dsimp only [Nbound, Smed, B, Sigma]
      ring

end GuthMaynardS3MediumFullActual
