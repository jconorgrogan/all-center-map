import GuthMaynardJIterationMediumRegionTailInsertion

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The actual low-frequency first-Poisson bound with its discarded tail.
Unlike the earlier finite-outer API, this theorem does not assume that the
infinite Poisson series is exactly finite: compact support selects `m3`, while
Fourier decay truncates `ell` with the explicit `T^-100` remainder. -/
theorem sourceGFinite_lowFrequencyIntegral_le_localized_add_firstPoissonTail
    (m1Range ellRange m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f)
    (q : ℕ) (hcompact : HasCompactSupport psi1)
    (hsmooth : ContDiff ℝ ∞ psi1)
    (T eta M1 : ℝ)
    {K0 K Kpsi M3 B Y C P N1 Hinner : ℝ}
    (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hK : 0 ≤ K) (hKpsi : 0 ≤ Kpsi) (hC : 0 ≤ C)
    (hP : 0 ≤ P) (hN1 : 0 ≤ N1) (hHinner : 0 ≤ Hinner)
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T eta M1 M3)
    (hbounded : ∀ z, ‖FourierTransform.fourier psi1 z‖ ≤ Kpsi)
    (hdecay2 : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hdecay : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤
        K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hpairCard : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3),
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤ P)
    (hcover : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3),
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange)
    (hxi : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3),
      ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y)
    (hinner : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3),
      ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier f) m1 xi‖ ≤ Hinner)
    (hfullInt : IntegrableOn (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2)
      (lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3)))
    (hlocalizedInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier psi1) (FourierTransform.fourier f)
        M3 B xi‖ ^ 2)
      (lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3))) :
    (∫ xi in lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3),
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) ≤
      4 * sourceLowFrequencyCutoff T eta M1 M3 *
        (P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2) +
      4 * sourceLowFrequencyCutoff T eta M1 M3 *
        ((C / T ^ 100) * (N1 * Hinner)) ^ 2 := by
  let S := lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3)
  let g : ℝ → ℂ := FourierTransform.fourier
    (sourceGFinite m1Range m2Range m3Range psi1 f M3)
  let retained : ℝ → ℂ := fun xi =>
    sourceFirstPoissonRetainedFinite m1Range m2Range
      (FourierTransform.fourier psi1) (FourierTransform.fourier f) M3 B xi
  let localized : ℝ → ℂ := fun xi =>
    sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
      (FourierTransform.fourier psi1) (FourierTransform.fourier f) M3 B xi
  let E : ℝ := (C / T ^ 100) * (N1 * Hinner)
  have hS : MeasurableSet S := measurableSet_lowFrequencyRegion _
  have hSfinite : volume S ≠ (⊤ : ENNReal) := by
    dsimp only [S, lowFrequencyRegion]
    rw [show {xi : ℝ | |xi| ≤ sourceLowFrequencyCutoff T eta M1 M3} =
        Set.Icc (-sourceLowFrequencyCutoff T eta M1 M3)
          (sourceLowFrequencyCutoff T eta M1 M3) by
      ext xi
      simp [abs_le]]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hretEq : Set.EqOn retained localized S := by
    intro xi hxiS
    exact sourceFirstPoissonRetainedFinite_eq_localizedPairSum
      m1Range ellRange m2Range (FourierTransform.fourier psi1)
      (FourierTransform.fourier f) hM3 hm1 xi (hcover xi hxiS)
  have hretInt : IntegrableOn (fun xi => ‖retained xi‖ ^ 2) S := by
    apply hlocalizedInt.congr_fun _ hS
    intro xi hxiS
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hretEq hxiS).symm
  have htail : ∀ xi ∈ S, ‖g xi - retained xi‖ ≤ E := by
    intro xi hxiS
    have hraw := norm_fourier_sourceGFinite_sub_retained_le_time_neg100
      m1Range m2Range m3Range psi1 f hf q hcompact hsmooth hK hM3 hB hY
      hT hdecay2 hdecay hbudget hm1 hm2 hsupport xi (hxi xi hxiS)
    have hsum : (∑ m1 ∈ m1Range,
        ‖sourceCorrectedM2FourierInner m2Range
          (FourierTransform.fourier f) m1 xi‖) ≤ N1 * Hinner := by
      calc
        (∑ m1 ∈ m1Range,
          ‖sourceCorrectedM2FourierInner m2Range
            (FourierTransform.fourier f) m1 xi‖) ≤
            ∑ _m1 ∈ m1Range, Hinner := by
              apply Finset.sum_le_sum
              intro m1 hm1mem
              exact hinner xi hxiS m1 hm1mem
        _ = (m1Range.card : ℝ) * Hinner := by simp
        _ ≤ N1 * Hinner := mul_le_mul_of_nonneg_right hcard1 hHinner
    calc
      ‖g xi - retained xi‖ ≤
          (C / T ^ 100) * ∑ m1 ∈ m1Range,
            ‖sourceCorrectedM2FourierInner m2Range
              (FourierTransform.fourier f) m1 xi‖ := by
        simpa only [g, retained] using hraw
      _ ≤ E := mul_le_mul_of_nonneg_left hsum
        (div_nonneg hC (pow_pos hT _).le)
  have hlocPoint : ∀ xi ∈ S, ‖localized xi‖ ^ 2 ≤
      P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2 := by
    intro xi hxiS
    have hraw := norm_sourceFirstPoissonLocalizedPairSum_sq_le
      m1Range ellRange m2Range (FourierTransform.fourier psi1)
      (FourierTransform.fourier f) (B := B) hM3.le hKpsi hbounded xi
    let pairs := sourceMediumLocalizedPairs m1Range ellRange M3 B xi
    have hsum : (∑ p ∈ pairs,
        (M3 * Kpsi) ^ 2 *
          ‖sourceCorrectedM2FourierInner m2Range
            (FourierTransform.fourier f) p.1 xi‖ ^ 2) ≤
        P * ((M3 * Kpsi) ^ 2 * Hinner ^ 2) := by
      calc
        (∑ p ∈ pairs, (M3 * Kpsi) ^ 2 *
            ‖sourceCorrectedM2FourierInner m2Range
              (FourierTransform.fourier f) p.1 xi‖ ^ 2) ≤
            ∑ _p ∈ pairs, (M3 * Kpsi) ^ 2 * Hinner ^ 2 := by
              apply Finset.sum_le_sum
              intro p hp
              apply mul_le_mul_of_nonneg_left
              · exact pow_le_pow_left₀ (norm_nonneg _)
                  (hinner xi hxiS p.1
                    ((mem_sourceMediumLocalizedPairs_iff.mp hp).1)) 2
              · positivity
        _ = (pairs.card : ℝ) * ((M3 * Kpsi) ^ 2 * Hinner ^ 2) := by simp
        _ ≤ P * ((M3 * Kpsi) ^ 2 * Hinner ^ 2) :=
          mul_le_mul_of_nonneg_right (hpairCard xi hxiS) (by positivity)
    calc
      ‖localized xi‖ ^ 2 ≤ (pairs.card : ℝ) *
          ∑ p ∈ pairs, (M3 * Kpsi) ^ 2 *
            ‖sourceCorrectedM2FourierInner m2Range
              (FourierTransform.fourier f) p.1 xi‖ ^ 2 := by
        simpa only [localized, pairs] using hraw
      _ ≤ P * (P * ((M3 * Kpsi) ^ 2 * Hinner ^ 2)) := by
        exact mul_le_mul (hpairCard xi hxiS) hsum (by positivity) hP
      _ = P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2 := by ring
  have hlocIntegral : (∫ xi in S, ‖localized xi‖ ^ 2) ≤
      2 * sourceLowFrequencyCutoff T eta M1 M3 *
        (P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2) := by
    exact sourceLowFrequencyIntegral_le localized hcut0 hlocalizedInt hlocPoint
  have happrox := setIntegral_norm_sq_le_of_uniform_approximation
    g retained S hS hfullInt hretInt hSfinite htail
  have hvol : volume.real S =
      2 * sourceLowFrequencyCutoff T eta M1 M3 := by
    dsimp only [S, lowFrequencyRegion]
    rw [show {xi : ℝ | |xi| ≤ sourceLowFrequencyCutoff T eta M1 M3} =
        Set.Icc (-sourceLowFrequencyCutoff T eta M1 M3)
          (sourceLowFrequencyCutoff T eta M1 M3) by
      ext xi
      simp [abs_le]]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
        2 * (∫ xi in S, ‖retained xi‖ ^ 2) + 2 * volume.real S * E ^ 2 :=
      happrox
    _ = 2 * (∫ xi in S, ‖localized xi‖ ^ 2) + 2 * volume.real S * E ^ 2 := by
      congr 2
      apply setIntegral_congr_fun hS
      intro xi hxiS
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hretEq hxiS)
    _ ≤ 2 * (2 * sourceLowFrequencyCutoff T eta M1 M3 *
          (P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2)) +
        2 * volume.real S * E ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlocIntegral (by norm_num)) le_rfl
    _ = _ := by rw [hvol]; dsimp only [E]; ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceGFinite_lowFrequencyIntegral_le_localized_add_firstPoissonTail
