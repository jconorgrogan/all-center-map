import GuthMaynardJIterationLowFrequencyTail
import GuthMaynardJIterationMediumRegionComplete
import GuthMaynardJIterationSourceHighFrequency

/-!
# Source-faithful low/medium/high frequency assembly

This is the corrected replacement for the earlier frequency-complete API.
The low-frequency branch is obtained from the first Poisson formula with its
discarded tail, rather than from a false exact equality with a finite outer
sum.  The same tail is retained independently in the medium branch, and the
high branch is derived from the literal rapid-decay estimate.
-/

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The low-frequency localized-pair count has the literal trivial product
bound.  This is often the correct source specialization: the `m1` range has
size `O(M1)` and the low-frequency `ell` window has size `O(T^eta)`. -/
theorem card_sourceMediumLocalizedPairs_le_rangeProduct
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) :
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card ≤
      m1Range.card * ellRange.card := by
  unfold sourceMediumLocalizedPairs
  simpa only [Finset.card_product] using
    Finset.card_filter_le (m1Range ×ˢ ellRange)
      (fun p : ℤ × ℤ =>
        |xi - (p.1 : ℝ) * (p.2 : ℝ)| < (|(p.1 : ℝ)| / M3) * B)

/-- Real-valued envelope form of the preceding exact finite bound. -/
theorem card_sourceMediumLocalizedPairs_cast_le_mul
    (m1Range ellRange : Finset ℤ) (M3 B xi N1 Nell : ℝ)
    (hN1 : (m1Range.card : ℝ) ≤ N1)
    (hNell : (ellRange.card : ℝ) ≤ Nell) :
    ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤
      N1 * Nell := by
  have hnat := card_sourceMediumLocalizedPairs_le_rangeProduct
    m1Range ellRange M3 B xi
  have hcast :
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤
        (m1Range.card : ℝ) * (ellRange.card : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (mul_le_mul hN1 hNell (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hN1))

/-- Assemble all three source frequency regions while retaining both copies
of the first-Poisson truncation error.  No regional integral estimate is an
input: region I comes from the localized finite pair sum, region II from the
corrected finite `SigmaII`, and region III from the source rapid-decay bound.

The remaining low-frequency inputs are geometric/cardinality and pointwise
envelopes for the literal localized sum.  In particular, there is no premise
identifying the full Poisson series with a finite outer sum. -/
theorem exists_sourceGFinite_frequencyIntegral_le_correctedSigmaII_v2
    (m1Range ellRange m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : ℝ → ℝ) (hf : Integrable f)
    (psi2 : ℝ → ℝ)
    (T etaFreq etaPair M1 M2 M3 B sigmaBound : ℝ)
    (qPoisson qHigh : ℕ)
    {K0 K Kpsi Y C P N1 Hinner c1 Lwindow : ℝ}
    (hpsi1compact : HasCompactSupport psi1)
    (hpsi1smooth : ContDiff ℝ ∞ psi1)
    (hM1 : 0 < M1) (hM3 : 0 < M3) (hB : 0 < B)
    (hY : 0 ≤ Y) (hK : 0 ≤ K) (hKpsi : 0 ≤ Kpsi)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hN1 : 0 ≤ N1)
    (hHinner : 0 ≤ Hinner) (hc1 : 0 ≤ c1)
    (hLwindow : 0 ≤ Lwindow) (hetaPair : 0 < etaPair)
    (hT : 1 ≤ T)
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T etaFreq M1 M3)
    (hcut : sourceLowFrequencyCutoff T etaFreq M1 M3 ≤
      sourceHighFrequencyCutoff T)
    (hthree : 3 ≤ Lwindow) (hwidth : 2 * c1 * B ≤ Lwindow)
    (hwindowBelowMedium :
      c1 * M1 / M3 * B < sourceLowFrequencyCutoff T etaFreq M1 M3)
    (hpsi1bounded : ∀ z, ‖FourierTransform.fourier psi1 z‖ ≤ Kpsi)
    (hpsi1decay2 : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hpsi1decay : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤
        K / (1 + |z|) ^ (qPoisson + 2))
    (hfirstPoissonBudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ qPoisson)
    (hm1ne : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1lo : ∀ m1 ∈ m1Range, M1 ≤ |(m1 : ℝ)|)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ c1 * M1)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hpsi1support : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard1scale : N1 ≤ c1 * M1)
    (hpairCardLow : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3),
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤ P)
    (hcoverLow : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3),
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange)
    (hxiLow : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3),
      ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y)
    (hinnerLow : ∀ xi ∈ lowFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3),
      ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤ Hinner)
    (hcoverMedium : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange)
    (hpsi2 : ∀ ell ∈ ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hxiMedium : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y)
    (hinnerMedium : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤ Hinner)
    (hghat : Integrable (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2))
    (hlowLocalizedInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier psi1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M3 B xi‖ ^ 2)
      (lowFrequencyRegion (sourceLowFrequencyCutoff T etaFreq M1 M3)))
    (hmediumLocalizedInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier psi1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M3 B xi‖ ^ 2)
      (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T)))
    (hsigma :
      sigmaIIFinite ellRange m2Range psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 B ≤ sigmaBound)
    {Sdec etaDec Cdec Rlo N1h N2h N3h P1 Rhi CIII : ℝ}
    (hSdec : 0 ≤ Sdec) (hCdec : 0 ≤ Cdec) (hRlo : 0 < Rlo)
    (hN1h : 0 ≤ N1h) (hN2h : 0 ≤ N2h) (hN3h : 0 ≤ N3h)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi)
    (hcard1h : (m1Range.card : ℝ) ≤ N1h)
    (hcard2h : (m2Range.card : ℝ) ≤ N2h)
    (hcard3h : (m3Range.card : ℝ) ≤ N3h)
    (hpsi1 : ∀ m3 ∈ m3Range, ‖psi1 ((m3 : ℝ) / M3)‖ ≤ P1)
    (hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))|)
    (hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hfdecay : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
        ((m2 / m1) * xi)‖ ≤
          Cdec * T ^ etaDec *
            (T / (|m2 / m1| * |xi|)) ^ (qHigh + 2) * Sdec)
    (hhighBudget :
      ((N1h * N2h * N3h * P1 * Rhi *
          (Cdec * T ^ etaDec * (T / Rlo) ^ (qHigh + 2) *
            2 ^ (qHigh + 2) * Sdec)) /
        (sourceHighFrequencyCutoff T) ^ qHigh) ^ 2 *
          quarticDecayMass * T ^ 100 ≤ CIII) :
    ∃ Cdiv : ℝ, 0 < Cdiv ∧
      (∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1
            (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2) ≤
        (4 * sourceLowFrequencyCutoff T etaFreq M1 M3 *
            (P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2) +
          4 * sourceLowFrequencyCutoff T etaFreq M1 M3 *
            ((C / T ^ 100) * (N1 * Hinner)) ^ 2) +
        ((2 * ((Lwindow * Cdiv *
            Real.rpow (sourceHighFrequencyCutoff T +
              c1 * M1 / M3 * B) etaPair) *
            c1 * Kpsi ^ 2 * (M1 + M3))) * sigmaBound +
          2 * volume.real (mediumFrequencyRegion
            (sourceLowFrequencyCutoff T etaFreq M1 M3)
            (sourceHighFrequencyCutoff T)) *
            ((C / T ^ 100) * (N1 * Hinner)) ^ 2) +
        CIII / T ^ 100 := by
  let ghat : ℝ → ℂ := FourierTransform.fourier
    (sourceGFinite m1Range m2Range m3Range psi1
      (fun u : ℝ => (f u : ℂ)) M3)
  have hm2ne : ∀ m2 ∈ m2Range, m2 ≠ 0 :=
    fun m2 hm2 => ne_of_gt (hm2pos m2 hm2)
  have hlow :=
    sourceGFinite_lowFrequencyIntegral_le_localized_add_firstPoissonTail
      m1Range ellRange m2Range m3Range psi1
      (fun u : ℝ => (f u : ℂ)) hf.ofReal qPoisson
      hpsi1compact hpsi1smooth T etaFreq M1 hM3 hB hY
      (lt_of_lt_of_le zero_lt_one hT) hK hKpsi hC hP hN1 hHinner
      hcut0 hpsi1bounded hpsi1decay2 hpsi1decay hfirstPoissonBudget
      hm1ne hm2ne hpsi1support hcard1 hpairCardLow hcoverLow hxiLow
      hinnerLow hghat.integrableOn hlowLocalizedInt
  obtain ⟨Cdiv, hCdiv, hmediumRaw⟩ :=
    exists_sourceGFinite_mediumIntegral_le_correctedSigmaII
      m1Range ellRange m2Range m3Range psi1
      (fun u : ℝ => (f u : ℂ)) hf.ofReal qPoisson
      hpsi1compact hpsi1smooth psi2 M1 M2 T hM1 hM3 hB hY
      (lt_of_lt_of_le zero_lt_one hT) hK hKpsi hC hN1 hHinner
      (by unfold sourceHighFrequencyCutoff; positivity) hc1 hLwindow
      hetaPair hthree hwidth hwindowBelowMedium hpsi1bounded
      hpsi1decay2 hpsi1decay hfirstPoissonBudget hm1ne hm1lo hm1hi
      hm2pos hpsi1support hcard1 hcard1scale hcoverMedium hpsi2
      hxiMedium hinnerMedium hghat.integrableOn hmediumLocalizedInt
  refine ⟨Cdiv, hCdiv, ?_⟩
  let Fmedium : ℝ :=
    2 * ((Lwindow * Cdiv *
      Real.rpow (sourceHighFrequencyCutoff T + c1 * M1 / M3 * B) etaPair) *
      c1 * Kpsi ^ 2 * (M1 + M3))
  let Emedium : ℝ :=
    2 * volume.real (mediumFrequencyRegion
      (sourceLowFrequencyCutoff T etaFreq M1 M3)
      (sourceHighFrequencyCutoff T)) *
      ((C / T ^ 100) * (N1 * Hinner)) ^ 2
  have hFmedium0 : 0 ≤ Fmedium := by
    dsimp only [Fmedium]
    have hhigh0 : 0 ≤ sourceHighFrequencyCutoff T := by
      unfold sourceHighFrequencyCutoff
      positivity
    have hwindow0 : 0 ≤ c1 * M1 / M3 * B := by positivity
    positivity [Real.rpow_nonneg (add_nonneg hhigh0 hwindow0) etaPair]
  have hmedium :
      (∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T), ‖ghat xi‖ ^ 2) ≤
        Fmedium * sigmaBound + Emedium := by
    have hSigma := mul_le_mul_of_nonneg_left hsigma hFmedium0
    calc
      (∫ xi in mediumFrequencyRegion
          (sourceLowFrequencyCutoff T etaFreq M1 M3)
          (sourceHighFrequencyCutoff T), ‖ghat xi‖ ^ 2) ≤
          Fmedium * sigmaIIFinite ellRange m2Range psi2
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            M2 T M3 B + Emedium := by
        dsimp only [ghat, Fmedium, Emedium]
        convert hmediumRaw using 1 <;> ring
      _ ≤ Fmedium * sigmaBound + Emedium := add_le_add hSigma le_rfl
  have hhigh :
      (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
        ‖ghat xi‖ ^ 2) ≤ CIII / T ^ 100 := by
    exact sourceGFinite_highFrequencyIntegral_le_time_neg100
      m1Range m2Range m3Range psi1 (fun u : ℝ => (f u : ℂ))
      hf.ofReal M3 qHigh hT hSdec hCdec hRlo hN1h hN2h hN3h
      hP1 hRhi hcard1h hcard2h hcard3h hm1ne hm2ne hpsi1
      hratioLo hratioHi hfdecay hghat.integrableOn hhighBudget
  have hfull := sourceFrequencyIntegral_le_of_region_bounds ghat hghat
    T etaFreq M1 M3
    (4 * sourceLowFrequencyCutoff T etaFreq M1 M3 *
        (P ^ 2 * (M3 * Kpsi) ^ 2 * Hinner ^ 2) +
      4 * sourceLowFrequencyCutoff T etaFreq M1 M3 *
        ((C / T ^ 100) * (N1 * Hinner)) ^ 2)
    (Fmedium * sigmaBound + Emedium) (CIII / T ^ 100)
    hcut hlow hmedium hhigh
  simpa only [ghat, Fmedium, Emedium] using hfull

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedPairs_le_rangeProduct
#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedPairs_cast_le_mul
#print axioms GuthMaynardJIteration.exists_sourceGFinite_frequencyIntegral_le_correctedSigmaII_v2
