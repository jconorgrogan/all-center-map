import GuthMaynardJIterationMediumRegionComplete
import GuthMaynardJIterationSourceFrequencyAssembly

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Exact low/medium/high assembly with the medium region derived from the
literal integer window, signed-divisor subpower bound, corrected `M3`
frequency, and first-Poisson tail.  The only remaining numerical input is an
upper bound for the now-explicit finite `SigmaII`. -/
theorem exists_sourceGFinite_frequencyIntegral_le_correctedSigmaII
    {ι : Type*}
    (m1Range m2Range m3Range ellRange : Finset ℤ) (outer : Finset ι)
    (psi1 : ℝ → ℂ) (f : ℝ → ℝ) (hf : Integrable f)
    (psi2 : ℝ → ℝ)
    (T etaFreq etaPair M1 M2 M3 B sigmaBound : ℝ)
    (arg : ℝ → ι → ℤ → ℝ) (coeff : ι → ℤ → ℂ)
    {Rlow Slow Llow N2low : ℝ}
    (hghatEq : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T etaFreq M1 M3),
      FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1
            (fun u : ℝ => (f u : ℂ)) M3) xi =
        sourceLowOuterSum outer (fun i =>
          (M3 : ℂ) * ∑ m2 ∈ m2Range,
            coeff i m2 *
              FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                (arg xi i m2)))
    (hLlow : (outer.card : ℝ) ≤ Llow)
    (hN2low : (m2Range.card : ℝ) ≤ N2low)
    (hRlow : ∀ i ∈ outer, ∀ m2 ∈ m2Range, ‖coeff i m2‖ ≤ Rlow)
    (hSlow : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T etaFreq M1 M3),
      ∀ i ∈ outer, ∀ m2 ∈ m2Range,
        ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
          (arg xi i m2)‖ ≤ Slow)
    (hRlow0 : 0 ≤ Rlow) (hSlow0 : 0 ≤ Slow)
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T etaFreq M1 M3)
    (hghat : Integrable (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2))
    (hcut : sourceLowFrequencyCutoff T etaFreq M1 M3 ≤
      sourceHighFrequencyCutoff T)
    (hsigma :
      sigmaIIFinite ellRange m2Range psi2
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          M2 T M3 B ≤ sigmaBound)
    (qHigh : ℕ) {Sdec etaDec Cdec Rlo N1h N2h N3h P1 Rhi CIII : ℝ}
    (hT : 1 ≤ T) (hSdec : 0 ≤ Sdec) (hCdec : 0 ≤ Cdec)
    (hRlo : 0 < Rlo)
    (hN1h : 0 ≤ N1h) (hN2h : 0 ≤ N2h) (hN3h : 0 ≤ N3h)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi)
    (hcard1h : (m1Range.card : ℝ) ≤ N1h)
    (hcard2h : (m2Range.card : ℝ) ≤ N2h)
    (hcard3h : (m3Range.card : ℝ) ≤ N3h)
    (hm1ne : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2ne : ∀ m2 ∈ m2Range, m2 ≠ 0)
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
          quarticDecayMass * T ^ 100 ≤ CIII)
    (qPoisson : ℕ)
    {K0 K Kpsi Y C N1 Hinner c1 Lwindow : ℝ}
    (hpsi1compact : HasCompactSupport psi1)
    (hpsi1smooth : ContDiff ℝ ∞ psi1)
    (hM1 : 0 < M1) (hM3 : 0 < M3) (hB : 0 < B)
    (hY : 0 ≤ Y) (hK : 0 ≤ K) (hKpsi : 0 ≤ Kpsi)
    (hC : 0 ≤ C) (hN1 : 0 ≤ N1) (hHinner : 0 ≤ Hinner)
    (hc1 : 0 ≤ c1) (hLwindow : 0 ≤ Lwindow) (hetaPair : 0 < etaPair)
    (hthree : 3 ≤ Lwindow) (hwidth : 2 * c1 * B ≤ Lwindow)
    (hwindowBelowMedium :
      c1 * M1 / M3 * B < sourceLowFrequencyCutoff T etaFreq M1 M3)
    (hpsi1bounded : ∀ z, ‖FourierTransform.fourier psi1 z‖ ≤ Kpsi)
    (hpsi1decay2 : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hpsi1decay : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K / (1 + |z|) ^ (qPoisson + 2))
    (hfirstPoissonBudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ qPoisson)
    (hm1lo : ∀ m1 ∈ m1Range, M1 ≤ |(m1 : ℝ)|)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ c1 * M1)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hpsi1support : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard1scale : N1 ≤ c1 * M1)
    (hcover : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange)
    (hpsi2 : ∀ ell ∈ ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hxi : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y)
    (hinner : ∀ xi ∈ mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤ Hinner)
    (hlocalizedInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier psi1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M3 B xi‖ ^ 2)
      (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T))) :
    ∃ Cdiv : ℝ, 0 < Cdiv ∧
      (∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1
            (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2) ≤
        2 * sourceLowFrequencyCutoff T etaFreq M1 M3 *
          (Llow ^ 2 * M3 ^ 2 * N2low ^ 2 * Rlow ^ 2 * Slow ^ 2) +
        ((2 * ((Lwindow * Cdiv *
            Real.rpow (sourceHighFrequencyCutoff T +
              c1 * M1 / M3 * B) etaPair) *
            c1 * Kpsi ^ 2 * (M1 + M3))) * sigmaBound +
          2 * volume.real (mediumFrequencyRegion
            (sourceLowFrequencyCutoff T etaFreq M1 M3)
            (sourceHighFrequencyCutoff T)) *
            ((C / T ^ 100) * (N1 * Hinner)) ^ 2) +
        CIII / T ^ 100 := by
  obtain ⟨Cdiv, hCdiv, hmedium⟩ :=
    exists_sourceGFinite_mediumIntegral_le_correctedSigmaII
      m1Range ellRange m2Range m3Range psi1
      (fun u : ℝ => (f u : ℂ)) hf.ofReal qPoisson hpsi1compact hpsi1smooth
      psi2 M1 M2 T hM1 hM3 hB hY (lt_of_lt_of_le zero_lt_one hT)
      hK hKpsi hC hN1 hHinner
      (by unfold sourceHighFrequencyCutoff; positivity) hc1 hLwindow hetaPair
      hthree hwidth hwindowBelowMedium hpsi1bounded hpsi1decay2 hpsi1decay
      hfirstPoissonBudget hm1ne hm1lo hm1hi hm2pos hpsi1support hcard1
      hcard1scale hcover hpsi2 hxi hinner hghat.integrableOn hlocalizedInt
  refine ⟨Cdiv, hCdiv, ?_⟩
  let Fmedium : ℝ :=
    (Lwindow * Cdiv * Real.rpow (sourceHighFrequencyCutoff T +
      c1 * M1 / M3 * B) etaPair) * c1 * Kpsi ^ 2 * (M1 + M3)
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
    have hW0 : 0 ≤ c1 * M1 / M3 * B := by positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hLwindow hCdiv.le)
            (Real.rpow_nonneg (add_nonneg hhigh0 hW0) etaPair)) hc1)
        (sq_nonneg Kpsi))
      (add_nonneg hM1.le hM3.le)
  have hmedium' :
      (∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T etaFreq M1 M3)
        (sourceHighFrequencyCutoff T),
          ‖FourierTransform.fourier
            (sourceGFinite m1Range m2Range m3Range psi1
              (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2) ≤
        (2 * Fmedium) *
          sigmaIIFinite ellRange m2Range psi2
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            M2 T M3 B + Emedium := by
    dsimp only [Fmedium, Emedium]
    convert hmedium using 1 <;> ring
  have hfull := sourceGFinite_frequencyIntegral_le_of_mediumSigma
    m1Range m2Range m3Range ellRange outer psi1 f hf psi2
    T etaFreq M1 M2 M3 B (2 * Fmedium) Emedium sigmaBound arg coeff
    hghatEq hLlow hN2low hRlow hSlow hM3.le hRlow0 hSlow0 hcut0 hghat hcut
    (mul_nonneg (by norm_num) hFmedium0) hmedium' hsigma qHigh hT hSdec hCdec
    hRlo hN1h hN2h hN3h hP1 hRhi hcard1h hcard2h hcard3h hm1ne hm2ne
    hpsi1 hratioLo hratioHi hfdecay hhighBudget
  simpa only [Fmedium, Emedium] using hfull

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.exists_sourceGFinite_frequencyIntegral_le_correctedSigmaII
