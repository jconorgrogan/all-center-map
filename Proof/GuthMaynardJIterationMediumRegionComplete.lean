import GuthMaynardJIterationAffineEnergy

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Exact scalar-window and divisor-loss insertion into source region II. -/

/-- The literal source window `1 + M1/M3`, the subpower signed-divisor loss,
and the dyadic `m1` count assemble into the corrected region-II factor
`(M1+M3) * SigmaII`.  The first-Poisson `T^-100` error remains explicit. -/
theorem exists_sourceGFinite_mediumIntegral_le_correctedSigmaII
    (m1Range ellRange m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : ℝ → ℂ) (hf : Integrable f)
    (q : ℕ) (hcompact : HasCompactSupport psi1)
    (hsmooth : ContDiff ℝ ∞ psi1)
    (psi2 : ℝ → ℝ) (M1 M2 T : ℝ)
    {K0 K Kpsi M3 B Y C N1 Hinner a b c1 Lwindow eta : ℝ}
    (hM1 : 0 < M1) (hM3 : 0 < M3) (hB : 0 < B)
    (hY : 0 ≤ Y) (hT : 0 < T) (hK : 0 ≤ K)
    (hKpsi : 0 ≤ Kpsi) (hC : 0 ≤ C)
    (hN1 : 0 ≤ N1) (hHinner : 0 ≤ Hinner)
    (hb : 0 ≤ b) (hc1 : 0 ≤ c1) (hLwindow : 0 ≤ Lwindow)
    (heta : 0 < eta)
    (hthree : 3 ≤ Lwindow) (hwidth : 2 * c1 * B ≤ Lwindow)
    (hwindowBelowMedium : c1 * M1 / M3 * B < a)
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
    (hm1lo : ∀ m1 ∈ m1Range, M1 ≤ |(m1 : ℝ)|)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ c1 * M1)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard1scale : N1 ≤ c1 * M1)
    (hcover : ∀ xi ∈ mediumFrequencyRegion a b,
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange)
    (hpsi2 : ∀ ell ∈ ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hxi : ∀ xi ∈ mediumFrequencyRegion a b, ∀ m1 ∈ m1Range,
      |xi / (m1 : ℝ)| ≤ Y)
    (hinner : ∀ xi ∈ mediumFrequencyRegion a b, ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier f) m1 xi‖ ≤ Hinner)
    (hfullInt : IntegrableOn (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2)
      (mediumFrequencyRegion a b))
    (hlocalizedInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier psi1) (FourierTransform.fourier f)
        M3 B xi‖ ^ 2) (mediumFrequencyRegion a b)) :
    ∃ Cdiv : ℝ, 0 < Cdiv ∧
      (∫ xi in mediumFrequencyRegion a b,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) ≤
        2 * ((Lwindow * Cdiv *
            Real.rpow (b + c1 * M1 / M3 * B) eta) *
          c1 * Kpsi ^ 2 * (M1 + M3) *
          sigmaIIFinite ellRange m2Range psi2
            (FourierTransform.fourier f) M2 T M3 B) +
        2 * volume.real (mediumFrequencyRegion a b) *
          ((C / T ^ 100) * (N1 * Hinner)) ^ 2 := by
  let W : ℝ := c1 * M1 / M3 * B
  let Nwindow : ℝ := Lwindow * (1 + M1 / M3)
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hradius : ∀ m1 ∈ m1Range,
      (|(m1 : ℝ)| / M3) * B ≤ W := by
    simpa only [W] using
      sourceMediumRadius_le_dyadicWindow hM3 hB.le hm1hi
  have hwindow : ∀ xi ∈ mediumFrequencyRegion a b,
      ((sourceIntegerWindow xi W).card : ℝ) ≤ Nwindow := by
    intro xi hxiMedium
    dsimp only [W, Nwindow]
    exact card_sourceIntegerWindow_le_sourceScale xi hM1.le hM3 hB.le hc1
      hthree hwidth
  obtain ⟨Cdiv, hCdiv, hpair⟩ :=
    exists_sourceMediumLocalizedPairCard_subpower
      m1Range ellRange heta hb hW0
      (by simpa only [W] using hwindowBelowMedium)
      hradius hwindow
  refine ⟨Cdiv, hCdiv, ?_⟩
  let Lpair : ℝ := Lwindow * Cdiv * Real.rpow (b + W) eta
  let P : ℝ := Nwindow * Cdiv * Real.rpow (b + W) eta
  have hratio0 : 0 ≤ M1 / M3 := div_nonneg hM1.le hM3.le
  have hbW : 0 ≤ b + W := add_nonneg hb hW0
  have hLpair0 : 0 ≤ Lpair := by
    dsimp only [Lpair]
    exact mul_nonneg (mul_nonneg hLwindow hCdiv.le)
      (Real.rpow_nonneg hbW eta)
  have hP0 : 0 ≤ P := by
    dsimp only [P, Nwindow]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hLwindow (add_nonneg zero_le_one hratio0)) hCdiv.le)
      (Real.rpow_nonneg hbW eta)
  have hpairCard : ∀ xi ∈ mediumFrequencyRegion a b,
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤ P := by
    intro xi hxiMedium
    exact hpair xi hxiMedium
  have hpairScale : P ≤ Lpair * (1 + M1 / M3) := by
    dsimp only [P, Nwindow, Lpair]
    ring_nf
    exact le_rfl
  let Sigma : ℝ := sigmaIIFinite ellRange m2Range psi2
    (FourierTransform.fourier f) M2 T M3 B
  have hSigma0 : 0 ≤ Sigma := by
    dsimp only [Sigma, sigmaIIFinite]
    apply Finset.sum_nonneg
    intro ell hell
    exact mul_nonneg (le_trans (by norm_num) (hpsi2 ell hell))
      (intervalIntegral.integral_nonneg (by linarith) fun tau htau => sq_nonneg _)
  have hmedium := sourceGFinite_mediumIntegral_le_sigmaII_add_firstPoissonTail
    m1Range ellRange m2Range m3Range psi1 f hf q hcompact hsmooth
    (mediumFrequencyRegion a b) (measurableSet_mediumFrequencyRegion a b)
    (volume_mediumFrequencyRegion_ne_top (a := a) (b := b))
    psi2 M1 M2 T hM1 hM3 hB hY hT hK hKpsi hC hP0 hN1 hHinner
    hbounded hdecay2 hdecay hbudget hm1 hm1lo hm2pos hsupport hcard1
    hpairCard hcover hpsi2 hxi hinner hfullInt hlocalizedInt
  have hfactor :
      P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma ≤
        (Lpair * c1 * Kpsi ^ 2) * (M1 + M3) * Sigma :=
    sourceMediumSigmaOutsideFactor_le hM1 hM3 hN1 hLpair0 hSigma0
      hpairScale hcard1scale
  calc
    (∫ xi in mediumFrequencyRegion a b,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) ≤
      2 * (P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma) +
        2 * volume.real (mediumFrequencyRegion a b) *
          ((C / T ^ 100) * (N1 * Hinner)) ^ 2 := by
      simpa only [Sigma] using hmedium
    _ ≤ 2 * ((Lpair * c1 * Kpsi ^ 2) * (M1 + M3) * Sigma) +
        2 * volume.real (mediumFrequencyRegion a b) *
          ((C / T ^ 100) * (N1 * Hinner)) ^ 2 := by
      gcongr
    _ = _ := by
      simp only [Lpair, W, Sigma]

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.exists_sourceGFinite_mediumIntegral_le_correctedSigmaII
