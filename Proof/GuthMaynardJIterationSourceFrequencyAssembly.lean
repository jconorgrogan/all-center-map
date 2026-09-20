import GuthMaynardJIterationSourceHighFrequency

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Source-shaped assembly of regions I, II, and III. -/

/-- Assemble the actual finite low-frequency estimate, a medium reduction to
the literal corrected-`M₃` finite `Sigma_II`, and the actual rapid-decay
high-frequency estimate for `sourceGFinite`.  Thus the theorem's only analytic
inputs are the source's medium reduction and a bound for the now-explicit
finite `Sigma_II`; regions I and III are derived, not renamed hypotheses. -/
theorem sourceGFinite_frequencyIntegral_le_of_mediumSigma
    {ι : Type*}
    (m1Range m2Range m3Range ellRange : Finset ℤ) (outer : Finset ι)
    (psi1 : ℝ → ℂ) (f : ℝ → ℝ) (hf : Integrable f)
    (psi2 : ℝ → ℝ)
    (T eta M1 M2 M3 Ctau mediumFactor mediumError sigmaBound : ℝ)
    (arg : ℝ → ι → ℤ → ℝ) (coeff : ι → ℤ → ℂ)
    {Rlow Slow Llow N2low : ℝ}
    (hghatEq : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T eta M1 M3),
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
      (sourceLowFrequencyCutoff T eta M1 M3),
      ∀ i ∈ outer, ∀ m2 ∈ m2Range,
        ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
          (arg xi i m2)‖ ≤ Slow)
    (hM3nonneg : 0 ≤ M3) (hRlow0 : 0 ≤ Rlow) (hSlow0 : 0 ≤ Slow)
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T eta M1 M3)
    (hghat : Integrable (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2))
    (hcut : sourceLowFrequencyCutoff T eta M1 M3 ≤
      sourceHighFrequencyCutoff T)
    (hmediumFactor : 0 ≤ mediumFactor)
    (hmediumSigma :
      (∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3)
        (sourceHighFrequencyCutoff T),
          ‖FourierTransform.fourier
            (sourceGFinite m1Range m2Range m3Range psi1
              (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2) ≤
        mediumFactor *
          sigmaIIFinite ellRange m2Range psi2
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            M2 T M3 Ctau + mediumError)
    (hsigma :
      sigmaIIFinite ellRange m2Range psi2
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          M2 T M3 Ctau ≤ sigmaBound)
    (q : ℕ) {Sdec etaDec Cdec Rlo N1 N2 N3 P1 Rhi CIII : ℝ}
    (hT : 1 ≤ T) (hSdec : 0 ≤ Sdec) (hCdec : 0 ≤ Cdec)
    (hRlo : 0 < Rlo)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard2 : (m2Range.card : ℝ) ≤ N2)
    (hcard3 : (m3Range.card : ℝ) ≤ N3)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hpsi1 : ∀ m3 ∈ m3Range, ‖psi1 ((m3 : ℝ) / M3)‖ ≤ P1)
    (hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))|)
    (hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hdecay : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
        ((m2 / m1) * xi)‖ ≤
          Cdec * T ^ etaDec *
            (T / (|m2 / m1| * |xi|)) ^ (q + 2) * Sdec)
    (hhighBudget :
      ((N1 * N2 * N3 * P1 * Rhi *
          (Cdec * T ^ etaDec * (T / Rlo) ^ (q + 2) *
            2 ^ (q + 2) * Sdec)) /
        (sourceHighFrequencyCutoff T) ^ q) ^ 2 *
          quarticDecayMass * T ^ 100 ≤ CIII) :
    (∫ xi : ℝ,
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (f u : ℂ)) M3) xi‖ ^ 2) ≤
      2 * sourceLowFrequencyCutoff T eta M1 M3 *
          (Llow ^ 2 * M3 ^ 2 * N2low ^ 2 * Rlow ^ 2 * Slow ^ 2) +
        (mediumFactor * sigmaBound + mediumError) + CIII / T ^ 100 := by
  let ghat : ℝ → ℂ := FourierTransform.fourier
    (sourceGFinite m1Range m2Range m3Range psi1
      (fun u : ℝ => (f u : ℂ)) M3)
  have hlow :
      (∫ xi in lowFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3), ‖ghat xi‖ ^ 2) ≤
      2 * sourceLowFrequencyCutoff T eta M1 M3 *
        (Llow ^ 2 * M3 ^ 2 * N2low ^ 2 * Rlow ^ 2 * Slow ^ 2) := by
    exact sourceLowFrequencyIntegral_from_finite_outer
      outer m2Range ghat
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
      T eta M1 M3 Rlow Slow Llow N2low arg coeff hghatEq
      hLlow hN2low hRlow hSlow hM3nonneg hRlow0 hSlow0 hcut0
      hghat.integrableOn
  have hmedium :
      (∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3)
        (sourceHighFrequencyCutoff T), ‖ghat xi‖ ^ 2) ≤
      mediumFactor * sigmaBound + mediumError := by
    refine hmediumSigma.trans ?_
    gcongr
  have hhigh :
      (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
        ‖ghat xi‖ ^ 2) ≤ CIII / T ^ 100 := by
    exact sourceGFinite_highFrequencyIntegral_le_time_neg100
      m1Range m2Range m3Range psi1 (fun u : ℝ => (f u : ℂ))
      hf.ofReal M3 q hT hSdec hCdec hRlo hN1 hN2 hN3 hP1 hRhi
      hcard1 hcard2 hcard3 hm1 hm2 hpsi1 hratioLo hratioHi hdecay
      hghat.integrableOn hhighBudget
  exact sourceFrequencyIntegral_le_of_region_bounds ghat hghat
    T eta M1 M3
    (2 * sourceLowFrequencyCutoff T eta M1 M3 *
      (Llow ^ 2 * M3 ^ 2 * N2low ^ 2 * Rlow ^ 2 * Slow ^ 2))
    (mediumFactor * sigmaBound + mediumError) (CIII / T ^ 100)
    hcut hlow hmedium hhigh

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceGFinite_frequencyIntegral_le_of_mediumSigma
