import GuthMaynardJIterationMediumRegionAggregation

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Explicit insertion of the certified first-Poisson truncation tail. -/

/-- Deterministic integration of a uniform norm approximation on a finite
measure set.  The factor `2` and the exact measure of the region are visible. -/
theorem setIntegral_norm_sq_le_of_uniform_approximation
    (g r : ℝ → ℂ) (S : Set ℝ) (hS : MeasurableSet S)
    {E : ℝ}
    (hg : IntegrableOn (fun xi => ‖g xi‖ ^ 2) S)
    (hr : IntegrableOn (fun xi => ‖r xi‖ ^ 2) S)
    (hSfinite : volume S ≠ (⊤ : ENNReal))
    (happrox : ∀ xi ∈ S, ‖g xi - r xi‖ ≤ E) :
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
      2 * (∫ xi in S, ‖r xi‖ ^ 2) + 2 * volume.real S * E ^ 2 := by
  have hconst : IntegrableOn (fun _xi : ℝ => 2 * E ^ 2) S :=
    integrableOn_const hSfinite
  have hright : IntegrableOn
      (fun xi => 2 * ‖r xi‖ ^ 2 + 2 * E ^ 2) S :=
    (hr.const_mul 2).add hconst
  have hpoint : ∀ xi ∈ S,
      ‖g xi‖ ^ 2 ≤ 2 * ‖r xi‖ ^ 2 + 2 * E ^ 2 := by
    intro xi hxi
    have htriangle : ‖g xi‖ ≤ ‖r xi‖ + ‖g xi - r xi‖ := by
      calc
        ‖g xi‖ = ‖r xi + (g xi - r xi)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have hnorm : ‖g xi‖ ≤ ‖r xi‖ + E :=
      htriangle.trans (by
        simpa [add_comm] using add_le_add_right (happrox xi hxi) ‖r xi‖)
    have hsq : ‖g xi‖ ^ 2 ≤ (‖r xi‖ + E) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖r xi‖ - E)]
  calc
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
        ∫ xi in S, (2 * ‖r xi‖ ^ 2 + 2 * E ^ 2) :=
      setIntegral_mono_on hg hright hS hpoint
    _ = 2 * (∫ xi in S, ‖r xi‖ ^ 2) + 2 * volume.real S * E ^ 2 := by
      have hconstInt : (∫ _xi : ℝ in S, 2 * E ^ 2) =
          volume.real S * (2 * E ^ 2) := by
        exact setIntegral_const (2 * E ^ 2)
      have htwoInt : (∫ xi in S, 2 * ‖r xi‖ ^ 2) =
          2 * ∫ xi in S, ‖r xi‖ ^ 2 := by
        exact MeasureTheory.integral_const_mul 2 (fun xi => ‖r xi‖ ^ 2)
      calc
        (∫ xi in S, (2 * ‖r xi‖ ^ 2 + 2 * E ^ 2)) =
            (∫ xi in S, 2 * ‖r xi‖ ^ 2) +
              ∫ xi in S, 2 * E ^ 2 :=
          integral_add (hr.const_mul 2) hconst
        _ = (2 * ∫ xi in S, ‖r xi‖ ^ 2) +
            volume.real S * (2 * E ^ 2) :=
          congrArg₂ (· + ·) htwoInt hconstInt
        _ = _ := by ring

/-- The actual finite source Fourier transform on a measurable medium region
is bounded by the corrected finite `Sigma_II` plus the already-certified
uniform first-Poisson tail.  This is the literal tail insertion missing
between TeX 1588 and 1598; no `O` notation is used. -/
theorem sourceGFinite_mediumIntegral_le_sigmaII_add_firstPoissonTail
    (m1Range ellRange m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : ℝ → ℂ) (hf : Integrable f)
    (q : ℕ) (hcompact : HasCompactSupport psi1)
    (hsmooth : ContDiff ℝ ∞ psi1)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSfinite : volume S ≠ (⊤ : ENNReal))
    (psi2 : ℝ → ℝ) (M1 M2 T : ℝ)
    {K0 K Kpsi M3 B Y C P N1 Hinner : ℝ}
    (hM1 : 0 < M1) (hM3 : 0 < M3) (hB : 0 < B)
    (hY : 0 ≤ Y) (hT : 0 < T) (hK : 0 ≤ K)
    (hKpsi : 0 ≤ Kpsi) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hN1 : 0 ≤ N1) (hHinner : 0 ≤ Hinner)
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
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hpairCard : ∀ xi ∈ S,
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤ P)
    (hcover : ∀ xi ∈ S, ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange)
    (hpsi2 : ∀ ell ∈ ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hxi : ∀ xi ∈ S, ∀ m1 ∈ m1Range,
      |xi / (m1 : ℝ)| ≤ Y)
    (hinner : ∀ xi ∈ S, ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier f) m1 xi‖ ≤ Hinner)
    (hfullInt : IntegrableOn (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) S)
    (hlocalizedInt : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier psi1) (FourierTransform.fourier f)
        M3 B xi‖ ^ 2) S) :
    (∫ xi in S,
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) ≤
      2 * (P * (N1 * (M3 * Kpsi ^ 2 / M1)) *
        sigmaIIFinite ellRange m2Range psi2
          (FourierTransform.fourier f) M2 T M3 B) +
      2 * volume.real S *
        ((C / T ^ 100) * (N1 * Hinner)) ^ 2 := by
  let g : ℝ → ℂ := FourierTransform.fourier
    (sourceGFinite m1Range m2Range m3Range psi1 f M3)
  let retained : ℝ → ℂ := fun xi =>
    sourceFirstPoissonRetainedFinite m1Range m2Range
      (FourierTransform.fourier psi1) (FourierTransform.fourier f) M3 B xi
  let localized : ℝ → ℂ := fun xi =>
    sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
      (FourierTransform.fourier psi1) (FourierTransform.fourier f) M3 B xi
  let E : ℝ := (C / T ^ 100) * (N1 * Hinner)
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
      hT hdecay2 hdecay hbudget hm1
      (fun m2 hm2mem => ne_of_gt (hm2pos m2 hm2mem)) hsupport xi
      (hxi xi hxiS)
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
      _ ≤ E := by
        exact mul_le_mul_of_nonneg_left hsum
          (div_nonneg hC (pow_pos hT _).le)
  have happrox := setIntegral_norm_sq_le_of_uniform_approximation
    g retained S hS hfullInt hretInt hSfinite htail
  have hretBound :
      (∫ xi in S, ‖retained xi‖ ^ 2) ≤
        P * (N1 * (M3 * Kpsi ^ 2 / M1)) *
          sigmaIIFinite ellRange m2Range psi2
            (FourierTransform.fourier f) M2 T M3 B := by
    calc
      (∫ xi in S, ‖retained xi‖ ^ 2) =
          ∫ xi in S, ‖localized xi‖ ^ 2 := by
            apply setIntegral_congr_fun hS
            intro xi hxiS
            exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hretEq hxiS)
      _ ≤ _ := setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_sigmaII
        m1Range ellRange m2Range (FourierTransform.fourier psi1)
        (FourierTransform.fourier f)
        (VectorFourier.fourierIntegral_continuous
          Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf)
        S hS psi2 M2 T hM1 hM3 hB.le hKpsi hP hN1 hbounded hm1 hm1lo
        hm2pos hcard1 hpairCard hpsi2 hlocalizedInt
  calc
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
        2 * (∫ xi in S, ‖retained xi‖ ^ 2) +
          2 * volume.real S * E ^ 2 := happrox
    _ ≤ 2 * (P * (N1 * (M3 * Kpsi ^ 2 / M1)) *
          sigmaIIFinite ellRange m2Range psi2
            (FourierTransform.fourier f) M2 T M3 B) +
        2 * volume.real S * E ^ 2 := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hretBound
          (show 0 ≤ (2 : ℝ) by norm_num))
        (2 * volume.real S * E ^ 2)
    _ = _ := by rfl

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.setIntegral_norm_sq_le_of_uniform_approximation
#print axioms GuthMaynardJIteration.sourceGFinite_mediumIntegral_le_sigmaII_add_firstPoissonTail
