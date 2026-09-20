import GuthMaynardJIterationAffineConfigs

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The exact `SigmaII` estimate with the source's selected affine branch
instantiated in the canonical finite powerset family.  This removes both the
artificial configuration-membership and bounded-supremum premises while
retaining every Poisson, support, integrability, coefficient and tail premise. -/
theorem sigmaIIFinite_le_canonicalAffineJ_sqrt_add_time_neg100
    (f psi2 psi : ℝ → ℝ) (hf : Integrable f)
    (ellRange mRange jRange : Finset ℤ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hpsi2smooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (q : ℕ) {K0 Kdec Ksup M2 T B Y C M3 Ctau c : ℝ}
    (hKdec : 0 ≤ Kdec) (hKsup : 0 ≤ Ksup)
    (hM2 : 0 < M2) (hT : 0 < T) (hB : 0 < B)
    (hY : 0 ≤ Y) (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (hc : 0 ≤ c)
    (hf0 : ∀ v, 0 ≤ f v) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        Kdec / (1 + |xi|) ^ (q + 2))
    (hF : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤ Ksup)
    (hbudget :
      (T / M2) * Kdec *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0)
    (hmpos : ∀ m ∈ mRange, 0 < (m : ℝ))
    (hmhi : ∀ m ∈ mRange, |(m : ℝ)| ≤ c * M2)
    (hy : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      ∀ z : ℝ × ℝ, f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y)
    (hpsi_major : ∀ m2' ∈ mRange, ∀ z,
      |z| ≤ (M2 / (m2' : ℝ)) * B → 1 ≤ psi z)
    (hlocal : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      ∀ u : ℝ, ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
        {u' | |(j : ℝ) - (m2' : ℝ) * u' + (m2 : ℝ) * u| ≤
          (M2 / T) * B})
    (haffineSmooth : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      ∀ u : ℝ, ∀ j : ℤ, Integrable
        (fun u' => T * psi (T *
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j - u')) * f u'))
    (hsum : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange, ∀ u : ℝ,
      Summable (fun j : ℤ => affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)))
    (hret : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (sigmaIIZPairRetainedKernel psi2 f
        M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (htail : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (sigmaIIZPairTailKernel psi2 f
        M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (hmajor : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (fun u : ℝ =>
        ((2 * Ctau * Ksup) / M2) * f u *
          ∑' j : ℤ, affineSmoothing T psi f
            (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)))
    (hpairInt : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (fun u : ℝ => f u *
        ∑' j : ℤ, affineSmoothing T psi f
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)))
    (hcover : ∀ u, f u ≠ 0 → ∀ m1 ∈ mRange, ∀ m2 ∈ mRange, ∀ j : ℤ,
      affineSmoothing T psi f
        (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0 → j ∈ jRange)
    (hfmeas : AEStronglyMeasurable f)
    (hameas : AEStronglyMeasurable
      (sourceFiniteAffineSum mRange mRange jRange
        (affineSmoothing T psi f)))
    (hf2 : Integrable (fun u => f u ^ 2))
    (ha2 : Integrable (fun u =>
      (sourceFiniteAffineSum mRange mRange jRange
        (affineSmoothing T psi f) u) ^ 2)) :
    sigmaIIFinite ellRange mRange psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau ≤
      ((2 * Ctau * Ksup) * c ^ 2 * M2) *
        Real.sqrt ((∫ u : ℝ, f u ^ 2) *
          sourceAffineJ (sourceAffineConfigs mRange jRange)
            (affineSmoothing T psi f)) +
      ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100)) := by
  exact sigmaIIFinite_le_affineJ_sqrt_add_time_neg100
    f psi2 psi hf ellRange mRange jRange hcompact hpsi2smooth q
    hKdec hKsup hM2 hT hB hY hM3 hCtau hc hf0 hpsi0 hdecay2 hdecay hF
    hbudget hsupport hmpos hmhi hy hpsi_major hlocal haffineSmooth hsum hret
    htail hmajor hpairInt (sourceAffineConfigs mRange jRange)
    (self_mem_sourceAffineConfigs mRange jRange)
    (bddAbove_sourceAffineConfigEnergies mRange jRange
      (affineSmoothing T psi f))
    hcover hfmeas hameas hf2 ha2

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sigmaIIFinite_le_canonicalAffineJ_sqrt_add_time_neg100
