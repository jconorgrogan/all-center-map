import GuthMaynardJIterationMediumRegionComplete
import GuthMaynardJIterationMediumAggregation

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def sourceAffinePairMass
    (mRange : Finset ℤ) (T : ℝ) (psi f : ℝ → ℝ)
    (m2 m2' : ℤ) : ℝ :=
  ∫ u : ℝ, f u * ∑' j : ℤ,
    affineSmoothing T psi f (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)

theorem affineSmoothing_nonneg
    {T : ℝ} (psi f : ℝ → ℝ) (hT : 0 ≤ T)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u) :
    ∀ x, 0 ≤ affineSmoothing T psi f x := by
  intro x
  unfold affineSmoothing
  exact integral_nonneg fun u =>
    mul_nonneg (mul_nonneg hT (hpsi0 _)) (hf0 u)

theorem sourceAffinePairMass_nonneg
    (mRange : Finset ℤ) {T : ℝ} (psi f : ℝ → ℝ)
    (hT : 0 ≤ T) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hf0 : ∀ u, 0 ≤ f u) (m2 m2' : ℤ) :
    0 ≤ sourceAffinePairMass mRange T psi f m2 m2' := by
  unfold sourceAffinePairMass
  apply integral_nonneg
  intro u
  exact mul_nonneg (hf0 u) (tsum_nonneg fun j =>
    affineSmoothing_nonneg psi f hT hpsi0 hf0 _)

/-- TeX 1645--1657 with all finite ranges exposed: the certified second
Poisson smoothing estimate, literal dyadic coefficient cancellation, and
whole-line Cauchy identify the medium `SigmaII` contribution with an actual
finite branch of `J(tilde f)`. -/
theorem sigmaIIFinite_le_affineJ_sqrt_add_time_neg100
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
    (configs : Set (Finset ℤ × Finset ℤ × Finset ℤ))
    (hconfig : (mRange, mRange, jRange) ∈ configs)
    (hbounded : BddAbove {x : ℝ | ∃ cfg ∈ configs,
      x = sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2
        (affineSmoothing T psi f)})
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
          sourceAffineJ configs (affineSmoothing T psi f)) +
      ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100)) := by
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  let D : ℝ := (2 * Ctau * Ksup) * c ^ 2 * M2
  let tailMass : ℝ :=
    (∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100)
  have hftilde0 : ∀ x, 0 ≤ ftilde x :=
    affineSmoothing_nonneg psi f hT.le hpsi0 hf0
  have hraw := sigmaIIFinite_le_pairSmoothing_add_time_neg100
    f psi2 psi hf ellRange mRange hcompact hpsi2smooth q hKdec hKsup
    hM2 hT hB hY hM3 hCtau hf0 hpsi0 hdecay2 hdecay hF hbudget
    hsupport hmpos hy hpsi_major hlocal haffineSmooth hsum hret htail hmajor
  have hpairMass0 : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      0 ≤ sourceAffinePairMass mRange T psi f m2 m2' := by
    intro m2 hm2 m2' hm2'
    exact sourceAffinePairMass_nonneg mRange psi f hT.le hpsi0 hf0 m2 m2'
  have hterm : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      |(m2 : ℝ) * (m2' : ℝ)| *
          ((∫ u : ℝ,
            ((2 * Ctau * Ksup) / M2) * f u *
              ∑' j : ℤ, ftilde
                (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) +
            tailMass) ≤
        D * sourceAffinePairMass mRange T psi f m2 m2' +
          |(m2 : ℝ) * (m2' : ℝ)| * tailMass := by
    intro m2 hm2 m2' hm2'
    have hcoeff := sourceDyadicPairCoefficient_le_M2
      hM2 hCtau hKsup hc m2 m2' (hmhi m2 hm2) (hmhi m2' hm2')
    have hint :
        (∫ u : ℝ,
          ((2 * Ctau * Ksup) / M2) * f u *
            ∑' j : ℤ, ftilde
              (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) =
        ((2 * Ctau * Ksup) / M2) *
          sourceAffinePairMass mRange T psi f m2 m2' := by
      unfold sourceAffinePairMass
      calc
        (∫ u : ℝ,
          ((2 * Ctau * Ksup) / M2) * f u *
            ∑' j : ℤ, ftilde
              (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) =
          ∫ u : ℝ, ((2 * Ctau * Ksup) / M2) *
            (f u * ∑' j : ℤ, ftilde
              (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
            apply integral_congr_ae
            filter_upwards with u
            ring
        _ = ((2 * Ctau * Ksup) / M2) *
            ∫ u : ℝ, f u * ∑' j : ℤ, ftilde
              (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j) :=
          integral_const_mul _ _
    rw [hint]
    dsimp only [D]
    calc
      |(m2 : ℝ) * (m2' : ℝ)| *
          (((2 * Ctau * Ksup) / M2) *
            sourceAffinePairMass mRange T psi f m2 m2' + tailMass) =
        (|(m2 : ℝ) * (m2' : ℝ)| * ((2 * Ctau * Ksup) / M2)) *
            sourceAffinePairMass mRange T psi f m2 m2' +
          |(m2 : ℝ) * (m2' : ℝ)| * tailMass := by ring
      _ ≤ ((2 * Ctau * Ksup) * c ^ 2 * M2) *
            sourceAffinePairMass mRange T psi f m2 m2' +
          |(m2 : ℝ) * (m2' : ℝ)| * tailMass := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcoeff
            (hpairMass0 m2 hm2 m2' hm2')) le_rfl
  have hsumBound :
      sigmaIIFinite ellRange mRange psi2
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          M2 T M3 Ctau ≤
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          (D * sourceAffinePairMass mRange T psi f m2 m2' +
            |(m2 : ℝ) * (m2' : ℝ)| * tailMass) := by
    refine hraw.trans ?_
    apply Finset.sum_le_sum
    intro m2 hm2
    apply Finset.sum_le_sum
    intro m2' hm2'
    simpa only [ftilde, tailMass] using hterm m2 hm2 m2' hm2'
  let A : ℝ → ℝ := sourceFiniteAffineSum mRange mRange jRange ftilde
  have hglobalEq :
      (∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        sourceAffinePairMass mRange T psi f m2 m2') =
        ∫ u : ℝ, f u * A u := by
    have htermInt : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
        Integrable (fun u : ℝ => f u * ∑' j : ℤ,
          ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
      intro m2 hm2 m2' hm2'
      simpa only [ftilde] using hpairInt m2 hm2 m2' hm2'
    symm
    calc
      (∫ u : ℝ, f u * A u) =
          ∫ u : ℝ, ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
            f u * ∑' j : ℤ,
              ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j) := by
        apply integral_congr_ae
        filter_upwards with u
        by_cases hfu : f u = 0
        · simp [hfu]
        · rw [← show (∑ m2 ∈ mRange, ∑ m2' ∈ mRange, ∑' j : ℤ,
              ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) = A u by
            simpa only [A, sourceAffineCenter] using
              sourceAffineTsum_eq_finite mRange mRange jRange ftilde u
                (hcover u hfu)]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m2 hm2
          rw [Finset.mul_sum]
      _ = ∑ m2 ∈ mRange, ∫ u : ℝ, ∑ m2' ∈ mRange,
            f u * ∑' j : ℤ,
              ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j) := by
        apply integral_finsetSum
        intro m2 hm2
        exact integrable_finset_sum mRange fun m2' hm2' =>
          htermInt m2 hm2 m2' hm2'
      _ = ∑ m2 ∈ mRange, ∑ m2' ∈ mRange, ∫ u : ℝ,
            f u * ∑' j : ℤ,
              ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j) := by
        apply Finset.sum_congr rfl
        intro m2 hm2
        exact integral_finsetSum mRange fun m2' hm2' =>
          htermInt m2 hm2 m2' hm2'
      _ = ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          sourceAffinePairMass mRange T psi f m2 m2' := by
        rfl
  have hI0 : 0 ≤ ∫ u : ℝ, f u * A u := by
    exact integral_nonneg fun u => mul_nonneg (hf0 u) (by
      unfold A sourceFiniteAffineSum
      exact Finset.sum_nonneg fun m1 hm1 =>
        Finset.sum_nonneg fun m2 hm2 =>
          Finset.sum_nonneg fun j hj => hftilde0 _)
  have hIsq :
      (∫ u : ℝ, f u * A u) ^ 2 ≤
        (∫ u : ℝ, f u ^ 2) * sourceAffineJ configs ftilde := by
    have hsquare := sourceAffinePairIntegral_sq_le_sourceAffineJ
        mRange jRange f ftilde configs hconfig hbounded hcover
        hfmeas hameas hf2 ha2 hf0 hftilde0
    have hintegral :
        (∫ u : ℝ, f u *
          (∑ m1 ∈ mRange, ∑ m2 ∈ mRange, ∑' j : ℤ,
            ftilde (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)))) =
          ∫ u : ℝ, f u * A u := by
      apply integral_congr_ae
      filter_upwards with u
      by_cases hfu : f u = 0
      · simp [hfu]
      · rw [sourceAffineTsum_eq_finite mRange mRange jRange ftilde u
          (hcover u hfu)]
    rw [hintegral] at hsquare
    exact hsquare
  have hI :
      (∫ u : ℝ, f u * A u) ≤
        Real.sqrt ((∫ u : ℝ, f u ^ 2) * sourceAffineJ configs ftilde) := by
    exact (Real.le_sqrt hI0
      (le_trans (sq_nonneg _) hIsq)).2 hIsq
  have hmassSum :
      (∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        D * sourceAffinePairMass mRange T psi f m2 m2') ≤
        D * Real.sqrt ((∫ u : ℝ, f u ^ 2) *
          sourceAffineJ configs ftilde) := by
    rw [show (∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        D * sourceAffinePairMass mRange T psi f m2 m2') =
      D * (∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        sourceAffinePairMass mRange T psi f m2 m2') by
          simp only [Finset.mul_sum]]
    rw [hglobalEq]
    exact mul_le_mul_of_nonneg_left hI (by
      dsimp only [D]
      positivity)
  calc
    sigmaIIFinite ellRange mRange psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau ≤
      ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
        (D * sourceAffinePairMass mRange T psi f m2 m2' +
          |(m2 : ℝ) * (m2' : ℝ)| * tailMass) := hsumBound
    _ = (∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          D * sourceAffinePairMass mRange T psi f m2 m2') +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| * tailMass := by
      simp only [Finset.sum_add_distrib]
    _ ≤ D * Real.sqrt ((∫ u : ℝ, f u ^ 2) *
          sourceAffineJ configs ftilde) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| * tailMass := by
      exact add_le_add hmassSum le_rfl
    _ = _ := by rfl

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.affineSmoothing_nonneg
#print axioms GuthMaynardJIteration.sourceAffinePairMass_nonneg
#print axioms GuthMaynardJIteration.sigmaIIFinite_le_affineJ_sqrt_add_time_neg100
