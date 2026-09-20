import GuthMaynardLemma92ConcreteBump
import GuthMaynardJIterationCanonicalSupremum

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardJIteration

/-!
# Selected-range weld for Lemma 9.2

The source `J` is a supremum over selected affine branches.  Consequently the
second-Poisson estimate must hold for every selected `m₂` range inside the
positive dyadic universe, rather than only for the full universe.  This file
closes that finite-range seam without using monotonicity of `SigmaII` (which is
false in general because the inner sums retain cancellation).
-/

/-- Enlarging both finite universes enlarges the canonical finite affine
supremum.  This follows branch by branch; it does not use a monotonicity claim
for the underlying squared sums. -/
theorem sourceAffineJ_mono_universe
    {mRange mUniverse jRange jUniverse : Finset ℤ} {f : ℝ → ℝ}
    (hm : mRange ⊆ mUniverse) (hj : jRange ⊆ jUniverse) :
    sourceAffineJ (sourceAffineConfigs mRange jRange) f ≤
      sourceAffineJ (sourceAffineConfigs mUniverse jUniverse) f := by
  apply sourceAffineJ_le_of_forall_config
  intro cfg hcfg
  rw [mem_sourceAffineConfigs_iff] at hcfg
  exact sourceFiniteAffineEnergy_le_canonicalJ mUniverse jUniverse f
    (hcfg.1.trans hm) (hcfg.2.1.trans hm) (hcfg.2.2.trans hj)

/-- Concrete Lemma 9.2 for an arbitrary selected `m₂` range inside the
positive dyadic universe.  The right side is measured against the one common
canonical `J` over the full universe, exactly as needed when taking the source
supremum over finite affine branches.

The only remaining analytic input is the displayed scalar second-Poisson
budget. -/
theorem exists_sigmaIIFinite_selectedPositiveDyadic_concreteBumps_le
    {T S F B C Ctau : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (hT : 0 < T) (hF : 0 ≤ F) (hB : 0 < B)
    (hCtau : 0 ≤ Ctau) (q : ℕ) :
    ∃ Kdec Ksup : ℝ,
      0 ≤ Kdec ∧ 0 ≤ Ksup ∧
      (((T / (M : ℝ)) * Kdec *
          ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
            max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
          C * B ^ q) →
        sigmaIIFinite (sourceBumpEllRange M T 1) mRange
            (fun x => sourceBump 1 zero_lt_one x)
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            (M : ℝ) T (M : ℝ) Ctau ≤
          ((2 * Ctau * Ksup) * (2 : ℝ) ^ 2 * (M : ℝ)) *
            Real.sqrt ((∫ u : ℝ, f u ^ 2) *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F (2 * B)))
                (affineSmoothing T (fun z => sourceBump B hB z) f)) +
          ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
            |(m2 : ℝ) * (m2' : ℝ)| *
              ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) *
                (C / T ^ 100))) := by
  obtain ⟨K0, Kdec, Ksup, hKdec, hKsup, hdecay2, hdecay,
      hFourierSup⟩ := exists_sourceBump_fourier_package 1 zero_lt_one q
  refine ⟨Kdec, Ksup, hKdec, hKsup, ?_⟩
  intro hbudget
  let psi : ℝ → ℝ := fun z => sourceBump B hB z
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  let jRange : Finset ℤ := sourceLemma92JRange M T F (2 * B)
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hY : 0 ≤ 4 * (M : ℝ) * F := by positivity
  have hM3 : (M : ℝ) ≠ 0 := hMreal.ne'
  have hp : SourceLemma92ProfilePremises T S F (2 * B) (M : ℝ) B f
      psi M := sourceLemma92_profilePremises_sourceBump hT hf hB hM
  have hmem {m : ℤ} (hm : m ∈ mRange) :
      m ∈ sourcePositiveDyadicRange M := hmRange hm
  have hy : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange, ∀ z : ℝ × ℝ,
      f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ 4 * (M : ℝ) * F := by
    intro m2 hm2 m2' hm2' z hz
    exact sourceLemma92_determinant_le_four_mul hf hM
      (hmem hm2) (hmem hm2') z hz
  have hsupport : ∀ ell : ℤ,
      ell ∉ sourceBumpEllRange M T 1 →
        sourceBump 1 zero_lt_one ((M : ℝ) * (ell : ℝ) / T) = 0 :=
    sourceBump_support_on_sourceBumpEllRange hM hT zero_lt_one
  have hret : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (sigmaIIZPairRetainedKernel
        (fun x => sourceBump 1 zero_lt_one x) f
        (M : ℝ) T (M : ℝ) Ctau B m2 m2')
        (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairRetainedKernel_of_budget
      (sourceBumpEllRange M T 1) (fun x => sourceBump 1 zero_lt_one x) f
      hf.integrable (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) q hKdec hMreal hT hB hY
      hM3 hCtau hdecay2 hdecay hbudget m2 m2' (hy m2 hm2 m2' hm2')
      hsupport
  have htail : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (sigmaIIZPairTailKernel
        (fun x => sourceBump 1 zero_lt_one x) f
        (M : ℝ) T (M : ℝ) Ctau B m2 m2')
        (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairTailKernel_of_budget
      (M3 := (M : ℝ)) (fun x => sourceBump 1 zero_lt_one x) f
      hf.integrable (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) q hKdec hMreal hT hB hY
      hCtau hdecay hbudget m2 m2' (hy m2 hm2 m2' hm2')
  have hftildeCont : Continuous ftilde := by
    apply continuous_affineSmoothing hT psi f
    · intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (sourceBump_nonneg B hB z)]
      exact sourceBump_le_one B hB z
    · exact (sourceBump_contDiff B hB).continuous
    · exact hf.integrable
  have hftildeSq : Integrable (fun u => ftilde u ^ 2) := by
    exact integrable_sq_affineSmoothing hT psi f
      (sourceBump_nonneg B hB) hf.nonneg (sourceBump B hB).integrable
      hf.integrable hf.squareIntegrable
  have hameas : AEStronglyMeasurable
      (sourceFiniteAffineSum mRange mRange jRange ftilde) :=
    (continuous_sourceFiniteAffineSum mRange mRange jRange ftilde
      hftildeCont).aestronglyMeasurable
  have ha2 : Integrable (fun u =>
      (sourceFiniteAffineSum mRange mRange jRange ftilde u) ^ 2) := by
    exact integrable_sq_sourceFiniteAffineSum mRange mRange jRange ftilde
      hftildeCont hftildeSq
      (fun m hm => sourcePositiveDyadicRange_ne_zero hM (hmem hm))
      (fun m hm => sourcePositiveDyadicRange_ne_zero hM (hmem hm))
  have hsmall := sigmaIIFinite_le_canonicalAffineJ_sqrt_add_time_neg100
    f (fun x => sourceBump 1 zero_lt_one x) psi hf.integrable
    (sourceBumpEllRange M T 1) mRange jRange
    (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
    (sourceBump_complex_contDiff 1 zero_lt_one) q hKdec hKsup
    hMreal hT hB hY hM3 hCtau (show 0 ≤ (2 : ℝ) by norm_num)
    hf.nonneg (sourceBump_nonneg B hB) hdecay2 hdecay hFourierSup
    hbudget hsupport
    (fun m hm => by
      exact_mod_cast sourcePositiveDyadicRange_pos hM (hmem hm))
    (fun m hm => by
      simpa using (sourcePositiveDyadicRange_abs_bounds hM (hmem hm)).2)
    hy
    (fun m hm =>
      sourceBump_majorizes_sourcePositiveDyadic_localization hM hB
        m (hmem hm))
    (fun m2 hm2 m2' hm2' u j =>
      hp.localIntegrable m2 (hmem hm2) m2' (hmem hm2') u j)
    (fun m2 hm2 m2' hm2' u j =>
      hp.affineSmooth m2 (hmem hm2) m2' (hmem hm2') u j)
    (fun m2 hm2 m2' hm2' u =>
      hp.summable m2 (hmem hm2) m2' (hmem hm2') u)
    hret htail
    (fun m2 hm2 m2' hm2' =>
      hp.pairMajorantIntegrable ((2 * Ctau * Ksup) / (M : ℝ))
        m2 (hmem hm2) m2' (hmem hm2'))
    (fun m2 hm2 m2' hm2' =>
      hp.pairMassIntegrable m2 (hmem hm2) m2' (hmem hm2'))
    (fun u hu m1 hm1 m2 hm2 j hj =>
      hp.cover u hu m1 (hmem hm1) m2 (hmem hm2) j hj)
    hf.integrable.aestronglyMeasurable hameas hf.squareIntegrable ha2
  have hJ : sourceAffineJ (sourceAffineConfigs mRange jRange) ftilde ≤
      sourceAffineJ
        (sourceAffineConfigs (sourcePositiveDyadicRange M) jRange)
        ftilde := sourceAffineJ_mono_universe hmRange Finset.Subset.rfl
  have hI : 0 ≤ ∫ u : ℝ, f u ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hA : 0 ≤ (2 * Ctau * Ksup) * (2 : ℝ) ^ 2 * (M : ℝ) := by
    positivity
  have hsqrt : Real.sqrt ((∫ u : ℝ, f u ^ 2) *
        sourceAffineJ (sourceAffineConfigs mRange jRange) ftilde) ≤
      Real.sqrt ((∫ u : ℝ, f u ^ 2) *
        sourceAffineJ
          (sourceAffineConfigs (sourcePositiveDyadicRange M) jRange)
          ftilde) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hJ hI)
  have hfinal := hsmall.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left hsqrt hA)
    (∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
      |(m2 : ℝ) * (m2' : ℝ)| *
        ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100))))
  simpa only [psi, ftilde, jRange] using hfinal

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceAffineJ_mono_universe
#print axioms GuthMaynardJIteration.exists_sigmaIIFinite_selectedPositiveDyadic_concreteBumps_le
