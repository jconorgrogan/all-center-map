import GuthMaynardLemma92SecondPoissonAbsorption
import GuthMaynardLemma92SubsetWeld

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardJIteration

/-!
# Source-compatible selected-range Lemma 9.2 endpoint

The affine smoothing radius is `B=T^δ`, while the Fourier decay order `q`
is left free.  The scalar budget is discharged by the exact constant from
`GuthMaynardLemma92SecondPoissonAbsorption`; the output uses the common
canonical `J` over the entire positive dyadic universe.
-/

/-- Source-faithful selected-range endpoint with no scalar-budget premise.
The only eventual-size input is the single threshold absorbing the fixed
Fourier seminorm and integer quadratic mass. -/
theorem sigmaIIFinite_selectedPositiveDyadic_concreteBumps_delta_le
    {T S F delta Ctau : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (q : ℕ) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4) (hCtau : 0 ≤ Ctau)
    (hthreshold : 25 * sourceLemma92Decay q * integerQuadraticMass ≤
      T ^ (delta * (q : ℝ) - 107)) :
    sigmaIIFinite (sourceBumpEllRange M T 1) mRange
          (fun x => sourceBump 1 zero_lt_one x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T (M : ℝ) Ctau ≤
        ((2 * Ctau * sourceLemma92Sup0) * (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F (2 * T ^ delta)))
              (affineSmoothing T
                (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau)) *
              (sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100))
      ∧ sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100 ≤
        T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hBpos : 0 < T ^ delta := Real.rpow_pos_of_pos hTpos delta
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hY : 0 ≤ 4 * (M : ℝ) * F := by positivity
  have hM3 : (M : ℝ) ≠ 0 := hMreal.ne'
  obtain ⟨hKdec, hKsup, hdecay2, hdecay, hFourierSup⟩ :=
    sourceLemma92ConcreteFourierPackage q
  have hbudget := sourceLemma92SecondPoissonCDelta_budget
    (T := T) (F := F) (delta := delta) (M := M) (q := q) hTpos
  let psi : ℝ → ℝ := fun z => sourceBump (T ^ delta) hBpos z
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  let jRange : Finset ℤ := sourceLemma92JRange M T F (2 * T ^ delta)
  have hp : SourceLemma92ProfilePremises T S F (2 * T ^ delta) (M : ℝ)
      (T ^ delta) f psi M :=
    sourceLemma92_profilePremises_sourceBump hTpos hf hBpos hM
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
    sourceBump_support_on_sourceBumpEllRange hM hTpos zero_lt_one
  have hret : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (sigmaIIZPairRetainedKernel
        (fun x => sourceBump 1 zero_lt_one x) f
        (M : ℝ) T (M : ℝ) Ctau (T ^ delta) m2 m2')
        (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairRetainedKernel_of_budget
      (sourceBumpEllRange M T 1) (fun x => sourceBump 1 zero_lt_one x) f
      hf.integrable (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) q hKdec hMreal hTpos
      hBpos hY hM3 hCtau hdecay2 hdecay hbudget m2 m2'
      (hy m2 hm2 m2' hm2') hsupport
  have htail : ∀ m2 ∈ mRange, ∀ m2' ∈ mRange,
      Integrable (sigmaIIZPairTailKernel
        (fun x => sourceBump 1 zero_lt_one x) f
        (M : ℝ) T (M : ℝ) Ctau (T ^ delta) m2 m2')
        (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairTailKernel_of_budget
      (M3 := (M : ℝ)) (fun x => sourceBump 1 zero_lt_one x) f
      hf.integrable (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) q hKdec hMreal hTpos
      hBpos hY hCtau hdecay hbudget m2 m2' (hy m2 hm2 m2' hm2')
  have hftildeCont : Continuous ftilde := by
    apply continuous_affineSmoothing hTpos psi f
    · intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (sourceBump_nonneg (T ^ delta) hBpos z)]
      exact sourceBump_le_one (T ^ delta) hBpos z
    · exact (sourceBump_contDiff (T ^ delta) hBpos).continuous
    · exact hf.integrable
  have hftildeSq : Integrable (fun u => ftilde u ^ 2) := by
    exact integrable_sq_affineSmoothing hTpos psi f
      (sourceBump_nonneg (T ^ delta) hBpos) hf.nonneg
      (sourceBump (T ^ delta) hBpos).integrable hf.integrable
      hf.squareIntegrable
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
    hMreal hTpos hBpos hY hM3 hCtau (show 0 ≤ (2 : ℝ) by norm_num)
    hf.nonneg (sourceBump_nonneg (T ^ delta) hBpos)
    hdecay2 hdecay hFourierSup hbudget hsupport
    (fun m hm => by
      exact_mod_cast sourcePositiveDyadicRange_pos hM (hmem hm))
    (fun m hm => by
      simpa using (sourcePositiveDyadicRange_abs_bounds hM (hmem hm)).2)
    hy
    (fun m hm =>
      sourceBump_majorizes_sourcePositiveDyadic_localization hM hBpos
        m (hmem hm))
    (fun m2 hm2 m2' hm2' u j =>
      hp.localIntegrable m2 (hmem hm2) m2' (hmem hm2') u j)
    (fun m2 hm2 m2' hm2' u j =>
      hp.affineSmooth m2 (hmem hm2) m2' (hmem hm2') u j)
    (fun m2 hm2 m2' hm2' u =>
      hp.summable m2 (hmem hm2) m2' (hmem hm2') u)
    hret htail
    (fun m2 hm2 m2' hm2' =>
      hp.pairMajorantIntegrable
        ((2 * Ctau * sourceLemma92Sup0) / (M : ℝ))
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
  have hA : 0 ≤
      (2 * Ctau * sourceLemma92Sup0) * (2 : ℝ) ^ 2 * (M : ℝ) := by
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
        ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) *
          (sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100))))
  constructor
  · simpa only [psi, ftilde, jRange] using hfinal
  · exact sourceLemma92SecondPoissonCDelta_div_time100_le
      hT hM hMhi hF0 hF hthreshold

#print axioms GuthMaynardJIteration.sigmaIIFinite_selectedPositiveDyadic_concreteBumps_delta_le

end GuthMaynardJIteration
