import GuthMaynardJIterationCanonicalSigmaII
import GuthMaynardAffineSmoothingNorms
import GuthMaynardAffineCrudeBound
import GuthMaynardSourceDyadicRanges
import GuthMaynardLemma92KernelIntegrability

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The literal support-driven integer window for the positive dyadic
`m₂,m₂'` branch of Lemma 9.2. -/
def sourceLemma92JRange (M : ℕ) (T F R : ℝ) : Finset ℤ :=
  sourceIntegerWindow 0 ((2 * (M : ℝ)) * (F + R / T + F))

/-- The local mass in every second-Poisson fiber is integrable solely from the
source profile's `L¹` hypothesis. -/
theorem sourceLemma92_localIntegrable
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    (m2 m2' : ℤ) (u : ℝ) (j : ℤ) {M2 B : ℝ} :
    IntegrableOn (fun u' => T * f u')
      {u' | |(j : ℝ) - (m2' : ℝ) * u' + (m2 : ℝ) * u| ≤
        (M2 / T) * B} :=
  (hf.integrable.const_mul T).integrableOn

/-- Every literal affine-smoothing section is integrable under the source
profile and smoothing-kernel packages. -/
theorem sourceLemma92_affineSmoothingSectionIntegrable
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    (m2 m2' : ℤ) (u : ℝ) (j : ℤ) :
    Integrable (fun u' => T * psi (T *
      (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j - u')) * f u') := by
  apply integrable_affineSmoothing_section hT psi f hpsi.integrable hf.continuous
    hf.bound_nonneg
  intro u'
  rw [abs_of_nonneg (hf.nonneg u')]
  exact hf.bounded u'

/-- Compact support of the smoothed profile makes the affine integer series
summable for every positive dyadic denominator. -/
theorem sourceLemma92_affineSeriesSummable
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2' : m2' ∈ sourcePositiveDyadicRange M) (u : ℝ) :
    Summable (fun j : ℤ => affineSmoothing T psi f
      (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  exact summable_affineSmoothing_sourceAffineCenter hT psi f hpsi.supported
    hf.supported (sourcePositiveDyadicRange_ne_zero hM hm2') u

/-- The exact finite `j` cover used at TeX 1657 for the positive dyadic
branch. -/
theorem sourceLemma92_supportCover
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) {u : ℝ} (hu : f u ≠ 0)
    {m1 m2 j : ℤ}
    (hm1 : m1 ∈ sourcePositiveDyadicRange M)
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hnonzero : affineSmoothing T psi f
      (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0) :
    j ∈ sourceLemma92JRange M T F R := by
  have hm1hi : |(m1 : ℝ)| ≤ 2 * (M : ℝ) := by
    simpa using (sourcePositiveDyadicRange_abs_bounds hM hm1).2
  have hm2hi : |(m2 : ℝ)| ≤ 2 * (M : ℝ) := by
    simpa using (sourcePositiveDyadicRange_abs_bounds hM hm2).2
  have hj := affineSmoothing_support_implies_j_mem_window hT psi f
    hpsi.supported hf.supported (show 0 ≤ 2 * (M : ℝ) by positivity)
    (hf.supported u hu) (sourcePositiveDyadicRange_ne_zero hM hm2)
    hm1hi hm2hi hnonzero
  simpa only [sourceLemma92JRange] using hj

/-- An individual affine translate of the smoothed profile is integrable for
positive dyadic numerator and denominator.  The proof keeps the exact affine
Jacobian inside mathlib's change-of-variables theorem. -/
theorem integrable_affineSmoothing_sourceAffineCenter
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hm2' : m2' ∈ sourcePositiveDyadicRange M) (j : ℤ) :
    Integrable (fun u => affineSmoothing T psi f
      (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  have hftilde : Integrable ftilde :=
    (sourceAdmissibleProfile_affineSmoothing hT psi f hf hpsi).integrable
  have hm2R : (m2 : ℝ) ≠ 0 := by
    exact_mod_cast sourcePositiveDyadicRange_ne_zero hM hm2
  have hm2'R : (m2' : ℝ) ≠ 0 := by
    exact_mod_cast sourcePositiveDyadicRange_ne_zero hM hm2'
  have h := (hftilde.comp_add_left ((j : ℝ) / (m2' : ℝ))).comp_mul_left'
    (div_ne_zero hm2R hm2'R)
  convert h using 1
  funext u
  dsimp only [ftilde, sourceAffineCenter]
  congr 2
  field_simp [hm2'R]
  ring

/-- The pair mass used in (9.11)--(9.12) is automatically integrable.  Compact
support first turns the literal `ℤ`-sum into the exact source window; the
resulting finite affine sum is `L¹`, and the original profile is bounded. -/
theorem sourceLemma92_pairMassIntegrable
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hm2' : m2' ∈ sourcePositiveDyadicRange M) :
    Integrable (fun u : ℝ => f u *
      ∑' j : ℤ, affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  let J : Finset ℤ := sourceLemma92JRange M T F R
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  let A : ℝ → ℝ := fun u => ∑ j ∈ J,
    ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)
  have hterm : ∀ j ∈ J, Integrable (fun u =>
      ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
    intro j hj
    exact integrable_affineSmoothing_sourceAffineCenter hT hf hpsi hM
      hm2 hm2' j
  have hA : Integrable A := by
    dsimp only [A]
    exact integrable_finsetSum J fun j hj => hterm j hj
  have hfBound : ∀ᵐ u : ℝ ∂volume, ‖f u‖ ≤ S := by
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (hf.nonneg u)]
    exact hf.bounded u
  have hprod : Integrable (fun u => f u * A u) :=
    hA.bdd_mul hf.continuous.aestronglyMeasurable hfBound
  apply hprod.congr
  filter_upwards with u
  by_cases hfu : f u = 0
  · simp [hfu]
  · congr 1
    dsimp only [A]
    symm
    apply tsum_eq_sum
    intro j hj
    by_contra hnonzero
    apply hj
    exact sourceLemma92_supportCover hT hf hpsi hM hfu hm2 hm2'
      (by simpa only [sourceAffineCenter, ftilde] using hnonzero)

/-- Any fixed scalar multiple of the pair mass is integrable.  Instantiating
the scalar with `(2*Ctau*Ksup)/M2` gives the exact `hmajor` premise. -/
theorem sourceLemma92_pairMajorantIntegrable
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hm2' : m2' ∈ sourcePositiveDyadicRange M) (a : ℝ) :
    Integrable (fun u : ℝ => a * f u *
      ∑' j : ℤ, affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  have h := (sourceLemma92_pairMassIntegrable hT hf hpsi hM hm2 hm2').const_mul a
  convert h using 1
  funext u
  ring

/-- Literal determinant-window bound from the profile support and the positive
dyadic ranges.  Thus the usual choice `Y = 4*M*F` is not an additional
analytic hypothesis. -/
theorem sourceLemma92_determinant_le_four_mul
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hm2' : m2' ∈ sourcePositiveDyadicRange M)
    (z : ℝ × ℝ) (hz : f z.1 * f z.2 ≠ 0) :
    |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ 4 * (M : ℝ) * F := by
  have hz1 : f z.1 ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  have hz2 : f z.2 ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  have hm2hi := (sourcePositiveDyadicRange_abs_bounds hM hm2).2
  have hm2'hi := (sourcePositiveDyadicRange_abs_bounds hM hm2').2
  calc
    |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤
        |(m2' : ℝ) * z.2| + |(m2 : ℝ) * z.1| := abs_sub _ _
    _ = |(m2' : ℝ)| * |z.2| + |(m2 : ℝ)| * |z.1| := by
      rw [abs_mul, abs_mul]
    _ ≤ (2 * (M : ℝ)) * F + (2 * (M : ℝ)) * F := by
      exact add_le_add
        (mul_le_mul hm2'hi (hf.supported z.2 hz2) (abs_nonneg _)
          (show 0 ≤ 2 * (M : ℝ) by positivity))
        (mul_le_mul hm2hi (hf.supported z.1 hz1) (abs_nonneg _)
          (show 0 ≤ 2 * (M : ℝ) by positivity))
    _ = 4 * (M : ℝ) * F := by ring

/-- All elementary regularity and finite-energy premises in the canonical
Lemma 9.2 producer, before the product-space retained/tail kernels enter. -/
theorem sourceLemma92_elementaryProfilePremises
    {T S F R : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) :
    (AEStronglyMeasurable f) ∧
    (AEStronglyMeasurable
      (sourceFiniteAffineSum (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceLemma92JRange M T F R)
        (affineSmoothing T psi f))) ∧
    (Integrable (fun u => f u ^ 2)) ∧
    (Integrable (fun u =>
      sourceFiniteAffineSum (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceLemma92JRange M T F R)
        (affineSmoothing T psi f) u ^ 2)) := by
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  have hftilde : SourceAdmissibleProfile T S (F + R / T) ftilde := by
    exact sourceAdmissibleProfile_affineSmoothing hT psi f hf hpsi
  refine ⟨hf.integrable.aestronglyMeasurable, ?_, hf.squareIntegrable, ?_⟩
  · exact (continuous_sourceFiniteAffineSum
      (sourcePositiveDyadicRange M) (sourcePositiveDyadicRange M)
      (sourceLemma92JRange M T F R) ftilde hftilde.continuous).aestronglyMeasurable
  · exact integrable_sq_sourceFiniteAffineSum
      (sourcePositiveDyadicRange M) (sourcePositiveDyadicRange M)
      (sourceLemma92JRange M T F R) ftilde hftilde.continuous
      hftilde.squareIntegrable
      (fun m hm => sourcePositiveDyadicRange_ne_zero hM hm)
      (fun m hm => sourcePositiveDyadicRange_ne_zero hM hm)

/-- The full source-profile side of the canonical Lemma 9.2 producer.  This
packages every regularity/integrability premise which is independent of the
retained and discarded product-space Poisson kernels. -/
structure SourceLemma92ProfilePremises
    (T S F R M2 B : ℝ) (f psi : ℝ → ℝ) (M : ℕ) : Prop where
  localIntegrable : ∀ m2 ∈ sourcePositiveDyadicRange M,
    ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ u : ℝ, ∀ j : ℤ,
      IntegrableOn (fun u' => T * f u')
        {u' | |(j : ℝ) - (m2' : ℝ) * u' + (m2 : ℝ) * u| ≤
          (M2 / T) * B}
  affineSmooth : ∀ m2 ∈ sourcePositiveDyadicRange M,
    ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ u : ℝ, ∀ j : ℤ,
      Integrable (fun u' => T * psi (T *
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j - u')) * f u')
  summable : ∀ m2 ∈ sourcePositiveDyadicRange M,
    ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ u : ℝ,
      Summable (fun j : ℤ => affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j))
  cover : ∀ u, f u ≠ 0 →
    ∀ m1 ∈ sourcePositiveDyadicRange M,
    ∀ m2 ∈ sourcePositiveDyadicRange M, ∀ j : ℤ,
      affineSmoothing T psi f
        (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0 →
      j ∈ sourceLemma92JRange M T F R
  fMeasurable : AEStronglyMeasurable f
  affineSumMeasurable : AEStronglyMeasurable
    (sourceFiniteAffineSum (sourcePositiveDyadicRange M)
      (sourcePositiveDyadicRange M) (sourceLemma92JRange M T F R)
      (affineSmoothing T psi f))
  fSquareIntegrable : Integrable (fun u => f u ^ 2)
  affineSumSquareIntegrable : Integrable (fun u =>
    sourceFiniteAffineSum (sourcePositiveDyadicRange M)
      (sourcePositiveDyadicRange M) (sourceLemma92JRange M T F R)
      (affineSmoothing T psi f) u ^ 2)
  pairMassIntegrable : ∀ m2 ∈ sourcePositiveDyadicRange M,
    ∀ m2' ∈ sourcePositiveDyadicRange M,
      Integrable (fun u : ℝ => f u *
        ∑' j : ℤ, affineSmoothing T psi f
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j))
  pairMajorantIntegrable : ∀ a : ℝ,
    ∀ m2 ∈ sourcePositiveDyadicRange M,
    ∀ m2' ∈ sourcePositiveDyadicRange M,
      Integrable (fun u : ℝ => a * f u *
        ∑' j : ℤ, affineSmoothing T psi f
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j))

/-- `SourceAdmissibleProfile` and `SourceSmoothingKernel` discharge the entire
finite-profile regularity package for Lemma 9.2, with the literal positive
dyadic range and support window. -/
theorem sourceLemma92_profilePremises
    {T S F R M2 B : ℝ} {f psi : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) :
    SourceLemma92ProfilePremises T S F R M2 B f psi M := by
  have helem := sourceLemma92_elementaryProfilePremises hT hf hpsi hM
  refine
    { localIntegrable := ?_
      affineSmooth := ?_
      summable := ?_
      cover := ?_
      fMeasurable := helem.1
      affineSumMeasurable := helem.2.1
      fSquareIntegrable := helem.2.2.1
      affineSumSquareIntegrable := helem.2.2.2
      pairMassIntegrable := ?_
      pairMajorantIntegrable := ?_ }
  · intro m2 hm2 m2' hm2' u j
    exact sourceLemma92_localIntegrable hf m2 m2' u j
  · intro m2 hm2 m2' hm2' u j
    exact sourceLemma92_affineSmoothingSectionIntegrable hT hf hpsi m2 m2' u j
  · intro m2 hm2 m2' hm2' u
    exact sourceLemma92_affineSeriesSummable hT hf hpsi hM hm2' u
  · intro u hu m1 hm1 m2 hm2 j hj
    exact sourceLemma92_supportCover hT hf hpsi hM hu hm1 hm2 hj
  · intro m2 hm2 m2' hm2'
    exact sourceLemma92_pairMassIntegrable hT hf hpsi hM hm2 hm2'
  · intro a m2 hm2 m2' hm2'
    exact sourceLemma92_pairMajorantIntegrable hT hf hpsi hM hm2 hm2' a

/-- Source-facing Lemma 9.2 producer on the literal positive dyadic range.
All finite-profile and retained/tail integrability hypotheses of the canonical
producer have been discharged.  What remains in the signature is precisely
the quantitative Fourier decay/budget, support, determinant-window and
plateau input used by the analytic second-Poisson argument. -/
theorem sigmaIIFinite_sourcePositiveDyadic_le_canonicalAffineJ_sqrt_add_time_neg100
    (f psi2 psi : ℝ → ℝ)
    {T S F R B Y C M3 Ctau K0 Kdec Ksup : ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi)
    {M : ℕ} (hM : 0 < M) (ellRange : Finset ℤ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hpsi2smooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (q : ℕ) (hKdec : 0 ≤ Kdec) (hKsup : 0 ≤ Ksup)
    (hT : 0 < T) (hB : 0 < B) (hY : 0 ≤ Y)
    (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        Kdec / (1 + |xi|) ^ (q + 2))
    (hFourierSup : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤ Ksup)
    (hbudget :
      (T / (M : ℝ)) * Kdec *
        ((1 + Y / ((M : ℝ) / T)) ^ 2 *
          max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        C * B ^ q)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 ((M : ℝ) * (ell : ℝ) / T) = 0)
    (hy : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ z : ℝ × ℝ,
        f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y)
    (hpsi_major : ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ z,
      |z| ≤ ((M : ℝ) / (m2' : ℝ)) * B → 1 ≤ psi z) :
    sigmaIIFinite ellRange (sourcePositiveDyadicRange M) psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T M3 Ctau ≤
      ((2 * Ctau * Ksup) * (2 : ℝ) ^ 2 * (M : ℝ)) *
        Real.sqrt ((∫ u : ℝ, f u ^ 2) *
          sourceAffineJ
            (sourceAffineConfigs (sourcePositiveDyadicRange M)
              (sourceLemma92JRange M T F R))
            (affineSmoothing T psi f)) +
      ∑ m2 ∈ sourcePositiveDyadicRange M,
        ∑ m2' ∈ sourcePositiveDyadicRange M,
          |(m2 : ℝ) * (m2' : ℝ)| *
            ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100)) := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hp : SourceLemma92ProfilePremises T S F R (M : ℝ) B f psi M :=
    sourceLemma92_profilePremises hT hf hpsi hM
  have hret : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M,
      Integrable (sigmaIIZPairRetainedKernel psi2 f
        (M : ℝ) T M3 Ctau B m2 m2') (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairRetainedKernel_of_budget
      ellRange psi2 f hf.integrable hcompact hpsi2smooth q hKdec
      hMreal hT hB hY hM3 hCtau hdecay2 hdecay hbudget m2 m2'
      (hy m2 hm2 m2' hm2') hsupport
  have htail : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M,
      Integrable (sigmaIIZPairTailKernel psi2 f
        (M : ℝ) T M3 Ctau B m2 m2') (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact integrable_sigmaIIZPairTailKernel_of_budget
      (M3 := M3) psi2 f hf.integrable hcompact hpsi2smooth q hKdec
      hMreal hT hB hY hCtau hdecay hbudget m2 m2'
      (hy m2 hm2 m2' hm2')
  apply sigmaIIFinite_le_canonicalAffineJ_sqrt_add_time_neg100
    f psi2 psi hf.integrable ellRange (sourcePositiveDyadicRange M)
    (sourceLemma92JRange M T F R) hcompact hpsi2smooth q
    hKdec hKsup hMreal hT hB hY hM3 hCtau (show 0 ≤ (2 : ℝ) by norm_num)
    hf.nonneg hpsi.nonneg hdecay2 hdecay hFourierSup hbudget hsupport
    (fun m hm => by exact_mod_cast sourcePositiveDyadicRange_pos hM hm)
    (fun m hm => by
      simpa using (sourcePositiveDyadicRange_abs_bounds hM hm).2)
    hy hpsi_major hp.localIntegrable hp.affineSmooth hp.summable
    hret htail
    (fun m2 hm2 m2' hm2' =>
      hp.pairMajorantIntegrable ((2 * Ctau * Ksup) / (M : ℝ))
        m2 hm2 m2' hm2')
    hp.pairMassIntegrable hp.cover hp.fMeasurable hp.affineSumMeasurable
    hp.fSquareIntegrable hp.affineSumSquareIntegrable

#print axioms GuthMaynardJIteration.sourceLemma92_localIntegrable
#print axioms GuthMaynardJIteration.sourceLemma92_affineSmoothingSectionIntegrable
#print axioms GuthMaynardJIteration.sourceLemma92_affineSeriesSummable
#print axioms GuthMaynardJIteration.sourceLemma92_supportCover
#print axioms GuthMaynardJIteration.integrable_affineSmoothing_sourceAffineCenter
#print axioms GuthMaynardJIteration.sourceLemma92_pairMassIntegrable
#print axioms GuthMaynardJIteration.sourceLemma92_pairMajorantIntegrable
#print axioms GuthMaynardJIteration.sourceLemma92_determinant_le_four_mul
#print axioms GuthMaynardJIteration.sourceLemma92_elementaryProfilePremises
#print axioms GuthMaynardJIteration.sourceLemma92_profilePremises
#print axioms GuthMaynardJIteration.sigmaIIFinite_sourcePositiveDyadic_le_canonicalAffineJ_sqrt_add_time_neg100

end GuthMaynardJIteration
