import GuthMaynardLemma92ProfileRegularity
import GuthMaynardJIterationBumpWeld
import GuthMaynardLemma92EllWindowSupport

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardJIteration

/-!
# Concrete-bump specialization of the finite Lemma 9.2 producer

The Fourier cutoff and the affine smoothing kernel are both instantiated by
`sourceBump`.  The determinant window is the literal `4*M*F`, and the
`ell`-sum is restricted to the exact support-driven finite window.  The only
second-Poisson analytic premise left in the main theorem is its displayed
scalar budget.

The hypothesis `4 * B ≤ 1` is not a source estimate.  It is the exact cost of
the current `SourceSmoothingKernel.mass_le_one` interface when a kernel is
required to equal one on `[-B,B]`.  The final theorem names this restriction
explicitly rather than hiding it.
-/

/-- The concrete plateau bump has mass at most the length `4*B` of its outer
support interval. -/
theorem integral_sourceBump_le_four_mul
    {B : ℝ} (hB : 0 < B) :
    (∫ z : ℝ, sourceBump B hB z) ≤ 4 * B := by
  have hrestrict :
      (∫ z : ℝ, sourceBump B hB z) =
        ∫ z : ℝ in Set.Icc (-2 * B) (2 * B), sourceBump B hB z := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Set.Icc (-2 * B) (2 * B)
    · rw [Set.indicator_of_mem hz]
    · have hzabs : 2 * B ≤ |z| := by
        rw [Set.mem_Icc, not_and_or] at hz
        rcases hz with hz | hz
        · have : z < -2 * B := lt_of_not_ge hz
          rw [abs_of_neg (by linarith)]
          linarith
        · have : 2 * B < z := lt_of_not_ge hz
          rw [abs_of_pos (by linarith)]
          linarith
      rw [sourceBump_eq_zero_of_two_mul_le_abs B hB hzabs]
      simp only [Set.indicator, hz, if_false]
  rw [hrestrict]
  calc
    (∫ z : ℝ in Set.Icc (-2 * B) (2 * B), sourceBump B hB z) ≤
        ∫ _z : ℝ in Set.Icc (-2 * B) (2 * B), 1 := by
      apply MeasureTheory.integral_mono_ae
      · exact (sourceBump B hB).integrable.integrableOn
      · exact MeasureTheory.integrableOn_const (by simp [Real.volume_Icc])
      · filter_upwards with z
        exact sourceBump_le_one B hB z
    _ = 4 * B := by
      rw [MeasureTheory.setIntegral_const]
      rw [smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- Under the explicit small-mass condition, the same concrete plateau bump
is a `SourceSmoothingKernel` with its exact outer support radius `2*B`. -/
theorem sourceBump_sourceSmoothingKernel
    {B : ℝ} (hB : 0 < B) (hBmass : 4 * B ≤ 1) :
    SourceSmoothingKernel (2 * B) (fun z => sourceBump B hB z) := by
  refine
    { nonneg := sourceBump_nonneg B hB
      bounded := sourceBump_le_one B hB
      supported := ?_
      integrable := (sourceBump B hB).integrable
      continuous := (sourceBump_contDiff B hB).continuous
      mass_le_one := (integral_sourceBump_le_four_mul hB).trans hBmass }
  intro z hz
  apply le_of_not_gt
  intro hlt
  exact hz (sourceBump_eq_zero_of_two_mul_le_abs B hB hlt.le)

/-- The positive dyadic lower endpoint makes the radius-`B` plateau dominate
all localizations `|(M/m)z| ≤ B`: no extra dyadic-ratio premise remains. -/
theorem sourceBump_majorizes_sourcePositiveDyadic_localization
    {M : ℕ} (hM : 0 < M) {B : ℝ} (hB : 0 < B) :
    ∀ m ∈ sourcePositiveDyadicRange M, ∀ z,
      |z| ≤ ((M : ℝ) / (m : ℝ)) * B → 1 ≤ sourceBump B hB z := by
  apply sourceBump_majorizes_dyadic_localization
  intro m hm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast sourcePositiveDyadicRange_pos hM hm
  have hmlo : (M : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (mem_sourcePositiveDyadicRange_iff.mp hm).1
  have hratio : (M : ℝ) / (m : ℝ) ≤ 1 :=
    (div_le_one hmpos).2 hmlo
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hB.le

/-- Exact outer support of the concrete smoothing bump, without the unrelated
mass-normalization field of `SourceSmoothingKernel`. -/
theorem sourceBump_supported_two_mul
    {B : ℝ} (hB : 0 < B) {z : ℝ}
    (hz : sourceBump B hB z ≠ 0) : |z| ≤ 2 * B := by
  apply le_of_not_gt
  intro hlt
  exact hz (sourceBump_eq_zero_of_two_mul_le_abs B hB hlt.le)

/-- An affine translate of the concrete smoothing orbit is integrable on every
positive dyadic numerator/denominator branch. -/
theorem integrable_affineSmoothing_sourceAffineCenter_sourceBump
    {T S F B : ℝ} {f : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f) (hB : 0 < B)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hm2' : m2' ∈ sourcePositiveDyadicRange M) (j : ℤ) :
    Integrable (fun u => affineSmoothing T (fun z => sourceBump B hB z) f
      (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  let ftilde : ℝ → ℝ := affineSmoothing T (fun z => sourceBump B hB z) f
  have hftilde : Integrable ftilde :=
    integrable_affineSmoothing hT (sourceBump B hB).integrable hf.integrable
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

/-- The exact support-driven `j` cover for the concrete smoothing bump. -/
theorem sourceLemma92_supportCover_sourceBump
    {T S F B : ℝ} {f : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f) (hB : 0 < B)
    {M : ℕ} (hM : 0 < M) {u : ℝ} (hu : f u ≠ 0)
    {m1 m2 j : ℤ}
    (hm1 : m1 ∈ sourcePositiveDyadicRange M)
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hnonzero : affineSmoothing T (fun z => sourceBump B hB z) f
      (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0) :
    j ∈ sourceLemma92JRange M T F (2 * B) := by
  have hm1hi : |(m1 : ℝ)| ≤ 2 * (M : ℝ) := by
    simpa using (sourcePositiveDyadicRange_abs_bounds hM hm1).2
  have hm2hi : |(m2 : ℝ)| ≤ 2 * (M : ℝ) := by
    simpa using (sourcePositiveDyadicRange_abs_bounds hM hm2).2
  have hj := affineSmoothing_support_implies_j_mem_window hT
    (fun z => sourceBump B hB z) f
    (fun _ hz => sourceBump_supported_two_mul hB hz) hf.supported
    (show 0 ≤ 2 * (M : ℝ) by positivity)
    (hf.supported u hu) (sourcePositiveDyadicRange_ne_zero hM hm2)
    hm1hi hm2hi hnonzero
  simpa only [sourceLemma92JRange] using hj

/-- The pair mass remains integrable for the unnormalized concrete plateau
bump.  Only compact support, boundedness and integrability are used. -/
theorem sourceLemma92_pairMassIntegrable_sourceBump
    {T S F B : ℝ} {f : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f) (hB : 0 < B)
    {M : ℕ} (hM : 0 < M) {m2 m2' : ℤ}
    (hm2 : m2 ∈ sourcePositiveDyadicRange M)
    (hm2' : m2' ∈ sourcePositiveDyadicRange M) :
    Integrable (fun u : ℝ => f u *
      ∑' j : ℤ, affineSmoothing T (fun z => sourceBump B hB z) f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  let J : Finset ℤ := sourceLemma92JRange M T F (2 * B)
  let ftilde : ℝ → ℝ := affineSmoothing T (fun z => sourceBump B hB z) f
  let A : ℝ → ℝ := fun u => ∑ j ∈ J,
    ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)
  have hterm : ∀ j ∈ J, Integrable (fun u =>
      ftilde (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
    intro j hj
    exact integrable_affineSmoothing_sourceAffineCenter_sourceBump
      hT hf hB hM hm2 hm2' j
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
    exact sourceLemma92_supportCover_sourceBump hT hf hB hM hfu hm2 hm2'
      (by simpa only [sourceAffineCenter, ftilde] using hnonzero)

/-- Every finite-profile premise required by the canonical producer follows
from the literal concrete bump, with no mass-one normalization. -/
theorem sourceLemma92_profilePremises_sourceBump
    {T S F B M2 B0 : ℝ} {f : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f) (hB : 0 < B)
    {M : ℕ} (hM : 0 < M) :
    SourceLemma92ProfilePremises T S F (2 * B) M2 B0 f
      (fun z => sourceBump B hB z) M := by
  let psi : ℝ → ℝ := fun z => sourceBump B hB z
  let ftilde : ℝ → ℝ := affineSmoothing T psi f
  have hpsiInt : Integrable psi := (sourceBump B hB).integrable
  have hpsiCont : Continuous psi := (sourceBump_contDiff B hB).continuous
  have hftildeInt : Integrable ftilde :=
    integrable_affineSmoothing hT hpsiInt hf.integrable
  have hftildeCont : Continuous ftilde := by
    apply continuous_affineSmoothing hT psi f
    · intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (sourceBump_nonneg B hB z)]
      exact sourceBump_le_one B hB z
    · exact hpsiCont
    · exact hf.integrable
  have hftildeSq : Integrable (fun u => ftilde u ^ 2) := by
    exact integrable_sq_affineSmoothing hT psi f
      (sourceBump_nonneg B hB) hf.nonneg hpsiInt hf.integrable
      hf.squareIntegrable
  refine
    { localIntegrable := ?_
      affineSmooth := ?_
      summable := ?_
      cover := ?_
      fMeasurable := hf.integrable.aestronglyMeasurable
      affineSumMeasurable := ?_
      fSquareIntegrable := hf.squareIntegrable
      affineSumSquareIntegrable := ?_
      pairMassIntegrable := ?_
      pairMajorantIntegrable := ?_ }
  · intro m2 hm2 m2' hm2' u j
    exact sourceLemma92_localIntegrable hf m2 m2' u j
  · intro m2 hm2 m2' hm2' u j
    apply integrable_affineSmoothing_section hT psi f hpsiInt hf.continuous
      hf.bound_nonneg
    intro u'
    rw [abs_of_nonneg (hf.nonneg u')]
    exact hf.bounded u'
  · intro m2 hm2 m2' hm2' u
    exact summable_affineSmoothing_sourceAffineCenter hT psi f
      (fun _ hz => sourceBump_supported_two_mul hB hz) hf.supported
      (sourcePositiveDyadicRange_ne_zero hM hm2') u
  · intro u hu m1 hm1 m2 hm2 j hj
    exact sourceLemma92_supportCover_sourceBump hT hf hB hM hu hm1 hm2 hj
  · exact (continuous_sourceFiniteAffineSum
      (sourcePositiveDyadicRange M) (sourcePositiveDyadicRange M)
      (sourceLemma92JRange M T F (2 * B)) ftilde
      hftildeCont).aestronglyMeasurable
  · exact integrable_sq_sourceFiniteAffineSum
      (sourcePositiveDyadicRange M) (sourcePositiveDyadicRange M)
      (sourceLemma92JRange M T F (2 * B)) ftilde hftildeCont
      hftildeSq
      (fun m hm => sourcePositiveDyadicRange_ne_zero hM hm)
      (fun m hm => sourcePositiveDyadicRange_ne_zero hM hm)
  · intro m2 hm2 m2' hm2'
    exact sourceLemma92_pairMassIntegrable_sourceBump
      hT hf hB hM hm2 hm2'
  · intro a m2 hm2 m2' hm2'
    have h := (sourceLemma92_pairMassIntegrable_sourceBump
      hT hf hB hM hm2 hm2').const_mul a
    convert h using 1
    funext u
    ring

/-- Fully concrete positive-dyadic Lemma 9.2 producer.  The Fourier bump has
inner radius one and exact finite support window `|ell| ≤ 2T/M` (up to the
literal floor/ceiling convention).  The affine smoothing bump has plateau
radius `B`, so the dyadic lower bound `m ≥ M` discharges the localization
majorant.  The determinant range is exactly `Y = 4*M*F`.

The sole analytic premise after the source profile/scale hypotheses is the
explicit second-Poisson scalar budget shown below. -/
theorem exists_sigmaIIFinite_sourcePositiveDyadic_concreteBumps_le
    {T S F B C Ctau : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M)
    (hT : 0 < T) (hF : 0 ≤ F) (hB : 0 < B)
    (hCtau : 0 ≤ Ctau) (q : ℕ) :
    ∃ Kdec Ksup : ℝ,
      0 ≤ Kdec ∧ 0 ≤ Ksup ∧
      (((T / (M : ℝ)) * Kdec *
          ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
            max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
          C * B ^ q) →
        sigmaIIFinite (sourceBumpEllRange M T 1)
            (sourcePositiveDyadicRange M)
            (fun x => sourceBump 1 zero_lt_one x)
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            (M : ℝ) T (M : ℝ) Ctau ≤
          ((2 * Ctau * Ksup) * (2 : ℝ) ^ 2 * (M : ℝ)) *
            Real.sqrt ((∫ u : ℝ, f u ^ 2) *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F (2 * B)))
                (affineSmoothing T (fun z => sourceBump B hB z) f)) +
          ∑ m2 ∈ sourcePositiveDyadicRange M,
            ∑ m2' ∈ sourcePositiveDyadicRange M,
              |(m2 : ℝ) * (m2' : ℝ)| *
                ((∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) *
                  (C / T ^ 100))) := by
  obtain ⟨K0, Kdec, Ksup, hKdec, hKsup, hdecay2, hdecay, hFourierSup⟩ :=
    exists_sourceBump_fourier_package 1 zero_lt_one q
  refine ⟨Kdec, Ksup, hKdec, hKsup, ?_⟩
  intro hbudget
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hY : 0 ≤ 4 * (M : ℝ) * F := by positivity
  have hM3 : (M : ℝ) ≠ 0 := hMreal.ne'
  have hp : SourceLemma92ProfilePremises T S F (2 * B) (M : ℝ) B f
      (fun z => sourceBump B hB z) M :=
    sourceLemma92_profilePremises_sourceBump hT hf hB hM
  have hy : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M, ∀ z : ℝ × ℝ,
        f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ 4 * (M : ℝ) * F := by
    intro m2 hm2 m2' hm2' z hz
    exact sourceLemma92_determinant_le_four_mul hf hM hm2 hm2' z hz
  have hsupport : ∀ ell : ℤ,
      ell ∉ sourceBumpEllRange M T 1 →
        sourceBump 1 zero_lt_one ((M : ℝ) * (ell : ℝ) / T) = 0 :=
    sourceBump_support_on_sourceBumpEllRange hM hT zero_lt_one
  have hret : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M,
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
  have htail : ∀ m2 ∈ sourcePositiveDyadicRange M,
      ∀ m2' ∈ sourcePositiveDyadicRange M,
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
  apply sigmaIIFinite_le_canonicalAffineJ_sqrt_add_time_neg100
    f (fun x => sourceBump 1 zero_lt_one x)
      (fun z => sourceBump B hB z) hf.integrable
      (sourceBumpEllRange M T 1) (sourcePositiveDyadicRange M)
      (sourceLemma92JRange M T F (2 * B))
      (sourceBump_complex_hasCompactSupport 1 zero_lt_one)
      (sourceBump_complex_contDiff 1 zero_lt_one) q hKdec hKsup
      hMreal hT hB hY hM3 hCtau (show 0 ≤ (2 : ℝ) by norm_num)
      hf.nonneg (sourceBump_nonneg B hB) hdecay2 hdecay hFourierSup
      hbudget hsupport
      (fun m hm => by exact_mod_cast sourcePositiveDyadicRange_pos hM hm)
      (fun m hm => by
        simpa using (sourcePositiveDyadicRange_abs_bounds hM hm).2)
      hy (sourceBump_majorizes_sourcePositiveDyadic_localization hM hB)
      hp.localIntegrable hp.affineSmooth hp.summable hret htail
      (fun m2 hm2 m2' hm2' =>
        hp.pairMajorantIntegrable ((2 * Ctau * Ksup) / (M : ℝ))
          m2 hm2 m2' hm2')
      hp.pairMassIntegrable hp.cover hp.fMeasurable hp.affineSumMeasurable
      hp.fSquareIntegrable hp.affineSumSquareIntegrable

#print axioms GuthMaynardJIteration.integral_sourceBump_le_four_mul
#print axioms GuthMaynardJIteration.sourceBump_sourceSmoothingKernel
#print axioms GuthMaynardJIteration.sourceBump_majorizes_sourcePositiveDyadic_localization
#print axioms GuthMaynardJIteration.sourceBump_supported_two_mul
#print axioms GuthMaynardJIteration.integrable_affineSmoothing_sourceAffineCenter_sourceBump
#print axioms GuthMaynardJIteration.sourceLemma92_supportCover_sourceBump
#print axioms GuthMaynardJIteration.sourceLemma92_pairMassIntegrable_sourceBump
#print axioms GuthMaynardJIteration.sourceLemma92_profilePremises_sourceBump
#print axioms GuthMaynardJIteration.exists_sigmaIIFinite_sourcePositiveDyadic_concreteBumps_le

end GuthMaynardJIteration
