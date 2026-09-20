import GuthMaynardS3LiteralProfileFourier
import GuthMaynardS3LiteralAffineReduction
import GuthMaynardLemma92ConcreteBump

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3WideProfile

open GuthMaynardJIteration
open GuthMaynardS3LiteralProfile
open GuthMaynardRatioKernelIdentity
open GuthMaynardS3LiteralProfileFourier

/-- The uncut smoothed square which occurs in the literal affine fibers. -/
def wideProfile (B : ℝ) (W : Finset ℝ) : ℝ → ℝ :=
  smoothedRatioSquare B W

/-- The current outer-cut profile cannot be used pointwise on all affine
centres; this wide profile is the exact square of the smoothed ratio factor. -/
theorem wideProfile_eq_smoothedRatioSquare (B : ℝ) (W : Finset ℝ) :
    wideProfile B W = smoothedRatioSquare B W := rfl

theorem wideProfile_nonneg {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ wideProfile B W u := by
  exact smoothedRatioSquare_nonneg hB W u

theorem wideProfile_supported {B : ℝ} (hB4 : (4 : ℝ) ≤ B) (W : Finset ℝ)
    {u : ℝ} (hu : wideProfile B W u ≠ 0) : |u| ≤ 7 := by
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB4
  have hs := smoothedRatioSquare_supported hB W hu
  have hfrac : 2 / B ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hB).2
    nlinarith [hB4]
  have hs' : |u| ≤ 6 + (1 : ℝ) / 2 := by
    linarith
  linarith

/-- The uncut smoothed square has the correct `4|W|²` height.  The factor 4
comes only from the literal mass bound of the unit source bump. -/
theorem wideProfile_bounded {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    wideProfile B W u ≤ 4 * (W.card : ℝ) ^ 2 := by
  let psi4 : ℝ → ℝ := fun z => sourceBump 1 zero_lt_one z / 4
  have hpsi0 : ∀ z, 0 ≤ psi4 z := by
    intro z
    dsimp [psi4]
    exact div_nonneg (sourceBump_nonneg 1 zero_lt_one z) (by norm_num)
  have hmass4 : ∫ z : ℝ, psi4 z ≤ 1 := by
    have hmass := integral_sourceBump_le_four_mul (B := (1 : ℝ)) zero_lt_one
    dsimp [psi4]
    rw [show (fun z : ℝ => sourceBump 1 zero_lt_one z / 4) =
        (fun z : ℝ => (1 / 4 : ℝ) * sourceBump 1 zero_lt_one z) by
          funext z; ring]
    rw [integral_const_mul]
    nlinarith
  have hpsiInt : Integrable psi4 := by
    have hbInt : Integrable (sourceBump 1 zero_lt_one) :=
      (sourceBump 1 zero_lt_one).integrable
    have hbScaled := hbInt.const_mul (1 / 4 : ℝ)
    have heq : psi4 = (fun z : ℝ => (1 / 4 : ℝ) * sourceBump 1 zero_lt_one z) := by
      funext z
      dsimp [psi4]
      ring
    rw [heq]
    exact hbScaled
  have hpsiCont : Continuous psi4 := by
    dsimp [psi4]
    exact (sourceBump_contDiff 1 zero_lt_one).continuous.div_const 4
  have hprofCont : Continuous (ratioProfile W) := ratioProfile_continuous W
  have hprofInt : Integrable (ratioProfile W) := ratioProfile_integrable W
  have hprof0 : ∀ x, 0 ≤ ratioProfile W x := ratioProfile_nonneg W
  have hprofLe : ∀ x, ratioProfile W x ≤ (W.card : ℝ) ^ 2 :=
    fun x => ratioProfile_le_card_sq W x
  have hcard0 : 0 ≤ (W.card : ℝ) ^ 2 := by positivity
  have hscaled : affineSmoothing B psi4 (ratioProfile W) u =
      wideProfile B W u / 4 := by
    unfold wideProfile smoothedRatioSquare affineSmoothing
    calc
      (∫ x : ℝ, B * psi4 (B * (u - x)) * ratioProfile W x) =
          ∫ x : ℝ, (1 / 4 : ℝ) *
            (B * sourceBump 1 zero_lt_one (B * (u - x)) * ratioProfile W x) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [psi4]
        ring
      _ = (1 / 4 : ℝ) *
          (∫ x : ℝ, B * sourceBump 1 zero_lt_one (B * (u - x)) * ratioProfile W x) := by
        rw [integral_const_mul]
      _ = (∫ x : ℝ, B * sourceBump 1 zero_lt_one (B * (u - x)) * ratioProfile W x) / 4 := by
        ring
  have hmain := affineSmoothing_le_of_le hB psi4 (ratioProfile W)
    hpsi0 hcard0 hprof0 hprofLe hmass4 hpsiInt hprofCont u
  rw [hscaled] at hmain
  nlinarith

/-- `wideProfile` is an admissible source profile with the enlarged support
collar 7.  Its Fourier decay is the already-proved literal smoothing decay;
only the height parameter is enlarged from `|W|²` to `4|W|²`. -/
theorem wideProfile_sourceAdmissibleProfile
    {T B : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B) (hBT : B ≤ T)
    (W : Finset ℝ) :
    SourceAdmissibleProfile T (4 * (W.card : ℝ) ^ 2) 7
      (wideProfile B W) := by
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB4
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hnonneg : ∀ u, 0 ≤ wideProfile B W u :=
    wideProfile_nonneg hB W
  have hbounded : ∀ u, wideProfile B W u ≤ 4 * (W.card : ℝ) ^ 2 :=
    wideProfile_bounded hB W
  have hcont : Continuous (wideProfile B W) := by
    exact smoothedRatioSquare_continuous hB W
  have hInt : Integrable (wideProfile B W) := by
    exact integrable_smoothedRatioSquare hB W
  have hsq : Integrable (fun u => (wideProfile B W u) ^ 2) := by
    have hsupport : HasCompactSupport (wideProfile B W) := by
      apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-7 : ℝ) 7))
      intro u hu
      by_contra hne
      exact hu (abs_le.mp (wideProfile_supported hB4 W hne))
    exact (hcont.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply] using (hsupport.mul_right :
        HasCompactSupport ((wideProfile B W) * (wideProfile B W))))
  have hdec0 := smoothedRatioSquare_sourceFourierRapidDecay hB hT hBT W
  have hdec : SourceFourierRapidDecay
      (FourierTransform.fourier (fun u : ℝ => (wideProfile B W u : ℂ))) T
      (4 * (W.card : ℝ) ^ 2) := by
    intro eta heta j
    obtain ⟨C, hC, hbound⟩ := hdec0 eta heta j
    refine ⟨C, hC, ?_⟩
    intro z hz
    have hnonneg : 0 ≤ C * T ^ eta * (T / |z|) ^ j := by positivity
    have hcard : 0 ≤ (W.card : ℝ) ^ 2 := by positivity
    have hsmall := hbound z hz
    calc
      ‖FourierTransform.fourier (fun u : ℝ => (wideProfile B W u : ℂ)) z‖ ≤
          C * T ^ eta * (T / |z|) ^ j * (W.card : ℝ) ^ 2 := hsmall
      _ ≤ C * T ^ eta * (T / |z|) ^ j * (4 * (W.card : ℝ) ^ 2) := by
        gcongr
        nlinarith [hcard]
  exact
    { nonneg := hnonneg
      bounded := hbounded
      supported := fun u hu => wideProfile_supported hB4 W hu
      integrable := hInt
      squareIntegrable := hsq
      continuous := hcont
      rapidDecay := hdec }

end GuthMaynardS3WideProfile

#print axioms GuthMaynardS3WideProfile.wideProfile_sourceAdmissibleProfile

namespace GuthMaynardS3WideProfile

open GuthMaynardJIteration
open GuthMaynardS3LiteralProfile
open GuthMaynardRatioKernelIdentity
open GuthMaynardS3LiteralAffineReduction

