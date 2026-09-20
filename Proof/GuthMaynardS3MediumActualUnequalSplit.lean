import GuthMaynardS3UnequalScaleSecondPoisson
import GuthMaynardLemma92UnequalScaleLargeEllWeld
import GuthMaynardS3ActualFourierTail

set_option maxHeartbeats 3000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3MediumActualUnequalSplit

open GuthMaynardJIteration
open GuthMaynardS3UnequalScaleSecondPoisson
open GuthMaynardS3LiteralLemma84Outer
open GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardHeathBrownInterface

/-! Endpoint-safe finite partition.  The standard source restriction uses
`<`; for the actual Fourier tail we retain the endpoint as well, so the
discarded filter yields the strict inequality required by its pointwise
estimate. -/
def sigmaIIEllRetainedFiniteLE
    (ellRange mRange : Finset ℤ) (L : ℝ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  sigmaIIFinite (ellRange.filter fun ell => |(ell : ℝ)| ≤ L)
    mRange psi2 fhat M2 T M3 Ctau

def sigmaIIEllTailFiniteLE
    (ellRange mRange : Finset ℤ) (L : ℝ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  sigmaIIFinite (ellRange.filter fun ell => ¬ |(ell : ℝ)| ≤ L)
    mRange psi2 fhat M2 T M3 Ctau

theorem sigmaIIFinite_eq_ellRetainedLE_add_tailLE
    (ellRange mRange : Finset ℤ) (L : ℝ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) :
    sigmaIIFinite ellRange mRange psi2 fhat M2 T M3 Ctau =
      sigmaIIEllRetainedFiniteLE ellRange mRange L psi2 fhat M2 T M3 Ctau +
        sigmaIIEllTailFiniteLE ellRange mRange L psi2 fhat M2 T M3 Ctau := by
  unfold sigmaIIEllRetainedFiniteLE sigmaIIEllTailFiniteLE sigmaIIFinite
  exact (Finset.sum_filter_add_sum_filter_not ellRange
    (fun ell => |(ell : ℝ)| ≤ L) _).symm

theorem sigmaIIEllRetainedFiniteLE_const_one_le_sourceBump_radius_unequalScale
    (ellRange mRange : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) {T M3 Ctau R : ℝ}
    (hT : 0 < T) (hCtau : 0 ≤ Ctau) (hR : 0 < R) :
    sigmaIIEllRetainedFiniteLE ellRange mRange (R * T / (M : ℝ))
        (fun _ => 1) fhat (M : ℝ) T M3 Ctau ≤
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
        (fun x => sourceBump R hR x) fhat (M : ℝ) T M3 Ctau := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  let retained := ellRange.filter fun ell : ℤ =>
    |(ell : ℝ)| ≤ R * T / (M : ℝ)
  have hsubset : retained ⊆ sourceBumpEllRange M T R := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply mem_sourceIntegerWindow_zero_of_abs_le
    have hbound : |(ell : ℝ)| ≤ 2 * R * T / (M : ℝ) := by
      calc
        |(ell : ℝ)| ≤ R * T / (M : ℝ) := hell'
        _ ≤ 2 * R * T / (M : ℝ) := by
          rw [show 2 * R * T / (M : ℝ) = 2 * (R * T / (M : ℝ)) by ring]
          nlinarith [show 0 ≤ R * T / (M : ℝ) by positivity]
    simpa only [sourceBumpEllRange] using hbound
  have hplateau : ∀ ell ∈ retained,
      sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) = 1 := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply sourceBump_eq_one_of_abs_le
    have hscaled :
        |(M : ℝ) * (ell : ℝ) / T| = (M : ℝ) * |(ell : ℝ)| / T := by
      rw [abs_div, abs_mul, abs_of_pos hMreal, abs_of_pos hT]
    rw [hscaled]
    have hmul : (M : ℝ) * |(ell : ℝ)| ≤ R * T := by
      simpa [mul_comm] using (le_div_iff₀ hMreal).mp hell'
    exact (div_le_iff₀ hT).2 hmul
  unfold sigmaIIEllRetainedFiniteLE sigmaIIFinite
  change (∑ ell ∈ retained,
      (1 : ℝ) * ∫ tau in -Ctau..Ctau,
        ‖∑ m2 ∈ mRange,
          sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) ≤ _
  calc
    (∑ ell ∈ retained,
        (1 : ℝ) * ∫ tau in -Ctau..Ctau,
          ‖∑ m2 ∈ mRange,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) =
      ∑ ell ∈ retained,
        sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ mRange,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [hplateau ell hell]
    _ ≤ ∑ ell ∈ sourceBumpEllRange M T R,
        sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ mRange,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro ell hellSmall hellNotRetained
        exact mul_nonneg (sourceBump_nonneg R hR _)
          (intervalIntegral.integral_nonneg (by linarith) fun tau _ =>
            sq_nonneg _)

/-! Exact finite ell bookkeeping.  The cutoff used by the detector and the
interval half-width `Ctau` are independent of the affine smoothing radius.
No Fourier-decay premise is used: the second summand is the literal
discarded finite ell integral that the Fourier lane must later estimate. -/
theorem sigmaIIFinite_const_one_split_sourceBump_radius_unequalScale
    (ellRange mRange : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M)
    {T M3 Ctau R : ℝ} (hT : 0 < T) (hCtau : 0 ≤ Ctau)
    (hR : 0 < R) :
    sigmaIIFinite ellRange mRange (fun _ => 1) fhat
        (M : ℝ) T M3 Ctau ≤
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hR x) fhat
          (M : ℝ) T M3 Ctau +
        sigmaIIEllTailFiniteLE ellRange mRange (R * T / (M : ℝ))
          (fun _ => 1) fhat (M : ℝ) T M3 Ctau := by
  rw [sigmaIIFinite_eq_ellRetainedLE_add_tailLE ellRange mRange
    (R * T / (M : ℝ)) (fun _ => 1) fhat (M : ℝ) T M3 Ctau]
  exact add_le_add
    (sigmaIIEllRetainedFiniteLE_const_one_le_sourceBump_radius_unequalScale
      ellRange mRange fhat hM hT hCtau hR)
    le_rfl

/-! Concrete unequal-scale insertion.  The detector is the literal radius
`4*T^eta` bump, while the second-Poisson interval has half-width `T^eta` and
the affine smoothing bump has radius `T^delta`.  The raw canonical producer
is used before the normalized `(4*T^delta)^2` collar rewrite. -/
theorem sigmaIIFinite_const_one_le_scaledSourceBump_add_literalEllTail
    {T S F eta delta M3 : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange ellRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (q : ℕ) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4) (hM3lo : (M : ℝ) ≤ M3)
    (hM3hi : M3 ≤ 16 * (M : ℝ)) (heta : 0 < eta)
    (hdelta : 0 ≤ delta)
    (hBpos : 0 < Real.rpow T delta)
    (hreserve : eta + 107 ≤ delta * (q : ℝ)) :
    sigmaIIFinite ellRange mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T M3 (Real.rpow T eta) ≤
      ((2 * (Real.rpow T eta) *
          ((4 * Real.rpow T eta) *
            sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M : ℝ)) *
        Real.sqrt ((∫ u : ℝ, f u ^ 2) *
          ((4 * (Real.rpow T delta)) ^ 2 *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F
                  (2 * Real.rpow T delta)))
            (affineSmoothing T
                (sourceBumpNormalized (Real.rpow T delta)
                  hBpos) f))) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * (Real.rpow T eta))) *
              ((25 * 4 * sourceLemma92Decay q * integerQuadraticMass) /
                T ^ 100)) +
        sigmaIIEllTailFiniteLE ellRange mRange
          ((4 * Real.rpow T eta) * T / (M : ℝ))
          (fun _ => 1)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 (Real.rpow T eta) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < 4 * Real.rpow T eta :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hTpos eta)
  have hRone : 1 ≤ 4 * Real.rpow T eta := by
    have hTeta : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT (le_of_lt heta)
    nlinarith
  have hCtau : 0 ≤ Real.rpow T eta :=
    (Real.rpow_nonneg hTpos.le eta)
  have hsplit :=
    sigmaIIFinite_const_one_split_sourceBump_radius_unequalScale
      (M3 := M3) ellRange mRange
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) hM hTpos hCtau hRpos
  have hweighted :=
    sigmaIIFinite_selectedPositiveDyadic_scaledRadius_unequalScale_normalizedJcoll_le
      (M3 := M3) (R := 4 * Real.rpow T eta)
      (B := Real.rpow T delta) (c := 4)
      hf hM mRange hmRange q hT hF0 hF hMhi hCtau
      (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt heta)
      (by ring) hRpos hRone (by rfl) hBpos hM3lo hM3hi hreserve
  have hweighted' :
      sigmaIIFinite (sourceBumpEllRange M T (4 * Real.rpow T eta)) mRange
          (fun x => sourceBump (4 * Real.rpow T eta) hRpos x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 (Real.rpow T eta) ≤
        ((2 * (Real.rpow T eta) *
            ((4 * Real.rpow T eta) *
              sourceBumpFourierConstant 1 zero_lt_one 0)) *
            (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            ((4 * (Real.rpow T delta)) ^ 2 *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F
                    (2 * Real.rpow T delta)))
                (affineSmoothing T
                  (sourceBumpNormalized (Real.rpow T delta) hBpos) f))) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * (Real.rpow T eta))) *
              ((25 * 4 * sourceLemma92Decay q * integerQuadraticMass) /
                T ^ 100)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hweighted
  calc
    _ ≤ sigmaIIFinite (sourceBumpEllRange M T (4 * Real.rpow T eta)) mRange
          (fun x => sourceBump (4 * Real.rpow T eta) hRpos x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 (Real.rpow T eta) +
        sigmaIIEllTailFiniteLE ellRange mRange
          ((4 * Real.rpow T eta) * T / (M : ℝ))
          (fun _ => 1)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 (Real.rpow T eta) := hsplit
    _ ≤ _ := add_le_add hweighted' le_rfl

/-! The literal discarded tail for the actual Lemma-8.4 profile.  The
Fourier lane supplies a pointwise bound on the affine `m₂` sum; finite-sum
integrability and the interval integral are handled here. -/
theorem sigmaIIEllTailFinite_actualLemma84Profile_le
    {B T S eta M2 M3 : ℝ} (hB4 : 4 ≤ B) (hT : 1 ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T)
    (hS0 : 0 ≤ S) (hS : ∀ u, lemma84Profile B W u ≤ S)
    (hSgrowth : S ≤ T ^ (4 : ℝ))
    (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3) (hM3pos : 0 < M3)
    (hM2growth : M2 ≤ T ^ (4 : ℝ))
    (ellRange m2Range : Finset ℤ)
    (hEllCard :
      ((ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2)).card : ℝ) ≤
        T ^ (11 : ℝ))
    (hm2lo : ∀ m2' ∈ m2Range, M2 ≤ |(m2' : ℝ)|)
    (hm2hi : ∀ m2' ∈ m2Range, |(m2' : ℝ)| ≤ 2 * M2)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q)
    (hfhat : Continuous
      (FourierTransform.fourier
        (fun u : ℝ => (lemma84Profile B W u : ℂ)))) :
    sigmaIIEllTailFiniteLE ellRange m2Range
        ((4 * Real.rpow T eta) * T / M2) (fun _ => 1)
        (FourierTransform.fourier
          (fun u : ℝ => (lemma84Profile B W u : ℂ)))
        M2 T M3 (Real.rpow T eta) ≤
      (2 * Real.rpow T eta) *
        (4 * lemma84OuterSupFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTeta0 : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hTpos.le eta
  have hL : (4 * Real.rpow T eta) * T / M2 =
      4 * Real.rpow T (1 + eta) / M2 := by
    have hpowadd : Real.rpow T (1 + eta) = T * Real.rpow T eta := by
      calc
        Real.rpow T (1 + eta) = Real.rpow T 1 * Real.rpow T eta :=
          Real.rpow_add hTpos 1 eta
        _ = T * Real.rpow T eta := by
          norm_num
    rw [hpowadd]
    ring
  let tailRange : Finset ℤ := ellRange.filter (fun ell : ℤ =>
    ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2)
  have htail := sum_norm_sq_sigmaII_affine_tail_le
    hB4 hT hBT W hW hS0 hS hSgrowth hM2pos hM2M3 hM3pos hM2growth
    tailRange m2Range
    (fun ell hell => lt_of_not_ge (Finset.mem_filter.mp hell).2)
    (by simpa only [tailRange] using hEllCard) hm2lo hm2hi hcard heta heta1 hq
  have htermInt : ∀ ell ∈ tailRange,
      IntervalIntegrable
        (fun tau : ℝ =>
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2)
        volume (-Real.rpow T eta) (Real.rpow T eta) := by
    intro ell hell
    apply Continuous.intervalIntegrable
    unfold sigmaIIAffineFrequency
    fun_prop
  have hswap :
      (∑ ell ∈ tailRange,
        ∫ tau in -Real.rpow T eta..Real.rpow T eta,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2) =
      ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 := by
    symm
    exact intervalIntegral.integral_finsetSum htermInt
  have hpoint : ∀ tau ∈ Set.Icc (-Real.rpow T eta) (Real.rpow T eta),
      ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
        4 * lemma84OuterSupFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ) := by
    intro tau htau
    exact htail tau (abs_le.2 ⟨htau.1, htau.2⟩)
  have hsumInt :
      IntervalIntegrable
        (fun tau : ℝ =>
          ∑ ell ∈ tailRange,
            ‖∑ m2 ∈ m2Range,
              (m2 : ℂ) *
                FourierTransform.fourier
                  (fun u : ℝ => (lemma84Profile B W u : ℂ))
                  (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2)
        volume (-Real.rpow T eta) (Real.rpow T eta) := by
    apply Continuous.intervalIntegrable
    unfold sigmaIIAffineFrequency
    fun_prop
  have hconstInt :
      IntervalIntegrable
        (fun _ : ℝ => 4 * lemma84OuterSupFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ))
        volume (-Real.rpow T eta) (Real.rpow T eta) :=
    Continuous.intervalIntegrable continuous_const _ _
  have hmono := intervalIntegral.integral_mono_on
    (by linarith [hTeta0]) hsumInt hconstInt hpoint
  unfold sigmaIIEllTailFiniteLE sigmaIIFinite
  rw [hL]
  simp only [one_mul]
  calc
    (∑ x ∈ ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2),
        ∫ tau in -Real.rpow T eta..Real.rpow T eta,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 x m2 tau)‖ ^ 2) =
      ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              FourierTransform.fourier
                (fun u : ℝ => (lemma84Profile B W u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 := by
      simpa only [tailRange] using hswap
    _ ≤ ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        4 * lemma84OuterSupFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ) := hmono
    _ = (2 * Real.rpow T eta) *
        (4 * lemma84OuterSupFourierConstant q ^ 2 *
          Real.rpow T (-229 : ℝ)) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

#print axioms GuthMaynardS3MediumActualUnequalSplit.sigmaIIFinite_const_one_split_sourceBump_radius_unequalScale
#print axioms GuthMaynardS3MediumActualUnequalSplit.sigmaIIFinite_const_one_le_scaledSourceBump_add_literalEllTail
#print axioms GuthMaynardS3MediumActualUnequalSplit.sigmaIIEllTailFinite_actualLemma84Profile_le

/-! Final source-facing weld.  `hfull` is the already-proved literal
first-Poisson/zero-ell estimate with constant weight `1` in its full
second-Poisson sum.  `hsplit` is the endpoint-safe finite ell split above,
`hweighted` is the raw-canonical-to-normalized `J` consumer, and `htail` is
the actual Lemma-8.4 Fourier tail.  The theorem performs only the final
nonnegative multiplication and addition, so no all-ell majorant is hidden. -/
theorem sourceGFinite_mediumIntegral_le_Ceta_actualNormalizedSigmaII_weld
    (S : Set ℝ) (G : ℝ → ℂ) (Sigma weighted Tail Main TailBound A Z E : ℝ)
    (hfull : (∫ xi in S, ‖G xi‖ ^ 2) ≤ A * Sigma + Z + E)
    (hsplit : Sigma ≤ weighted + Tail)
    (hweighted : weighted ≤ Main)
    (htail : Tail ≤ TailBound)
    (hA : 0 ≤ A) :
    (∫ xi in S, ‖G xi‖ ^ 2) ≤ A * (Main + TailBound) + Z + E := by
  calc
    (∫ xi in S, ‖G xi‖ ^ 2) ≤ A * Sigma + Z + E := hfull
    _ ≤ A * (weighted + Tail) + Z + E := by
      gcongr
    _ ≤ A * (Main + TailBound) + Z + E := by
      gcongr

#print axioms GuthMaynardS3MediumActualUnequalSplit.sourceGFinite_mediumIntegral_le_Ceta_actualNormalizedSigmaII_weld

end GuthMaynardS3MediumActualUnequalSplit
