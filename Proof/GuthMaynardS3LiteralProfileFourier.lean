import GuthMaynardS3LiteralProfile
import GuthMaynardS3LiteralRadialDecay
import GuthMaynardAffineSmoothingNorms

/-!
# Lemma 8.4: uniform Fourier seminorms of the literal ratio profile

The objects are the actual compactly supported ratio profile
`ratioCutoff * ‖ratioDirichletKernel W‖²` and its affine smoothing at scale
`B`, not a proxy bump.  Cutoff derivative/Fourier constants are independent of
`W`.  The smoothing Fourier bound carries the source scale `B`.  After the
source comparison `B ≤ T` this is the `T^j / |ξ|^j |W|²` envelope.  The
comparison of `|W|²` to `sup f` via `f(1) ≍ |W|² B/T` is not claimed.

Source: Guth--Maynard, Lemma 8.4.
-/

namespace GuthMaynardS3LiteralProfileFourier

open MeasureTheory Metric
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open GuthMaynardS3LiteralProfile GuthMaynardS3LiteralRadialDecay
open GuthMaynardLemma43FourierIBP GuthMaynardJIteration
open GuthMaynardRatioKernelIdentity

noncomputable section

/-! ## Cutoff derivative and Fourier budgets -/

theorem ratioCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) ratioCutoff := by
  unfold ratioCutoff
  exact ((sourceBump_contDiff 2 (by norm_num)).comp
    (contDiff_id.sub contDiff_const)).mul
      (contDiff_const.sub (sourceBump_contDiff (1 / 16) (by norm_num)))

theorem ratioCutoff_hasCompactSupport : HasCompactSupport ratioCutoff := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-6 : ℝ) 6))
  intro u hu
  by_contra hne
  exact hu (abs_le.mp (ratioCutoff_supported hne))

theorem ratioCutoff_complex_hasCompactSupport :
    HasCompactSupport (fun u : ℝ => (ratioCutoff u : ℂ)) :=
  ratioCutoff_hasCompactSupport.comp_left Complex.ofReal_zero

theorem ratioCutoff_complex_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (ratioCutoff u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ratioCutoff_contDiff

def ratioCutoffSchwartz : 𝓢(ℝ, ℂ) :=
  ratioCutoff_complex_hasCompactSupport.toSchwartzMap ratioCutoff_complex_contDiff

def ratioCutoffDerivativeSup (q : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (schwartzIteratedDerivative q ratioCutoffSchwartz)

theorem ratioCutoffDerivativeSup_nonneg (q : ℕ) :
    0 ≤ ratioCutoffDerivativeSup q :=
  apply_nonneg _ _

theorem norm_iteratedDeriv_ratioCutoff_le (q : ℕ) (u : ℝ) :
    ‖iteratedDeriv q (fun x : ℝ => (ratioCutoff x : ℂ)) u‖ ≤
      ratioCutoffDerivativeSup q := by
  have h := SchwartzMap.norm_le_seminorm ℂ
    (schwartzIteratedDerivative q ratioCutoffSchwartz) u
  rw [schwartzIteratedDerivative_apply] at h
  exact h

def ratioCutoffFourierConstant (q : ℕ) : ℝ :=
  2 ^ q * (Finset.Iic (q, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 ratioCutoffSchwartz)

theorem ratioCutoffFourierConstant_nonneg (q : ℕ) :
    0 ≤ ratioCutoffFourierConstant q := by
  unfold ratioCutoffFourierConstant
  positivity

theorem ratioCutoff_fourier_decay (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier (fun u : ℝ => (ratioCutoff u : ℂ)) xi‖ ≤
      ratioCutoffFourierConstant q / (1 + |xi|) ^ q := by
  let bhat : 𝓢(ℝ, ℂ) := 𝓕 ratioCutoffSchwartz
  have hseminorm := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (q, 0)) (k := q) (n := 0)
    le_rfl le_rfl bhat xi
  have hseminorm' :
      (1 + |xi|) ^ q * ‖bhat xi‖ ≤
        2 ^ q * (Finset.Iic (q, 0)).sup
          (fun m => SchwartzMap.seminorm ℂ m.1 m.2) bhat := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using hseminorm
  have hden : 0 < (1 + |xi|) ^ q := by positivity
  apply (le_div_iff₀ hden).2
  rw [mul_comm]
  simpa only [bhat, ratioCutoffFourierConstant] using hseminorm'

/-! ## `L¹` Fourier envelope of the actual ratio profile -/

def ratioProfileC (W : Finset ℝ) : ℝ → ℂ :=
  fun u => (ratioProfile W u : ℂ)

theorem integral_ratioProfile_le (W : Finset ℝ) :
    (∫ u : ℝ, ratioProfile W u) ≤ 12 * (W.card : ℝ) ^ 2 := by
  have hi := ratioProfile_integrable W
  have heq : (∫ u : ℝ, ratioProfile W u) =
      ∫ u : ℝ in Set.Icc (-6 : ℝ) 6, ratioProfile W u := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Icc (-6 : ℝ) 6
    · rw [Set.indicator_of_mem hu]
    · have : ratioProfile W u = 0 := by
        by_contra hne
        exact hu (abs_le.mp (ratioProfile_supported W hne))
      rw [Set.indicator_of_notMem hu, this]
  rw [heq]
  calc
    _ ≤ ∫ _ : ℝ in Set.Icc (-6 : ℝ) 6, (W.card : ℝ) ^ 2 := by
      apply integral_mono_ae hi.integrableOn
        (integrableOn_const (hs := by simp [Real.volume_Icc]))
      exact Filter.Eventually.of_forall (fun u => ratioProfile_le_card_sq W u)
    _ = 12 * (W.card : ℝ) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]
      norm_num

theorem norm_fourier_ratioProfile_le (W : Finset ℝ) (xi : ℝ) :
    ‖FourierTransform.fourier (ratioProfileC W) xi‖ ≤
      12 * (W.card : ℝ) ^ 2 := by
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (ratioProfileC W) xi
  change ‖FourierTransform.fourier (ratioProfileC W) xi‖ ≤
    ∫ u : ℝ, ‖ratioProfileC W u‖ at hraw
  have hnorm : (∫ u : ℝ, ‖ratioProfileC W u‖) = ∫ u : ℝ, ratioProfile W u := by
    apply integral_congr_ae
    filter_upwards with u
    simp [ratioProfileC, abs_of_nonneg (ratioProfile_nonneg W u)]
  rw [hnorm] at hraw
  exact hraw.trans (integral_ratioProfile_le W)

/-! ## Smoothing-scale Fourier budget of the actual affine smoothing -/

theorem fourier_smoothedRatioSquare
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi =
      FourierTransform.fourier (ratioProfileC W) xi *
        FourierTransform.fourier
          (fun z : ℝ => (sourceBump 1 zero_lt_one z : ℂ)) (xi / B) := by
  simpa [smoothedRatioSquare, ratioProfileC] using
    fourier_ofReal_affineSmoothing hB (fun z => sourceBump 1 zero_lt_one z)
      (ratioProfile W) (sourceBump 1 zero_lt_one).integrable
      (ratioProfile_integrable W) (sourceBump_contDiff 1 zero_lt_one).continuous
      (ratioProfile_continuous W) xi

/-- Source intermediate bound: `hat f₁(ξ) ≪_j |W|² / (1+|ξ|/B)^j`. -/
theorem smoothedRatioSquare_fourier_decay
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi‖ ≤
      (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) /
        (1 + |xi| / B) ^ q := by
  rw [fourier_smoothedRatioSquare hB W xi, norm_mul]
  have hg := norm_fourier_ratioProfile_le W xi
  have hpsi := sourceBump_fourier_decay 1 zero_lt_one q (xi / B)
  have hden : |xi / B| = |xi| / B := by rw [abs_div, abs_of_pos hB]
  rw [hden] at hpsi
  have hW : 0 ≤ 12 * (W.card : ℝ) ^ 2 := by positivity
  calc
    ‖FourierTransform.fourier (ratioProfileC W) xi‖ *
        ‖FourierTransform.fourier
          (fun z : ℝ => (sourceBump 1 zero_lt_one z : ℂ)) (xi / B)‖ ≤
      (12 * (W.card : ℝ) ^ 2) *
        (sourceBumpFourierConstant 1 zero_lt_one q / (1 + |xi| / B) ^ q) :=
      mul_le_mul hg hpsi (norm_nonneg _) hW
    _ = _ := by ring

theorem smoothedRatioSquare_fourier_decay_abs
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (q : ℕ) {xi : ℝ} (hxi : xi ≠ 0) :
    ‖FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi‖ ≤
      (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) *
        (B / |xi|) ^ q := by
  have hmain := smoothedRatioSquare_fourier_decay hB W q xi
  have hcmp : 1 / (1 + |xi| / B) ^ q ≤ (B / |xi|) ^ q := by
    have hpos : 0 < |xi| / B := div_pos (abs_pos.mpr hxi) hB
    have hbase : (|xi| / B) ^ q ≤ (1 + |xi| / B) ^ q :=
      pow_le_pow_left₀ hpos.le (le_add_of_nonneg_left zero_le_one) q
    have := inv_anti₀ (pow_pos hpos q) hbase
    simpa [one_div, div_pow, inv_div] using this
  have hC : 0 ≤ 12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (sourceBumpFourierConstant_nonneg 1 zero_lt_one q)
  calc
    _ ≤ (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) /
          (1 + |xi| / B) ^ q := hmain
    _ = (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) *
          (1 / (1 + |xi| / B) ^ q) := by ring
    _ ≤ (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) *
          (B / |xi|) ^ q :=
      mul_le_mul_of_nonneg_left hcmp hC

/-! ## Outer cutoff profile of Lemma 8.4 -/

/-- Literal Lemma 8.4 profile: outer bump `ψ₁` times the `B`-smoothing of the
actual compactly supported ratio profile. -/
def lemma84Profile (B : ℝ) (W : Finset ℝ) (u : ℝ) : ℝ :=
  ratioCutoff u * smoothedRatioSquare B W u

theorem lemma84Profile_nonneg {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ lemma84Profile B W u :=
  mul_nonneg (ratioCutoff_nonneg u) (smoothedRatioSquare_nonneg hB W u)

theorem lemma84Profile_supported {B : ℝ} (W : Finset ℝ) {u : ℝ}
    (hu : lemma84Profile B W u ≠ 0) : |u| ≤ 6 := by
  apply ratioCutoff_supported
  intro hz
  exact hu (by simp [lemma84Profile, hz])

theorem lemma84Profile_hasCompactSupport {B : ℝ} (W : Finset ℝ) :
    HasCompactSupport (lemma84Profile B W) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-6 : ℝ) 6))
  intro u hu
  by_contra hne
  exact hu (abs_le.mp (lemma84Profile_supported W hne))

theorem lemma84Profile_le_smoothedRatioSquare
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    lemma84Profile B W u ≤ smoothedRatioSquare B W u :=
  mul_le_of_le_one_left (smoothedRatioSquare_nonneg hB W u)
    (ratioCutoff_le_one u)

theorem smoothedRatioSquare_continuous {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    Continuous (smoothedRatioSquare B W) := by
  unfold smoothedRatioSquare
  refine continuous_affineSmoothing (P := (1 : ℝ)) hB
    (fun z => sourceBump 1 zero_lt_one z) (ratioProfile W) ?_
    (sourceBump_contDiff 1 zero_lt_one).continuous
    (ratioProfile_integrable W)
  intro z
  simpa [Real.norm_eq_abs, abs_of_nonneg (sourceBump_nonneg 1 zero_lt_one z)]
    using sourceBump_le_one 1 zero_lt_one z

theorem lemma84Profile_continuous {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    Continuous (lemma84Profile B W) :=
  ratioCutoff_continuous.mul (smoothedRatioSquare_continuous hB W)

theorem lemma84Profile_integrable {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    Integrable (lemma84Profile B W) :=
  (lemma84Profile_continuous hB W).integrable_of_hasCompactSupport
    (lemma84Profile_hasCompactSupport W)

theorem integrable_smoothedRatioSquare {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    Integrable (smoothedRatioSquare B W) := by
  simpa [smoothedRatioSquare] using
    integrable_affineSmoothing hB (sourceBump 1 zero_lt_one).integrable
      (ratioProfile_integrable W)

theorem integral_lemma84Profile_le
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    (∫ u : ℝ, lemma84Profile B W u) ≤ 48 * (W.card : ℝ) ^ 2 := by
  have hmono :=
    integral_mono (lemma84Profile_integrable hB W)
      (integrable_smoothedRatioSquare hB W)
      (fun u => lemma84Profile_le_smoothedRatioSquare hB W u)
  have hsm := integral_smoothedRatio_sq_le hB W
  have heq : (∫ u : ℝ, smoothedRatio B W u ^ 2) =
      ∫ u : ℝ, smoothedRatioSquare B W u := by
    apply integral_congr_ae
    filter_upwards with u
    exact smoothedRatio_sq hB W u
  have hr := integral_ratioProfile_le W
  have hfour : (0 : ℝ) ≤ 4 := by norm_num
  calc
    (∫ u : ℝ, lemma84Profile B W u) ≤
        ∫ u : ℝ, smoothedRatioSquare B W u := hmono
    _ = ∫ u : ℝ, smoothedRatio B W u ^ 2 := heq.symm
    _ ≤ 4 * ∫ u : ℝ, ratioProfile W u := hsm
    _ ≤ 4 * (12 * (W.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hr hfour
    _ = 48 * (W.card : ℝ) ^ 2 := by ring

def lemma84ProfileC (B : ℝ) (W : Finset ℝ) : ℝ → ℂ :=
  fun u => (lemma84Profile B W u : ℂ)

/-- `L¹` Fourier envelope of the actual compact Lemma 8.4 profile. -/
theorem norm_fourier_lemma84Profile_le
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤
      48 * (W.card : ℝ) ^ 2 := by
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (lemma84ProfileC B W) xi
  change ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤
    ∫ u : ℝ, ‖lemma84ProfileC B W u‖ at hraw
  have hnorm : (∫ u : ℝ, ‖lemma84ProfileC B W u‖) =
      ∫ u : ℝ, lemma84Profile B W u := by
    apply integral_congr_ae
    filter_upwards with u
    simp [lemma84ProfileC, abs_of_nonneg (lemma84Profile_nonneg hB W u)]
  rw [hnorm] at hraw
  exact hraw.trans (integral_lemma84Profile_le hB W)

/-! ## Lemma 8.4 Fourier conclusion, with source `T` and scale `B` -/

/-- After `B ≤ T`, the smoothing Fourier bound is the source
`T^q / |ξ|^q |W|²` envelope. -/
theorem smoothedRatioSquare_fourier_le_timePow_mul_card
    {B T : ℝ} (hB : 0 < B) (_hT : 1 ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) (q : ℕ) {xi : ℝ} (hxi : xi ≠ 0) :
    ‖FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi‖ ≤
      (12 * sourceBumpFourierConstant 1 zero_lt_one q) *
        (W.card : ℝ) ^ 2 * (T / |xi|) ^ q := by
  have hmain := smoothedRatioSquare_fourier_decay_abs hB W q hxi
  have hBxi : B / |xi| ≤ T / |xi| := by
    exact div_le_div_of_nonneg_right hBT (abs_nonneg _)
  have hpow : (B / |xi|) ^ q ≤ (T / |xi|) ^ q :=
    pow_le_pow_left₀ (by positivity) hBxi q
  have hC : 0 ≤ 12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (sourceBumpFourierConstant_nonneg 1 zero_lt_one q)
  have hstep :
      12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
          (B / |xi|) ^ q ≤
        12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
          (T / |xi|) ^ q :=
    mul_le_mul_of_nonneg_left hpow hC
  refine hmain.trans (hstep.trans (le_of_eq ?_))
  ring

/-- Explicit order-`q` constant in the smoothing Fourier bound, independent of
`W`, `T`, and `B`. -/
def lemma84SmoothingFourierConstant (q : ℕ) : ℝ :=
  12 * sourceBumpFourierConstant 1 zero_lt_one q

theorem lemma84SmoothingFourierConstant_nonneg (q : ℕ) :
    0 ≤ lemma84SmoothingFourierConstant q :=
  mul_nonneg (by norm_num)
    (sourceBumpFourierConstant_nonneg 1 zero_lt_one q)

/-- The actual smoothing satisfies the Proposition 9.1 Fourier-decay class
on the scale `S = |W|²`, with the source `T` and smoothing-scale `B`.
The `T^η` slack is the quantified form of the source `≪_j`. -/
theorem smoothedRatioSquare_sourceFourierRapidDecay
    {B T : ℝ} (hB : 0 < B) (hT : 1 ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) :
    SourceFourierRapidDecay
      (FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)))
      T ((W.card : ℝ) ^ 2) := by
  intro eta heta j
  have hTeta : 1 ≤ T ^ eta := Real.one_le_rpow hT heta.le
  refine ⟨lemma84SmoothingFourierConstant j, lemma84SmoothingFourierConstant_nonneg j, ?_⟩
  intro z hz
  have hS : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
  have hfac : 0 ≤ lemma84SmoothingFourierConstant j :=
    lemma84SmoothingFourierConstant_nonneg j
  have hdec :=
    smoothedRatioSquare_fourier_le_timePow_mul_card hB hT hBT W j hz
  have hpow : 0 ≤ (T / |z|) ^ j := by positivity
  refine hdec.trans ?_
  change lemma84SmoothingFourierConstant j * (W.card : ℝ) ^ 2 * (T / |z|) ^ j ≤
    lemma84SmoothingFourierConstant j * T ^ eta * (T / |z|) ^ j *
      (W.card : ℝ) ^ 2
  have hleft :
      lemma84SmoothingFourierConstant j * (W.card : ℝ) ^ 2 * (T / |z|) ^ j =
        lemma84SmoothingFourierConstant j * ((T / |z|) ^ j * (W.card : ℝ) ^ 2) := by
    ring
  have hright :
      lemma84SmoothingFourierConstant j * T ^ eta * (T / |z|) ^ j *
          (W.card : ℝ) ^ 2 =
        lemma84SmoothingFourierConstant j *
          (T ^ eta * ((T / |z|) ^ j * (W.card : ℝ) ^ 2)) := by
    ring
  rw [hleft, hright]
  exact mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_left (mul_nonneg hpow hS) hTeta) hfac

end
end GuthMaynardS3LiteralProfileFourier

#print axioms GuthMaynardS3LiteralProfileFourier.ratioCutoff_fourier_decay
#print axioms GuthMaynardS3LiteralProfileFourier.norm_iteratedDeriv_ratioCutoff_le
#print axioms GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_fourier_decay
#print axioms GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_fourier_decay_abs
#print axioms GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_fourier_le_timePow_mul_card
#print axioms GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_sourceFourierRapidDecay
#print axioms GuthMaynardS3LiteralProfileFourier.lemma84Profile_hasCompactSupport
#print axioms GuthMaynardS3LiteralProfileFourier.norm_fourier_lemma84Profile_le
#print axioms GuthMaynardS3LiteralProfileFourier.integral_lemma84Profile_le

#print GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_fourier_decay
#print GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_fourier_decay_abs
#print GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_fourier_le_timePow_mul_card
#print GuthMaynardS3LiteralProfileFourier.smoothedRatioSquare_sourceFourierRapidDecay
#print GuthMaynardS3LiteralProfileFourier.lemma84Profile
#print GuthMaynardS3LiteralProfileFourier.norm_fourier_lemma84Profile_le
