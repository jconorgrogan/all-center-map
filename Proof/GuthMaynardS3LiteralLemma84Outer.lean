import GuthMaynardS3LiteralProfileFourier
import GuthMaynardHeathBrownInterface
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Lemma 8.4, remaining outer-profile obligations

The inner smoothing `f₁ = smoothedRatioSquare` already has the B-scale bound
`‖ˆf₁(ξ)‖ ≤ 12 |W|² C_q / (1+|ξ|/B)^q`.  That is not the compact outer
profile `f = ψ₁ f₁` of Lemma 8.4.

This module proves:

1. the Fourier product/convolution identity `ˆf = ˆψ₁ ∗ ˆf₁` and the
   transfer of B-scale rapid decay to `lemma84Profile`;
2. the source lower comparison near `u = 1`, with height
   (`ContainedInIntervalOfLength`) and nested smoothing-scale hypotheses;
3. the genuine `T/B` loss converting `|W|²` to `(T/B) * sup f`, keeping the
   stronger B-scale bound and using a frequency split plus one extra decay
   order;
4. nested cutoff compatibility: the same imported `ratioCutoff` is one on
   the inner plateau `[1/8,4]`, and for `4 ≤ B` the smoothing kernel at `u=1`
   is supported inside that plateau.

Upper Fourier envelopes remain valid for arbitrary finite `W`.  The lower
bound does not inherit that unrestricted scope.

This is not Lemma 9.2 or Proposition 9.1.  Do not feed `f₁` to a slot that
asks for `f`.
-/

namespace GuthMaynardS3LiteralLemma84Outer

open MeasureTheory Metric Real Complex FiniteDimensional
open scoped BigOperators FourierTransform Convolution ContDiff SchwartzMap
open GuthMaynardS3LiteralProfile GuthMaynardS3LiteralProfileFourier
open GuthMaynardJIteration GuthMaynardRatioKernelIdentity
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownIccIocEndpointAdapter

noncomputable section

set_option maxHeartbeats 800000

/-! ## Nested cutoff geometry -/

/-- For `B ≥ 4` the radius-`2/B` smoothing support at `u=1` sits in the
inner/outer ratio plateau `[1/8,4]`. -/
theorem nestedCutoff_smoothingSupport_subset_plateau
    {B u : ℝ} (hB : (4 : ℝ) ≤ B) (hu : |u - 1| ≤ 2 / B) :
    u ∈ Set.Icc (1 / 8 : ℝ) 4 := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  have hhalf : 2 / B ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ hBpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hball : |u - 1| ≤ (1 / 2 : ℝ) := hu.trans hhalf
  have hI : u ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := by
    rw [Set.mem_Icc]
    constructor <;> linarith [abs_le.mp hball]
  exact ⟨by linarith [hI.1], by linarith [hI.2]⟩

theorem ratioCutoff_eq_one_on_smoothingSupport_at_one
    {B u : ℝ} (hB : (4 : ℝ) ≤ B) (hu : |u - 1| ≤ 2 / B) :
    ratioCutoff u = 1 :=
  ratioCutoff_eq_one (nestedCutoff_smoothingSupport_subset_plateau hB hu)

theorem sourceBump_eq_zero_of_smoothingSupport_at_one
    {B u : ℝ} (hB : (0 : ℝ) < B)
    (hu : 2 / B < |u - 1|) :
    sourceBump 1 zero_lt_one (B * (1 - u)) = 0 := by
  apply sourceBump_eq_zero_of_two_mul_le_abs 1 zero_lt_one
  have : 2 ≤ |B * (1 - u)| := by
    rw [abs_mul, abs_of_pos hB, abs_sub_comm]
    simpa [mul_comm] using (div_le_iff₀ hB).mp hu.le
  simpa using this

/-- On the kernel support at `u=1`, the inner cutoff is identically one, so
the smoothing of `ratioProfile` is the smoothing of `|R|²`. -/
theorem smoothedRatioSquare_at_one_eq_kernel_sq_smoothing
    {B : ℝ} (hB : (4 : ℝ) ≤ B) (W : Finset ℝ) :
    smoothedRatioSquare B W 1 =
      affineSmoothing B (fun z => sourceBump 1 zero_lt_one z)
        (fun u => ‖ratioDirichletKernel W u‖ ^ 2) 1 := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  unfold smoothedRatioSquare affineSmoothing ratioProfile
  apply integral_congr_ae
  filter_upwards with u
  by_cases hker : sourceBump 1 zero_lt_one (B * (1 - u)) = 0
  · simp [hker]
  · have hsupp : |u - 1| ≤ 2 / B := by
      have hs := sourceBump_supported_two_mul zero_lt_one hker
      have : |B * (1 - u)| ≤ 2 := by simpa using hs
      rw [abs_mul, abs_of_pos hBpos, abs_sub_comm] at this
      exact (le_div_iff₀ hBpos).2 (by simpa [mul_comm] using this)
    have hψ : ratioCutoff u = 1 :=
      ratioCutoff_eq_one_on_smoothingSupport_at_one hB hsupp
    simp [hψ]

theorem lemma84Profile_eq_smoothedRatioSquare_at_one
    {B : ℝ} (W : Finset ℝ) :
    lemma84Profile B W 1 = smoothedRatioSquare B W 1 := by
  have hone : ratioCutoff (1 : ℝ) = 1 :=
    ratioCutoff_eq_one ⟨by norm_num, by norm_num⟩
  simp [lemma84Profile, hone]

/-! ## Fourier product / convolution identity -/

theorem integrable_fourier_ratioCutoff :
    Integrable (FourierTransform.fourier fun u : ℝ => (ratioCutoff u : ℂ)) := by
  have hfun :
      (fun u : ℝ => (ratioCutoff u : ℂ)) = (ratioCutoffSchwartz : ℝ → ℂ) := by
    funext u
    rfl
  rw [hfun]
  exact (𝓕 ratioCutoffSchwartz).integrable (μ := volume)

theorem ratioCutoff_fourier_inversion (u : ℝ) :
    (ratioCutoff u : ℂ) =
      ∫ η : ℝ, Complex.exp ((2 * Real.pi * u * η : ℝ) * Complex.I) *
        FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) η := by
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f u)
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) ratioCutoffSchwartz)
  change 𝓕⁻ (𝓕 ratioCutoffSchwartz : 𝓢(ℝ, ℂ)) u = ratioCutoffSchwartz u at h
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq'] at h
  have h' := h.symm
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using! h'

theorem fourier_eq_exp_mul (f : ℝ → ℂ) (xi : ℝ) :
    FourierTransform.fourier f xi =
      ∫ u : ℝ, Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) * f u := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae ?_
  filter_upwards with u
  simp [smul_eq_mul]

theorem lemma84ProfileC_eq_mul {B : ℝ} (W : Finset ℝ) (u : ℝ) :
    lemma84ProfileC B W u =
      (ratioCutoff u : ℂ) * (smoothedRatioSquare B W u : ℂ) := by
  simp [lemma84ProfileC, lemma84Profile, Complex.ofReal_mul]

/-- Pointwise integrand of the Fourier product identity. -/
def lemma84FourierProductKernel (B : ℝ) (W : Finset ℝ) (xi : ℝ) :
    ℝ → ℝ → ℂ :=
  fun eta u =>
    FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
      Complex.exp ((2 * Real.pi * u * eta : ℝ) * Complex.I) *
        (smoothedRatioSquare B W u : ℂ) *
          Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I)

theorem lemma84FourierProductKernel_norm
    {B : ℝ} (W : Finset ℝ) (xi eta u : ℝ) :
    ‖lemma84FourierProductKernel B W xi eta u‖ =
      ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
        |smoothedRatioSquare B W u| := by
  unfold lemma84FourierProductKernel
  simp [norm_mul, Complex.norm_exp, Real.norm_eq_abs]

theorem lemma84FourierProductKernel_eq_phase
    {B : ℝ} (W : Finset ℝ) (xi eta u : ℝ) :
    lemma84FourierProductKernel B W xi eta u =
      FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
        (smoothedRatioSquare B W u : ℂ) *
          Complex.exp ((-2 * Real.pi * u * (xi - eta) : ℝ) * Complex.I) := by
  unfold lemma84FourierProductKernel
  have hphase :
      Complex.exp ((2 * Real.pi * u * eta : ℝ) * Complex.I) *
          Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) =
        Complex.exp ((-2 * Real.pi * u * (xi - eta) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
          ((smoothedRatioSquare B W u : ℂ) *
            (Complex.exp ((2 * Real.pi * u * eta : ℝ) * Complex.I) *
              Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I))) := by
      ring
    _ = _ := by
      rw [hphase]
      ring

theorem integrable_lemma84FourierProductKernel
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    Integrable (Function.uncurry (lemma84FourierProductKernel B W xi)) := by
  have hψ := integrable_fourier_ratioCutoff
  have hf1 : Integrable fun u : ℝ => (smoothedRatioSquare B W u : ℂ) :=
    (integrable_smoothedRatioSquare hB W).ofReal
  have hprod :
      Integrable fun z : ℝ × ℝ =>
        FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) z.1 *
          (smoothedRatioSquare B W z.2 : ℂ) :=
    hψ.mul_prod hf1
  have hphase :
      AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          Complex.exp ((2 * Real.pi * z.2 * z.1 : ℝ) * Complex.I) *
            Complex.exp ((-2 * Real.pi * z.2 * xi : ℝ) * Complex.I))
        volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hbound :
      ∀ᵐ z : ℝ × ℝ,
        ‖Complex.exp ((2 * Real.pi * z.2 * z.1 : ℝ) * Complex.I) *
            Complex.exp ((-2 * Real.pi * z.2 * xi : ℝ) * Complex.I)‖ ≤ 1 := by
    filter_upwards with z
    simp [norm_mul, Complex.norm_exp]
  have hK := hprod.mul_bdd hphase hbound
  apply hK.congr
  filter_upwards with z
  unfold lemma84FourierProductKernel Function.uncurry
  ring

/-- Source identity: `ˆ(ψ₁ f₁) = ˆψ₁ ∗ ˆf₁`. -/
theorem fourier_lemma84Profile_eq_convolution
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    FourierTransform.fourier (lemma84ProfileC B W) xi =
      (FourierTransform.fourier (fun u : ℝ => (ratioCutoff u : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        FourierTransform.fourier fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi := by
  have hKint := integrable_lemma84FourierProductKernel hB W xi
  have hswap :=
    integral_integral_swap (f := lemma84FourierProductKernel B W xi) hKint
  have hleft :
      FourierTransform.fourier (lemma84ProfileC B W) xi =
        ∫ u : ℝ, ∫ eta : ℝ, lemma84FourierProductKernel B W xi eta u := by
    rw [fourier_eq_exp_mul]
    apply integral_congr_ae
    filter_upwards with u
    have hinv := ratioCutoff_fourier_inversion u
    have hc :
        (smoothedRatioSquare B W u : ℂ) *
            Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) =
          (smoothedRatioSquare B W u : ℂ) *
            Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) := rfl
    calc
      Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) *
            lemma84ProfileC B W u =
          Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) *
            ((ratioCutoff u : ℂ) * (smoothedRatioSquare B W u : ℂ)) := by
        rw [lemma84ProfileC_eq_mul]
      _ = (ratioCutoff u : ℂ) *
            ((smoothedRatioSquare B W u : ℂ) *
              Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I)) := by
        ring
      _ = (∫ eta : ℝ,
            Complex.exp ((2 * Real.pi * u * eta : ℝ) * Complex.I) *
              FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta) *
            ((smoothedRatioSquare B W u : ℂ) *
              Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I)) := by
        rw [hinv]
      _ = ∫ eta : ℝ,
            Complex.exp ((2 * Real.pi * u * eta : ℝ) * Complex.I) *
              FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
                ((smoothedRatioSquare B W u : ℂ) *
                  Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I)) := by
        rw [integral_mul_const]
      _ = ∫ eta : ℝ, lemma84FourierProductKernel B W xi eta u := by
        apply integral_congr_ae
        filter_upwards with eta
        unfold lemma84FourierProductKernel
        ring
  have hright :
      ∫ eta : ℝ, ∫ u : ℝ, lemma84FourierProductKernel B W xi eta u =
        ∫ eta : ℝ,
          FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
            FourierTransform.fourier
              (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta) := by
    apply integral_congr_ae
    filter_upwards with eta
    have hphase := lemma84FourierProductKernel_eq_phase (B := B) W xi eta
    have hinner :
        (∫ u : ℝ, lemma84FourierProductKernel B W xi eta u) =
          FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
            ∫ u : ℝ,
              Complex.exp ((-2 * Real.pi * u * (xi - eta) : ℝ) * Complex.I) *
                (smoothedRatioSquare B W u : ℂ) := by
      have hcong :
          (fun u => lemma84FourierProductKernel B W xi eta u) =
            fun u =>
              FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
                ((smoothedRatioSquare B W u : ℂ) *
                  Complex.exp ((-2 * Real.pi * u * (xi - eta) : ℝ) * Complex.I)) := by
        funext u
        rw [hphase]
        ring
      rw [hcong, integral_const_mul]
      apply congrArg
      apply integral_congr_ae
      filter_upwards with u
      ring
    rw [hinner]
    rw [← fourier_eq_exp_mul
      (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)]
  calc
    FourierTransform.fourier (lemma84ProfileC B W) xi =
        ∫ u : ℝ, ∫ eta : ℝ, lemma84FourierProductKernel B W xi eta u := hleft
    _ = ∫ eta : ℝ, ∫ u : ℝ, lemma84FourierProductKernel B W xi eta u := hswap.symm
    _ = ∫ eta : ℝ,
          FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
            FourierTransform.fourier
              (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta) := hright
    _ = (FourierTransform.fourier (fun u : ℝ => (ratioCutoff u : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          FourierTransform.fourier fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi := by
      rw [convolution_mul]

/-! ## Transfer of B-scale rapid decay to the outer profile -/

theorem one_div_one_add_abs_pow_le_inv_one_add_sq (q : ℕ) (x : ℝ) :
    1 / (1 + |x|) ^ (q + 2) ≤ (1 + x ^ 2)⁻¹ := by
  have hden : (0 : ℝ) < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hden' : (0 : ℝ) < (1 + |x|) ^ (q + 2) := by positivity
  rw [one_div, inv_le_inv₀ hden' hden]
  have hsq : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    rw [add_sq, sq_abs]
    nlinarith [abs_nonneg x]
  have hbase : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hq : (1 : ℝ) ≤ (1 + |x|) ^ q := one_le_pow₀ hbase
  have hpow : (1 + |x|) ^ 2 ≤ (1 + |x|) ^ (q + 2) := by
    calc
      (1 + |x|) ^ 2 = (1 + |x|) ^ 2 * 1 := by ring
      _ ≤ (1 + |x|) ^ 2 * (1 + |x|) ^ q :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (1 + |x|) ^ (2 + q) := by rw [pow_add]
      _ = (1 + |x|) ^ (q + 2) := by congr 1 <;> omega
  exact hsq.trans hpow

theorem integrable_one_div_one_add_abs_pow (q : ℕ) :
    Integrable fun x : ℝ => 1 / (1 + |x|) ^ (q + 2) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < (q + 2 : ℝ) := by
    simp only [Module.finrank_self]
    have hq : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have htwo : (2 : ℝ) ≤ (q : ℝ) + 2 := by linarith
    have hlt : ((1 : ℕ) : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le hlt htwo
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) hr
  apply h.congr
  filter_upwards with x
  have hx : (0 : ℝ) ≤ 1 + |x| := by positivity
  rw [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |x|)]
  have he : (q + 2 : ℝ) = ((q + 2 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_natCast]
  simp only [one_div]

theorem integral_one_div_one_add_abs_pow_le_pi (q : ℕ) :
    (∫ x : ℝ, 1 / (1 + |x|) ^ (q + 2)) ≤ Real.pi := by
  have hf := integrable_one_div_one_add_abs_pow q
  have hg := integrable_inv_one_add_sq
  have hmono :
      (∫ x : ℝ, 1 / (1 + |x|) ^ (q + 2)) ≤ ∫ x : ℝ, (1 + x ^ 2)⁻¹ := by
    apply integral_mono hf hg
    intro x
    exact one_div_one_add_abs_pow_le_inv_one_add_sq q x
  exact hmono.trans (le_of_eq integral_univ_inv_one_add_sq)

/-- Explicit order-`q` constant for the outer B-scale envelope, independent of
`W`, `T` and `B`. -/
def lemma84OuterFourierConstant (q : ℕ) : ℝ :=
  12 * Real.pi * 2 ^ q *
    (sourceBumpFourierConstant 1 zero_lt_one q + 4) *
    ratioCutoffFourierConstant (q + 2)

theorem lemma84OuterFourierConstant_nonneg (q : ℕ) :
    0 ≤ lemma84OuterFourierConstant q := by
  unfold lemma84OuterFourierConstant
  have h1 := sourceBumpFourierConstant_nonneg 1 zero_lt_one q
  have h2 := ratioCutoffFourierConstant_nonneg (q + 2)
  have h3 : 0 ≤ sourceBumpFourierConstant 1 zero_lt_one q + 4 :=
    add_nonneg h1 (by norm_num)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (by positivity)) h3) h2

theorem one_add_abs_div_scale_le_two {B xi : ℝ} (hB : 0 < B) :
    1 + |xi| / B ≤ 2 * (1 + |xi| / (2 * B)) := by
  calc
    1 + |xi| / B ≤ 2 + |xi| / B := by linarith
    _ = 2 * (1 + |xi| / (2 * B)) := by
      field_simp [hB.ne']

theorem abs_sub_ge_of_half_ball {xi eta : ℝ} (h : |eta| ≤ |xi| / 2) :
    |xi| / 2 ≤ |xi - eta| := by
  have := abs_sub_abs_le_abs_sub xi eta
  linarith [abs_sub_comm xi eta]

theorem one_add_abs_le_two_mul_one_add_half (xi : ℝ) :
    1 + |xi| ≤ 2 * (1 + |xi| / 2) := by
  linarith [abs_nonneg xi]

theorem continuous_fourier_smoothedRatioSquare
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    Continuous
      (FourierTransform.fourier fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂
    (integrable_smoothedRatioSquare hB W).ofReal

theorem continuous_fourier_ratioCutoff :
    Continuous (FourierTransform.fourier fun u : ℝ => (ratioCutoff u : ℂ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂
    (ratioCutoff_continuous.integrable_of_hasCompactSupport
      ratioCutoff_hasCompactSupport).ofReal

theorem norm_fourier_smoothedRatioSquare_le_card
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi‖ ≤
      48 * (W.card : ℝ) ^ 2 := by
  have hL1 := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ)
    (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) xi
  have hnorm :
      (∫ u : ℝ, ‖(smoothedRatioSquare B W u : ℂ)‖) =
        ∫ u : ℝ, smoothedRatioSquare B W u := by
    apply integral_congr_ae
    filter_upwards with u
    simp [abs_of_nonneg (smoothedRatioSquare_nonneg hB W u)]
  have hsm := integral_smoothedRatio_sq_le hB W
  have heq : (∫ u : ℝ, smoothedRatio B W u ^ 2) =
      ∫ u : ℝ, smoothedRatioSquare B W u := by
    apply integral_congr_ae
    filter_upwards with u
    exact smoothedRatio_sq hB W u
  have hr := integral_ratioProfile_le W
  have hinter :
      (∫ u : ℝ, smoothedRatioSquare B W u) ≤ 48 * (W.card : ℝ) ^ 2 := by
    calc
      (∫ u : ℝ, smoothedRatioSquare B W u) =
          ∫ u : ℝ, smoothedRatio B W u ^ 2 := heq.symm
      _ ≤ 4 * ∫ u : ℝ, ratioProfile W u := hsm
      _ ≤ 4 * (12 * (W.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 48 * (W.card : ℝ) ^ 2 := by ring
  exact hL1.trans (hnorm.trans_le hinter)

theorem integrable_abs_fourier_convolution_integrand
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    Integrable fun eta : ℝ =>
      ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
        ‖FourierTransform.fourier
          (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖ := by
  have hψ := integrable_fourier_ratioCutoff.norm
  have hC : 0 ≤ 48 * (W.card : ℝ) ^ 2 := by positivity
  have hmajor :
      Integrable fun eta : ℝ =>
        (48 * (W.card : ℝ) ^ 2) *
          ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ :=
    hψ.const_mul (48 * (W.card : ℝ) ^ 2)
  have hcont : Continuous (fun eta : ℝ =>
      FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)) :=
    (continuous_fourier_smoothedRatioSquare hB W).comp
      (continuous_const.sub continuous_id)
  apply hmajor.mono'
  · exact hψ.aestronglyMeasurable.mul hcont.norm.aestronglyMeasurable
  · filter_upwards with eta
    have hf1 := norm_fourier_smoothedRatioSquare_le_card hB W (xi - eta)
    have hψn :
        0 ≤ ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ :=
      norm_nonneg _
    calc
      ‖‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
            ‖FourierTransform.fourier
              (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖‖ =
          ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
            ‖FourierTransform.fourier
              (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hψn (norm_nonneg _))]
      _ ≤ ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
            (48 * (W.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hf1 hψn
      _ = (48 * (W.card : ℝ) ^ 2) *
            ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ := by
        ring

theorem lemma84Profile_fourier_le_convolution_L1
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (xi : ℝ) :
    ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤
      ∫ eta : ℝ,
        ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
          ‖FourierTransform.fourier
            (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖ := by
  have hid := fourier_lemma84Profile_eq_convolution hB W xi
  have hint := integrable_abs_fourier_convolution_integrand hB W xi
  rw [hid, convolution_mul]
  have hnorm :=
    norm_integral_le_integral_norm (μ := volume)
      (fun eta : ℝ =>
        FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta *
          FourierTransform.fourier
            (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta))
  refine hnorm.trans ?_
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards with eta
  simp [norm_mul]

/-- B-scale decay of the compact outer profile `f = ψ₁ f₁`.  No height
restriction on `W`.  Requires `1 ≤ B` so the Schwartz tail of `ˆψ₁` is at
least as strong as the B-scale envelope. -/
theorem lemma84Profile_fourier_decay
    {B : ℝ} (hB : (1 : ℝ) ≤ B) (W : Finset ℝ) (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤
      lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 /
        (1 + |xi| / B) ^ q := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hconv := lemma84Profile_fourier_le_convolution_L1 hBpos W xi
  set G : ℝ → ℝ := fun eta =>
    ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
      ‖FourierTransform.fourier
        (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖
  have hGint := integrable_abs_fourier_convolution_integrand hBpos W xi
  have hG0 : ∀ eta, 0 ≤ G eta := fun eta =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let s : Set ℝ := Metric.closedBall (0 : ℝ) (|xi| / 2)
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hsplit : (∫ eta, G eta) = (∫ eta in s, G eta) + ∫ eta in sᶜ, G eta :=
    (integral_add_compl hs hGint).symm
  have hCψ := ratioCutoffFourierConstant_nonneg (q + 2)
  have hCb := sourceBumpFourierConstant_nonneg 1 zero_lt_one q
  have hWsq : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
  have hden : 0 < (1 + |xi| / B) ^ q := by positivity
  have htwoq : (0 : ℝ) ≤ 2 ^ q := by positivity
  -- Region |η| ≤ |ξ|/2 uses the inner B-scale decay.
  have hA :
      (∫ eta in s, G eta) ≤
        12 * Real.pi * 2 ^ q * sourceBumpFourierConstant 1 zero_lt_one q *
          ratioCutoffFourierConstant (q + 2) * (W.card : ℝ) ^ 2 /
            (1 + |xi| / B) ^ q := by
    have hpt : ∀ eta ∈ s,
        G eta ≤
          (ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) *
            (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
              2 ^ q / (1 + |xi| / B) ^ q) := by
      intro eta heta
      have hψ := ratioCutoff_fourier_decay (q + 2) eta
      have hf1 := smoothedRatioSquare_fourier_decay hBpos W q (xi - eta)
      have hball : |eta| ≤ |xi| / 2 := by
        simpa [s, Metric.mem_closedBall, Real.dist_eq] using heta
      have hsub : |xi| / 2 ≤ |xi - eta| := abs_sub_ge_of_half_ball hball
      have hbase : 1 + |xi| / (2 * B) ≤ 1 + |xi - eta| / B := by
        have : |xi| / (2 * B) ≤ |xi - eta| / B := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B) hBpos]
          nlinarith [mul_le_mul_of_nonneg_right hsub hBpos.le]
        linarith
      have hscale : 1 + |xi| / B ≤ 2 * (1 + |xi| / (2 * B)) :=
        one_add_abs_div_scale_le_two hBpos
      have hden2 : 0 < 1 + |xi| / (2 * B) := by positivity
      have hpow :
          (1 + |xi - eta| / B) ^ q ≥ (1 + |xi| / (2 * B)) ^ q :=
        pow_le_pow_left₀ (by positivity) hbase q
      have hinv :
          1 / (1 + |xi - eta| / B) ^ q ≤ 2 ^ q / (1 + |xi| / B) ^ q := by
        have h1 : 1 / (1 + |xi - eta| / B) ^ q ≤
            1 / (1 + |xi| / (2 * B)) ^ q :=
          by simpa only [one_div] using
            (inv_anti₀ (pow_pos (by positivity) q) hpow)
        have h2 : 1 / (1 + |xi| / (2 * B)) ^ q ≤
            2 ^ q / (1 + |xi| / B) ^ q := by
          have hlin := hscale
          have hp := pow_le_pow_left₀ (by positivity) hlin q
          rw [mul_pow] at hp
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          simpa [mul_comm] using hp
        exact h1.trans h2
      have hf1' :
          ‖FourierTransform.fourier
              (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖ ≤
            12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
              2 ^ q / (1 + |xi| / B) ^ q := by
        have := hf1
        have hC : 0 ≤
            12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q :=
          mul_nonneg (mul_nonneg (by norm_num) hWsq) hCb
        calc
          _ ≤ (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) /
                (1 + |xi - eta| / B) ^ q := this
          _ = (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) *
                (1 / (1 + |xi - eta| / B) ^ q) := by ring
          _ ≤ (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q) *
                (2 ^ q / (1 + |xi| / B) ^ q) :=
            mul_le_mul_of_nonneg_left hinv hC
          _ = _ := by ring
      have hψn :
          0 ≤ ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ :=
        norm_nonneg _
      calc
        G eta =
            ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
              ‖FourierTransform.fourier
                (fun u : ℝ => (smoothedRatioSquare B W u : ℂ)) (xi - eta)‖ := rfl
        _ ≤ (ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) *
              (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
                2 ^ q / (1 + |xi| / B) ^ q) :=
          mul_le_mul hψ hf1' (norm_nonneg _)
            (div_nonneg hCψ (by positivity))
    have hfac :
        0 ≤
          12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
            2 ^ q / (1 + |xi| / B) ^ q := by positivity
    have hmaj : Integrable fun eta : ℝ =>
        (ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) *
          (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
            2 ^ q / (1 + |xi| / B) ^ q) := by
      have hh :=
        ((integrable_one_div_one_add_abs_pow q).const_mul
          (ratioCutoffFourierConstant (q + 2))).const_mul
          (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
            2 ^ q / (1 + |xi| / B) ^ q)
      convert hh using 1 <;> ext eta <;> simp [div_eq_mul_inv] <;> ring
    have hleft := hGint.integrableOn (s := s)
    have hright := hmaj.integrableOn (s := s)
    have hmono := setIntegral_mono_on hleft hright hs hpt
    have hpull :
        (∫ eta in s,
            (ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) *
              (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
                2 ^ q / (1 + |xi| / B) ^ q)) =
          (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
              2 ^ q / (1 + |xi| / B) ^ q) *
            ∫ eta in s, ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with eta
      ring
    have hrest :
        (∫ eta in s, ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) ≤
          ∫ eta : ℝ, ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2) := by
      have hf := ((integrable_one_div_one_add_abs_pow q).const_mul
        (ratioCutoffFourierConstant (q + 2)))
      have hf' : Integrable (fun eta : ℝ =>
          ratioCutoffFourierConstant (q + 2) /
            (1 + |eta|) ^ (q + 2)) := by
        convert hf using 1 <;> ext eta <;> ring
      exact setIntegral_le_integral hf'
        (Filter.Eventually.of_forall fun _ => div_nonneg hCψ (by positivity))
    have hπ :
        (∫ eta : ℝ,
            ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) ≤
          ratioCutoffFourierConstant (q + 2) * Real.pi := by
      have := integral_one_div_one_add_abs_pow_le_pi q
      have heq :
          (fun eta : ℝ => ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) =
            fun eta : ℝ =>
              ratioCutoffFourierConstant (q + 2) * (1 / (1 + |eta|) ^ (q + 2)) := by
        funext eta
        ring
      rw [heq, integral_const_mul]
      exact mul_le_mul_of_nonneg_left this hCψ
    calc
      (∫ eta in s, G eta) ≤
          ∫ eta in s,
            (ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2)) *
              (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
                2 ^ q / (1 + |xi| / B) ^ q) := hmono
      _ = (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
            2 ^ q / (1 + |xi| / B) ^ q) *
          ∫ eta in s, ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2) := hpull
      _ ≤ (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
            2 ^ q / (1 + |xi| / B) ^ q) *
          ∫ eta : ℝ, ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2) :=
        mul_le_mul_of_nonneg_left hrest hfac
      _ ≤ (12 * (W.card : ℝ) ^ 2 * sourceBumpFourierConstant 1 zero_lt_one q *
            2 ^ q / (1 + |xi| / B) ^ q) *
          (ratioCutoffFourierConstant (q + 2) * Real.pi) :=
        mul_le_mul_of_nonneg_left hπ hfac
      _ = 12 * Real.pi * 2 ^ q * sourceBumpFourierConstant 1 zero_lt_one q *
            ratioCutoffFourierConstant (q + 2) * (W.card : ℝ) ^ 2 /
              (1 + |xi| / B) ^ q := by ring
  -- Region |η| > |ξ|/2 uses only the integrable Schwartz tail of ˆψ₁.
  have hBreg :
      (∫ eta in sᶜ, G eta) ≤
        48 * Real.pi * 2 ^ q * ratioCutoffFourierConstant (q + 2) *
          (W.card : ℝ) ^ 2 / (1 + |xi| / B) ^ q := by
    have hpt : ∀ eta ∈ sᶜ,
        G eta ≤
          48 * (W.card : ℝ) ^ 2 * ratioCutoffFourierConstant (q + 2) *
            (2 ^ q / (1 + |xi| / B) ^ q) * (1 + eta ^ 2)⁻¹ := by
      intro eta heta
      have hψ := ratioCutoff_fourier_decay (q + 2) eta
      have hf1 := norm_fourier_smoothedRatioSquare_le_card hBpos W (xi - eta)
      have hmem : |xi| / 2 < |eta| := by
        have : eta ∉ s := heta
        have : ¬ |eta| ≤ |xi| / 2 := by
          simpa [s, Metric.mem_closedBall, Real.dist_eq] using this
        exact lt_of_not_ge this
      have hpow : (1 + |xi| / 2) ^ q ≤ (1 + |eta|) ^ q :=
        pow_le_pow_left₀ (by positivity) (by linarith [hmem.le]) q
      have hdenq : (1 + |eta|) ^ (q + 2) =
          (1 + |eta|) ^ q * (1 + |eta|) ^ 2 := by
        rw [← pow_add]
      have hle :
          1 / (1 + |eta|) ^ (q + 2) ≤
            2 ^ q / (1 + |xi|) ^ q * (1 + eta ^ 2)⁻¹ := by
        have h1 : 1 / (1 + |eta|) ^ (q + 2) =
            (1 / (1 + |eta|) ^ q) * (1 / (1 + |eta|) ^ 2) := by
          rw [hdenq, div_mul_eq_div_mul_one_div, one_div]
        have h2 : 1 / (1 + |eta|) ^ q ≤ 1 / (1 + |xi| / 2) ^ q :=
          by simpa only [one_div] using
            (inv_anti₀ (pow_pos (by positivity) q) hpow)
        have h3 : 1 / (1 + |xi| / 2) ^ q ≤ 2 ^ q / (1 + |xi|) ^ q := by
          have hlin := one_add_abs_le_two_mul_one_add_half xi
          have hp := pow_le_pow_left₀ (by positivity) hlin q
          rw [mul_pow] at hp
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          simpa [mul_comm] using hp
        have h4 : 1 / (1 + |eta|) ^ 2 ≤ (1 + eta ^ 2)⁻¹ := by
          have : (1 + eta ^ 2) ≤ (1 + |eta|) ^ 2 := by
            rw [add_sq, sq_abs]
            nlinarith [abs_nonneg eta]
          simpa only [one_div] using
            (inv_anti₀ (by positivity) this)
        calc
          1 / (1 + |eta|) ^ (q + 2) =
              (1 / (1 + |eta|) ^ q) * (1 / (1 + |eta|) ^ 2) := h1
          _ ≤ (2 ^ q / (1 + |xi|) ^ q) * (1 + eta ^ 2)⁻¹ :=
            mul_le_mul (h2.trans h3) h4 (by positivity) (by positivity)
      have hxiB : 1 / (1 + |xi|) ^ q ≤ 1 / (1 + |xi| / B) ^ q := by
        have : 1 + |xi| / B ≤ 1 + |xi| := by
          have : |xi| / B ≤ |xi| := by
            exact div_le_self (abs_nonneg _) hB
          linarith
        simpa only [one_div] using
          (inv_anti₀ (pow_pos (by positivity) q)
            (pow_le_pow_left₀ (by positivity) this q))
      have hψ' :
          ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ ≤
            ratioCutoffFourierConstant (q + 2) *
              (2 ^ q / (1 + |xi| / B) ^ q) * (1 + eta ^ 2)⁻¹ := by
        have := hψ
        have hC : 0 ≤ ratioCutoffFourierConstant (q + 2) := hCψ
        calc
          _ ≤ ratioCutoffFourierConstant (q + 2) / (1 + |eta|) ^ (q + 2) := this
          _ = ratioCutoffFourierConstant (q + 2) * (1 / (1 + |eta|) ^ (q + 2)) := by
            ring
          _ ≤ ratioCutoffFourierConstant (q + 2) *
                (2 ^ q / (1 + |xi|) ^ q * (1 + eta ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hle hC
          _ ≤ ratioCutoffFourierConstant (q + 2) *
                (2 ^ q / (1 + |xi| / B) ^ q * (1 + eta ^ 2)⁻¹) := by
            have hnn : 0 ≤ (1 + eta ^ 2)⁻¹ := by positivity
            have hxiB' : ((1 + |xi|) ^ q)⁻¹ ≤
                ((1 + |xi| / B) ^ q)⁻¹ := by
              simpa only [one_div] using hxiB
            have hmul : 2 ^ q * ((1 + |xi|) ^ q)⁻¹ ≤
                2 ^ q * ((1 + |xi| / B) ^ q)⁻¹ :=
              mul_le_mul_of_nonneg_left hxiB' htwoq
            have hmul' : 2 ^ q / (1 + |xi|) ^ q ≤
                2 ^ q / (1 + |xi| / B) ^ q := by
              simpa only [one_div, div_eq_mul_inv] using hmul
            have hprod := mul_le_mul_of_nonneg_right hmul' hnn
            exact mul_le_mul_of_nonneg_left hprod hC
          _ = _ := by ring
      have hψn :
          0 ≤ ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ :=
        norm_nonneg _
      calc
        G eta ≤
            ‖FourierTransform.fourier (fun x : ℝ => (ratioCutoff x : ℂ)) eta‖ *
              (48 * (W.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hf1 hψn
        _ ≤ (ratioCutoffFourierConstant (q + 2) *
              (2 ^ q / (1 + |xi| / B) ^ q) * (1 + eta ^ 2)⁻¹) *
              (48 * (W.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hψ' (by positivity)
        _ = _ := by ring
    have hmaj : Integrable fun eta : ℝ =>
        48 * (W.card : ℝ) ^ 2 * ratioCutoffFourierConstant (q + 2) *
          (2 ^ q / (1 + |xi| / B) ^ q) * (1 + eta ^ 2)⁻¹ :=
      (integrable_inv_one_add_sq.const_mul _)
    have hleft := hGint.integrableOn (s := sᶜ)
    have hright := hmaj.integrableOn (s := sᶜ)
    have hmono := setIntegral_mono_on hleft hright hs.compl hpt
    refine hmono.trans ?_
    have hpull :
        (∫ eta in sᶜ,
            48 * (W.card : ℝ) ^ 2 * ratioCutoffFourierConstant (q + 2) *
              (2 ^ q / (1 + |xi| / B) ^ q) * (1 + eta ^ 2)⁻¹) ≤
          ∫ eta : ℝ,
            48 * (W.card : ℝ) ^ 2 * ratioCutoffFourierConstant (q + 2) *
              (2 ^ q / (1 + |xi| / B) ^ q) * (1 + eta ^ 2)⁻¹ :=
      setIntegral_le_integral hmaj (Filter.Eventually.of_forall fun _ => by positivity)
    refine hpull.trans ?_
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
    ring_nf
    apply le_of_eq
    ring
  have hsum :
      (∫ eta, G eta) ≤
        lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 /
          (1 + |xi| / B) ^ q := by
    rw [hsplit]
    have := add_le_add hA hBreg
    refine this.trans (le_of_eq ?_)
    unfold lemma84OuterFourierConstant
    ring
  exact hconv.trans hsum

theorem lemma84Profile_fourier_decay_abs
    {B : ℝ} (hB : (1 : ℝ) ≤ B) (W : Finset ℝ) (q : ℕ) {xi : ℝ} (hxi : xi ≠ 0) :
    ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤
      lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 * (B / |xi|) ^ q := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hmain := lemma84Profile_fourier_decay hB W q xi
  have hcmp : 1 / (1 + |xi| / B) ^ q ≤ (B / |xi|) ^ q := by
    have hpos : 0 < |xi| / B := div_pos (abs_pos.mpr hxi) hBpos
    have hbase : (|xi| / B) ^ q ≤ (1 + |xi| / B) ^ q :=
      pow_le_pow_left₀ hpos.le (le_add_of_nonneg_left zero_le_one) q
    have := inv_anti₀ (pow_pos hpos q) hbase
    simpa [one_div, div_pow, inv_div] using this
  have hC : 0 ≤ lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 :=
    mul_nonneg (lemma84OuterFourierConstant_nonneg q) (sq_nonneg _)
  calc
    _ ≤ lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 /
          (1 + |xi| / B) ^ q := hmain
    _ = lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 *
          (1 / (1 + |xi| / B) ^ q) := by ring
    _ ≤ lemma84OuterFourierConstant q * (W.card : ℝ) ^ 2 * (B / |xi|) ^ q :=
      mul_le_mul_of_nonneg_left hcmp hC

/-! ## Source lower bound near `u = 1` -/

theorem abs_log_le_two_mul_abs_sub_one {u : ℝ}
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    |Real.log u| ≤ 2 * |u - 1| := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu.1
  by_cases hge : (1 : ℝ) ≤ u
  · have hlog : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
    have : 0 ≤ Real.log u := Real.log_nonneg hge
    rw [abs_of_nonneg this, abs_of_nonneg (sub_nonneg.mpr hge)]
    linarith
  · have hlt : u < 1 := lt_of_not_ge hge
    have hlog : Real.log u < 0 := Real.log_neg hu0 hlt
    have hinvpos : (0 : ℝ) < 1 / u := one_div_pos.mpr hu0
    have hloginv : Real.log (1 / u) ≤ 1 / u - 1 :=
      Real.log_le_sub_one_of_pos hinvpos
    have habs : |Real.log u| = Real.log (1 / u) := by
      rw [abs_of_neg hlog, ← Real.log_inv, inv_eq_one_div]
    have hle : Real.log (1 / u) ≤ 2 * (1 - u) := by
      have : 1 / u - 1 = (1 - u) / u := by field_simp
      have hdiv : (1 - u) / u ≤ 2 * (1 - u) := by
        have h1u : 0 ≤ 1 - u := sub_nonneg.mpr hlt.le
        have huinv : 1 / u ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith [hu.1])
        calc
          (1 - u) / u = (1 - u) * (1 / u) := by ring
          _ ≤ (1 - u) * 2 := mul_le_mul_of_nonneg_left huinv h1u
          _ = 2 * (1 - u) := by ring
      linarith [hloginv]
    rw [habs, abs_of_neg (sub_lt_zero.mpr hlt)]
    convert hle using 1 <;> ring

theorem re_exp_I_ge_half {θ : ℝ} (hθ : |θ| ≤ Real.pi / 3) :
    (1 / 2 : ℝ) ≤ (Complex.exp (Complex.I * (θ : ℂ))).re := by
  have hcomm : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
  rw [hcomm, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
    Complex.sin_ofReal_re, Complex.I_re, Complex.I_im, mul_zero,
    Complex.sin_ofReal_im, mul_one, sub_zero]
  have hx : 0 ≤ |θ| := abs_nonneg θ
  have hy : Real.pi / 3 ≤ Real.pi := by
    have : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    linarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx hy hθ
  have habs : Real.cos θ = Real.cos |θ| := by
    by_cases h : 0 ≤ θ
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), Real.cos_neg]
  rw [habs]
  simpa [Real.cos_pi_div_three] using hcos

theorem ratioDirichletKernel_norm_sq_ge_card_sq_div_four
    {W : Finset ℝ} {T u : ℝ}
    (hW : ContainedInIntervalOfLength W T) (hT : (1 : ℝ) ≤ T)
    (hu : |u - 1| ≤ 1 / (4 * T)) :
    (W.card : ℝ) ^ 2 / 4 ≤ ‖ratioDirichletKernel W u‖ ^ 2 := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have huI : u ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := by
    have hδ : 1 / (4 * T) ≤ (1 / 4 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : |u - 1| ≤ (1 / 4 : ℝ) := hu.trans hδ
    rw [Set.mem_Icc]
    constructor <;> linarith [abs_le.mp this]
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) huI.1
  have hlog : |Real.log u| ≤ 2 * |u - 1| := abs_log_le_two_mul_abs_sub_one huI
  have hlog' : |Real.log (|u|)| ≤ 1 / (2 * T) := by
    rw [abs_of_pos hu0]
    have : 2 * |u - 1| ≤ 2 * (1 / (4 * T)) :=
      mul_le_mul_of_nonneg_left hu (by norm_num)
    have h2 : 2 * (1 / (4 * T)) = 1 / (2 * T) := by field_simp; ring
    exact hlog.trans (this.trans_eq h2)
  obtain ⟨x0, hx0⟩ := hW
  let L : ℝ := Real.log |u|
  have hphase (t : ℝ) (ht : t ∈ W) : |(t - x0) * L| ≤ Real.pi / 3 := by
    have htI := hx0 t ht
    have hgap : 0 ≤ t - x0 ∧ t - x0 ≤ T := ⟨sub_nonneg.mpr htI.1, sub_le_iff_le_add'.mpr htI.2⟩
    have : |(t - x0) * L| = |t - x0| * |L| := abs_mul _ _
    have htx : |t - x0| ≤ T := by
      rw [abs_of_nonneg hgap.1]
      exact hgap.2
    have hprod : |t - x0| * |L| ≤ T * (1 / (2 * T)) :=
      mul_le_mul htx hlog' (abs_nonneg _) hTpos.le
    have hsimp : T * (1 / (2 * T)) = (1 / 2 : ℝ) := by field_simp [hTpos.ne']
    have hhalf : (1 / 2 : ℝ) ≤ Real.pi / 3 := by
      have : (3 : ℝ) < Real.pi * 2 := by
        nlinarith [Real.pi_gt_three]
      linarith
    rw [this]
    exact hprod.trans_eq hsimp |>.trans hhalf
  have hrot :
      ratioDirichletKernel W u =
        Complex.exp (Complex.I * ((x0 * L : ℝ) : ℂ)) *
          ∑ t ∈ W, Complex.exp (Complex.I * (((t - x0) * L : ℝ) : ℂ)) := by
    unfold ratioDirichletKernel
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnorm :
      ‖ratioDirichletKernel W u‖ =
        ‖∑ t ∈ W, Complex.exp (Complex.I * (((t - x0) * L : ℝ) : ℂ))‖ := by
    rw [hrot, norm_mul, Complex.norm_exp]
    simp
  have hre :
      (W.card : ℝ) / 2 ≤
        (∑ t ∈ W, Complex.exp (Complex.I * (((t - x0) * L : ℝ) : ℂ))).re := by
    rw [Complex.re_sum]
    have hterm : ∀ t ∈ W,
        (1 / 2 : ℝ) ≤
          (Complex.exp (Complex.I * (((t - x0) * L : ℝ) : ℂ))).re :=
      fun t ht => re_exp_I_ge_half (hphase t ht)
    calc
      (W.card : ℝ) / 2 = ∑ _t ∈ W, (1 / 2 : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ t ∈ W, (Complex.exp (Complex.I * (((t - x0) * L : ℝ) : ℂ))).re :=
        Finset.sum_le_sum hterm
  have hge : (W.card : ℝ) / 2 ≤ ‖ratioDirichletKernel W u‖ := by
    rw [hnorm]
    exact hre.trans (Complex.re_le_norm _)
  have hsq := pow_le_pow_left₀ (by positivity) hge 2
  have : ((W.card : ℝ) / 2) ^ 2 = (W.card : ℝ) ^ 2 / 4 := by ring
  rwa [this] at hsq

theorem lemma84Profile_at_one_ge_card_sq_scale_over_time
    {B T : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) (hW : ContainedInIntervalOfLength W T) :
    (B / T) * (W.card : ℝ) ^ 2 / 8 ≤ lemma84Profile B W 1 := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  rw [lemma84Profile_eq_smoothedRatioSquare_at_one]
  let δ : ℝ := 1 / (4 * T)
  let S : Set ℝ := Set.Icc (1 - δ) (1 + δ)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδB : δ ≤ 1 / B := by
    dsimp [δ]
    have h1 : 1 / (4 * T) ≤ 1 / T := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hTpos
      nlinarith
    have h2 : 1 / T ≤ 1 / B := by
      simpa only [one_div] using (inv_anti₀ hBpos hBT)
    exact h1.trans h2
  have hSmeas : MeasurableSet S := measurableSet_Icc
  have hmaj' : ∀ u ∈ S, 1 ≤ sourceBump 1 zero_lt_one (B * (1 - u)) := by
    intro u hu
    have huδ : |1 - u| ≤ 1 / B := by
      have : |u - 1| ≤ δ := by
        rw [Set.mem_Icc] at hu
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_sub_comm]
      exact this.trans hδB
    have : |B * (1 - u)| ≤ 1 := by
      rw [abs_mul, abs_of_pos hBpos]
      calc
        B * |1 - u| = |1 - u| * B := by ring
        _ ≤ (1 / B) * B :=
          mul_le_mul_of_nonneg_right huδ hBpos.le
        _ = 1 := by field_simp [hBpos.ne']
    exact le_of_eq (sourceBump_eq_one_of_abs_le 1 zero_lt_one this).symm
  have hf0 : ∀ u, 0 ≤ ratioProfile W u := ratioProfile_nonneg W
  have hpsi0 : ∀ z, 0 ≤ sourceBump 1 zero_lt_one z :=
    sourceBump_nonneg 1 zero_lt_one
  have hlocal : IntegrableOn (fun u => B * ratioProfile W u) S :=
    ((ratioProfile_integrable W).const_mul B).integrableOn
  have hsmooth : Integrable fun u =>
      B * sourceBump 1 zero_lt_one (B * (1 - u)) * ratioProfile W u :=
    integrable_affineSmoothing_section hBpos
      (fun z => sourceBump 1 zero_lt_one z) (ratioProfile W)
      (sourceBump 1 zero_lt_one).integrable (ratioProfile_continuous W)
      (sq_nonneg (W.card : ℝ))
      (fun u => by
        rw [abs_of_nonneg (ratioProfile_nonneg W u)]
        exact ratioProfile_le_card_sq W u) 1
  have hdom :=
    localized_integral_le_affineSmoothing S hSmeas
      (fun z => sourceBump 1 zero_lt_one z) (ratioProfile W)
      hBpos.le hf0 hpsi0 hmaj' hlocal hsmooth
  have hpt : ∀ u ∈ S, (W.card : ℝ) ^ 2 / 4 ≤ ratioProfile W u := by
    intro u hu
    have huδ : |u - 1| ≤ δ := by
      rw [Set.mem_Icc] at hu
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have huI : u ∈ Set.Icc (1 / 8 : ℝ) 4 := by
      have : |u - 1| ≤ (1 / 4 : ℝ) := by
        have hδ4 : δ ≤ (1 / 4 : ℝ) := by
          dsimp [δ]
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        exact huδ.trans hδ4
      rw [Set.mem_Icc]
      constructor <;> linarith [abs_le.mp this]
    have hcut : ratioCutoff u = 1 := ratioCutoff_eq_one huI
    have hR := ratioDirichletKernel_norm_sq_ge_card_sq_div_four hW hT huδ
    simp [ratioProfile, hcut, hR]
  have hmono : (∫ u in S, B * ((W.card : ℝ) ^ 2 / 4)) ≤ ∫ u in S, B * ratioProfile W u := by
    apply setIntegral_mono_on
    · exact continuous_const.integrableOn_Icc
    · exact hlocal
    · exact hSmeas
    · intro u hu
      exact mul_le_mul_of_nonneg_left (hpt u hu) hBpos.le
  have hvol : (∫ u in S, B * ((W.card : ℝ) ^ 2 / 4)) =
      B * ((W.card : ℝ) ^ 2 / 4) * (2 * δ) := by
    have hle : 1 - δ ≤ 1 + δ := by linarith [hδpos.le]
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hle]
    ring
  have hδval : 2 * δ = 1 / (2 * T) := by
    dsimp [δ]
    field_simp
    ring
  have : B * ((W.card : ℝ) ^ 2 / 4) * (2 * δ) = (B / T) * (W.card : ℝ) ^ 2 / 8 := by
    rw [hδval]
    field_simp
    ring
  have hle1 := hmono.trans hdom
  have : (B / T) * (W.card : ℝ) ^ 2 / 8 ≤
      affineSmoothing B (fun z => sourceBump 1 zero_lt_one z) (ratioProfile W) 1 :=
    (le_of_eq this.symm).trans (hvol.symm.trans_le hle1)
  simpa [smoothedRatioSquare] using this

theorem card_sq_le_eight_mul_time_div_scale_mul_profile_at_one
    {B T : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) (hW : ContainedInIntervalOfLength W T) :
    (W.card : ℝ) ^ 2 ≤ 8 * (T / B) * lemma84Profile B W 1 := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hlow := lemma84Profile_at_one_ge_card_sq_scale_over_time hB hT hBT W hW
  have hid :
      (W.card : ℝ) ^ 2 =
        8 * (T / B) * ((B / T) * (W.card : ℝ) ^ 2 / 8) := by
    field_simp [hBpos.ne', hTpos.ne']
  rw [hid]
  exact mul_le_mul_of_nonneg_left hlow (by positivity)

theorem lemma84Profile_fourier_le_twelve_mul_sup
    {B S : ℝ} (hB : 0 < B) (W : Finset ℝ)
    (hS : ∀ u, lemma84Profile B W u ≤ S) (hS0 : 0 ≤ S) (xi : ℝ) :
    ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤ 12 * S := by
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (lemma84ProfileC B W) xi
  have hnorm : (∫ u : ℝ, ‖lemma84ProfileC B W u‖) = ∫ u : ℝ, lemma84Profile B W u := by
    apply integral_congr_ae
    filter_upwards with u
    simp [lemma84ProfileC, abs_of_nonneg (lemma84Profile_nonneg hB W u)]
  have hsupp :
      (∫ u : ℝ, lemma84Profile B W u) =
        ∫ u in Set.Icc (-6 : ℝ) 6, lemma84Profile B W u := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Icc (-6 : ℝ) 6
    · rw [Set.indicator_of_mem hu]
    · have : lemma84Profile B W u = 0 := by
        by_contra hne
        exact hu (abs_le.mp (lemma84Profile_supported W hne))
      rw [Set.indicator_of_notMem hu, this]
  have hmono :
      (∫ u in Set.Icc (-6 : ℝ) 6, lemma84Profile B W u) ≤
        ∫ _u in Set.Icc (-6 : ℝ) 6, S := by
    apply setIntegral_mono_on
    · exact (lemma84Profile_integrable hB W).integrableOn
    · exact continuous_const.integrableOn_Icc
    · exact measurableSet_Icc
    · intro u _
      exact hS u
  have hvol : (∫ _u in Set.Icc (-6 : ℝ) 6, S) = 12 * S := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]
    ring
  exact hraw.trans (hnorm.trans_le (hsupp.trans_le (hmono.trans_eq hvol)))

/-- Source `T/B` conversion with a frequency split at `|ξ|=B` and one extra
decay order on the high-frequency side.  The B-scale bound above is not
relabelled: it is used as an input, and the `T/B` factor is absorbed only
after the split. -/
def lemma84OuterSupFourierConstant (j : ℕ) : ℝ :=
  12 + 8 * lemma84OuterFourierConstant (j + 1)

theorem lemma84OuterSupFourierConstant_nonneg (j : ℕ) :
    0 ≤ lemma84OuterSupFourierConstant j := by
  unfold lemma84OuterSupFourierConstant
  exact add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (lemma84OuterFourierConstant_nonneg (j + 1)))

theorem lemma84Profile_fourier_le_timePow_mul_sup
    {B T S : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) (hW : ContainedInIntervalOfLength W T)
    (hS : ∀ u, lemma84Profile B W u ≤ S) (hS0 : 0 ≤ S)
    (j : ℕ) {xi : ℝ} (hxi : xi ≠ 0) :
    ‖FourierTransform.fourier (lemma84ProfileC B W) xi‖ ≤
      lemma84OuterSupFourierConstant j * (T / |xi|) ^ j * S := by
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  have hB1 : (1 : ℝ) ≤ B := le_trans (by norm_num) hB
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have h12 := lemma84Profile_fourier_le_twelve_mul_sup hBpos W hS hS0 xi
  have hC : 0 ≤ lemma84OuterSupFourierConstant j :=
    lemma84OuterSupFourierConstant_nonneg j
  have hpow0 : 0 ≤ (T / |xi|) ^ j := by positivity
  have h12' : 12 * S ≤ lemma84OuterSupFourierConstant j * S := by
    have : (12 : ℝ) ≤ lemma84OuterSupFourierConstant j := by
      unfold lemma84OuterSupFourierConstant
      linarith [lemma84OuterFourierConstant_nonneg (j + 1)]
    exact mul_le_mul_of_nonneg_right this hS0
  by_cases hj : j = 0
  · subst j
    simpa [pow_zero, one_mul] using h12.trans h12'
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    by_cases hxiB : |xi| ≤ B
    · have hTxi : 1 ≤ T / |xi| := by
        have : |xi| ≤ T := hxiB.trans hBT
        exact (one_le_div₀ (abs_pos.mpr hxi)).mpr this
      have hone : 1 ≤ (T / |xi|) ^ j := one_le_pow₀ hTxi
      have : 12 * S ≤ lemma84OuterSupFourierConstant j * (T / |xi|) ^ j * S := by
        calc
          12 * S ≤ lemma84OuterSupFourierConstant j * S := h12'
          _ ≤ lemma84OuterSupFourierConstant j * (T / |xi|) ^ j * S := by
            have := mul_le_mul_of_nonneg_left hone hC
            nlinarith [mul_nonneg hC hS0, hpow0]
      exact h12.trans this
    · have hxiB' : B < |xi| := lt_of_not_ge hxiB
      have hdec := lemma84Profile_fourier_decay_abs hB1 W (j + 1) hxi
      have hWle :=
        card_sq_le_eight_mul_time_div_scale_mul_profile_at_one hB hT hBT W hW
      have hf1le : lemma84Profile B W 1 ≤ S := hS 1
      have hWleS : (W.card : ℝ) ^ 2 ≤ 8 * (T / B) * S :=
        hWle.trans (mul_le_mul_of_nonneg_left hf1le (by positivity))
      have hCq := lemma84OuterFourierConstant_nonneg (j + 1)
      have hstep :
          lemma84OuterFourierConstant (j + 1) * (W.card : ℝ) ^ 2 *
              (B / |xi|) ^ (j + 1) ≤
            lemma84OuterSupFourierConstant j * (T / |xi|) ^ j * S := by
        have hprod :
            lemma84OuterFourierConstant (j + 1) * (W.card : ℝ) ^ 2 *
                (B / |xi|) ^ (j + 1) ≤
              lemma84OuterFourierConstant (j + 1) * (8 * (T / B) * S) *
                (B / |xi|) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hWleS hCq)
            (by positivity)
        have hsimp :
            lemma84OuterFourierConstant (j + 1) * (8 * (T / B) * S) *
                (B / |xi|) ^ (j + 1) =
              8 * lemma84OuterFourierConstant (j + 1) * S *
                T * B ^ j / |xi| ^ (j + 1) := by
          have : (B / |xi|) ^ (j + 1) = B ^ (j + 1) / |xi| ^ (j + 1) :=
            div_pow _ _ _
          rw [this]
          field_simp [hBpos.ne', (abs_pos.mpr hxi).ne']
          ring
        have habsorb :
            8 * lemma84OuterFourierConstant (j + 1) * S *
                T * B ^ j / |xi| ^ (j + 1) ≤
              8 * lemma84OuterFourierConstant (j + 1) * S *
                T ^ j / |xi| ^ j := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
          have hratio : T * B ^ (k + 1) / |xi| ^ (k + 1 + 1) ≤
              T ^ (k + 1) / |xi| ^ (k + 1) := by
            have hden : 0 < |xi| ^ (k + 2) := by
              simpa [show k + 2 = k + 1 + 1 by ring] using
                (pow_pos (abs_pos.mpr hxi) (k + 2))
            have hden' : 0 < |xi| ^ (k + 1) := by positivity
            have hden2 : 0 < |xi| ^ (k + 1 + 1) := by positivity
            rw [div_le_div_iff₀ hden2 hden']
            have hBk : B ^ (k + 1) ≤ T ^ k * |xi| := by
              rw [pow_succ]
              calc
                B ^ k * B ≤ T ^ k * B :=
                  mul_le_mul_of_nonneg_right
                    (pow_le_pow_left₀ hBpos.le hBT k) hBpos.le
                _ ≤ T ^ k * |xi| :=
                  mul_le_mul_of_nonneg_left hxiB'.le (by positivity)
            have h1 : T * B ^ (k + 1) ≤ T ^ (k + 1) * |xi| := by
              have := mul_le_mul_of_nonneg_left hBk hTpos.le
              simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
            calc
              T * B ^ (k + 1) * |xi| ^ (k + 1) ≤
                  (T ^ (k + 1) * |xi|) * |xi| ^ (k + 1) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = T ^ (k + 1) * |xi| ^ (k + 1 + 1) := by
                rw [pow_succ]
                ring
          have hnn : 0 ≤ 8 * lemma84OuterFourierConstant (k + 1 + 1) * S := by
            simpa using
              (by positivity :
                0 ≤ 8 * lemma84OuterFourierConstant ((k + 1) + 1) * S)
          have := mul_le_mul_of_nonneg_left hratio
            (by positivity :
              0 ≤ 8 * lemma84OuterFourierConstant ((k + 1) + 1) * S)
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
        have hC8 : 8 * lemma84OuterFourierConstant (j + 1) ≤
            lemma84OuterSupFourierConstant j := by
          unfold lemma84OuterSupFourierConstant
          linarith
        have : 8 * lemma84OuterFourierConstant (j + 1) * S * T ^ j / |xi| ^ j ≤
            lemma84OuterSupFourierConstant j * (T / |xi|) ^ j * S := by
          have : (T / |xi|) ^ j = T ^ j / |xi| ^ j := div_pow _ _ _
          rw [this]
          have hnn : 0 ≤ S * T ^ j / |xi| ^ j := by positivity
          have hmul := mul_le_mul_of_nonneg_right hC8 hnn
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        exact hprod.trans (hsimp.trans_le (habsorb.trans this))
      exact hdec.trans hstep

/-- Lemma 8.4 Fourier conclusion for the compact outer profile, on the scale
`S` of an upper bound of `f`.  This is not Proposition 9.1. -/
theorem lemma84Profile_sourceFourierRapidDecay
    {B T S : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T) (hBT : B ≤ T)
    (W : Finset ℝ) (hW : ContainedInIntervalOfLength W T)
    (hS : ∀ u, lemma84Profile B W u ≤ S) (hS0 : 0 ≤ S) :
    SourceFourierRapidDecay
      (FourierTransform.fourier (lemma84ProfileC B W)) T S := by
  intro eta heta j
  have hTeta : 1 ≤ T ^ eta := Real.one_le_rpow hT heta.le
  refine ⟨lemma84OuterSupFourierConstant j, lemma84OuterSupFourierConstant_nonneg j, ?_⟩
  intro z hz
  have hdec :=
    lemma84Profile_fourier_le_timePow_mul_sup hB hT hBT W hW hS hS0 j hz
  have hpow : 0 ≤ (T / |z|) ^ j := by positivity
  have hfac : 0 ≤ lemma84OuterSupFourierConstant j :=
    lemma84OuterSupFourierConstant_nonneg j
  refine hdec.trans ?_
  have : lemma84OuterSupFourierConstant j * (T / |z|) ^ j * S ≤
      lemma84OuterSupFourierConstant j * T ^ eta * (T / |z|) ^ j * S := by
    have hmul := mul_le_mul_of_nonneg_left hTeta
      (mul_nonneg hpow hS0)
    have hmul' := mul_le_mul_of_nonneg_left hmul hfac
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

end
end GuthMaynardS3LiteralLemma84Outer

#print axioms GuthMaynardS3LiteralLemma84Outer.fourier_lemma84Profile_eq_convolution
#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_fourier_decay
#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_fourier_decay_abs
#print axioms GuthMaynardS3LiteralLemma84Outer.nestedCutoff_smoothingSupport_subset_plateau
#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_at_one_ge_card_sq_scale_over_time
#print axioms GuthMaynardS3LiteralLemma84Outer.card_sq_le_eight_mul_time_div_scale_mul_profile_at_one
#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_fourier_le_timePow_mul_sup
#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_sourceFourierRapidDecay

#print GuthMaynardS3LiteralLemma84Outer.fourier_lemma84Profile_eq_convolution
#print GuthMaynardS3LiteralLemma84Outer.lemma84Profile_fourier_decay
#print GuthMaynardS3LiteralLemma84Outer.lemma84Profile_fourier_le_timePow_mul_sup
#print GuthMaynardS3LiteralLemma84Outer.lemma84Profile_sourceFourierRapidDecay
