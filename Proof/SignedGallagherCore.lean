import ContinuousSlidingFourier
import L1L2PlancherelBridge
import ContinuousKernelOverlap
import Mathlib.MeasureTheory.Function.L2Space

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Set
open scoped BigOperators FourierTransform ArithmeticFunction ENNReal
noncomputable section
open PrimePairEndpoints MAPMajorArcWeld

/-! ## The exact interval multiplier is globally square-integrable -/

/-- Translation of `[0,y]` to `[y,2y]`, with the full phase retained. -/
theorem dyadicAmplitude_eq_phase_mul_gallagherWindowKernel
    (y beta : ℝ) :
    MAPContinuousOverlap.dyadicAmplitude y beta =
      Complex.exp (2 * Real.pi * Complex.I * (beta * y)) *
        gallagherWindowKernel y beta := by
  unfold MAPContinuousOverlap.dyadicAmplitude gallagherWindowKernel
  have hshift := intervalIntegral.integral_comp_add_left
    (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (beta * t))) y
    (a := 0) (b := y)
  have hfactor :
      (∫ u in (0 : ℝ)..y,
        Complex.exp (2 * Real.pi * Complex.I * (beta * (y + u)))) =
      Complex.exp (2 * Real.pi * Complex.I * (beta * y)) *
        ∫ u in (0 : ℝ)..y,
          Complex.exp (2 * Real.pi * Complex.I * (beta * u)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    change Complex.exp (2 * Real.pi * Complex.I *
          ((beta : ℂ) * ((y : ℂ) + (u : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I *
          ((beta : ℂ) * (y : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((beta : ℂ) * (u : ℂ)))
    rw [← Complex.exp_add]
    congr 1
    ring
  have hshift' :
      (∫ u in (0 : ℝ)..y,
        Complex.exp (2 * Real.pi * Complex.I * (beta * (y + u)))) =
      ∫ t in y..2 * y,
        Complex.exp (2 * Real.pi * Complex.I * (beta * t)) := by
    simpa only [Complex.ofReal_add, zero_add, add_zero, two_mul] using hshift
  exact hshift'.symm.trans hfactor

/-- Translation changes only phase, not the exact multiplier norm. -/
theorem norm_gallagherWindowKernel_eq_norm_dyadicAmplitude
    (y beta : ℝ) :
    ‖gallagherWindowKernel y beta‖ =
      ‖MAPContinuousOverlap.dyadicAmplitude y beta‖ := by
  rw [dyadicAmplitude_eq_phase_mul_gallagherWindowKernel, norm_mul]
  have hphase :
      ‖Complex.exp (2 * Real.pi * Complex.I * (beta * y))‖ = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I *
          ((beta : ℂ) * (y : ℂ)) =
        ((2 * Real.pi * beta * y : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [hphase, one_mul]

/-- Global `L²` mass of the exact Gallagher multiplier, obtained from the
already-certified dyadic interval amplitude by translation. -/
theorem integrable_sq_norm_gallagherWindowKernel
    {y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun beta => ‖gallagherWindowKernel y beta‖ ^ 2) := by
  have h := MAPContinuousOverlap.integrable_sq_norm_dyadicAmplitude hy
  apply h.congr
  filter_upwards with beta
  rw [norm_gallagherWindowKernel_eq_norm_dyadicAmplitude]

/-! ## Spatial integrability and bounded-to-L² bridge -/

/-- The continuous overlap field is integrable, proved by the same compact
Fubini support used in its exact Fourier transform. -/
theorem integrable_dyadicContinuousWindowLength
    {X y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun x : ℝ => (dyadicContinuousWindowLength X x y : ℂ)) := by
  let G : ℝ → ℝ → ℂ := fun x t =>
    (Set.Ioc X (2 * X)).indicator (fun t => slidingAtom t y x) t
  have hs := integrable_continuousSlidingSupport_indicator
    (X := X) (y := y) (beta := 0) hy
  have hprod : Integrable (Function.uncurry G) (volume.prod volume) := by
    apply hs.swap.congr
    filter_upwards with p
    rcases p with ⟨x, t⟩
    have he := phase_smul_sliding_indicator_eq_support_indicator
      X y 0 t x
    simpa [Function.comp_apply, G] using he.symm
  have hinner := hprod.integral_prod_left
  apply hinner.congr
  filter_upwards with x
  simp only [Function.uncurry_apply_pair, G]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    integral_slidingAtom_dyadic]

/-- Literal overlap length is at most the window length. -/
theorem dyadicContinuousWindowLength_le_window
    {X x y : ℝ} (hy : 0 ≤ y) :
    dyadicContinuousWindowLength X x y ≤ y := by
  unfold dyadicContinuousWindowLength
  apply max_le hy
  have hmin : min (2 * X) (x + y) ≤ x + y := min_le_right _ _
  have hmax : x ≤ max X x := le_max_right _ _
  linarith

/-- Uniform bound for the literal atomic sliding field. -/
def atomicSlidingBound (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖

theorem atomicSlidingBound_nonneg (X : ℝ) : 0 ≤ atomicSlidingBound X := by
  unfold atomicSlidingBound
  positivity

theorem norm_twistedPrimeSlidingWindow_le
    (X : ℝ) (q a : ℕ) (x y : ℝ) :
    ‖twistedPrimeSlidingWindow X q a x y‖ ≤ atomicSlidingBound X := by
  unfold twistedPrimeSlidingWindow atomicSlidingBound
  calc
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        if x < (n : ℝ) ∧ (n : ℝ) ≤ x + y then
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            fourier (n : ℤ) (rationalCenter q a)
        else 0‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖if x < (n : ℝ) ∧ (n : ℝ) ≤ x + y then
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            fourier (n : ℤ) (rationalCenter q a)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs
      · rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
      · simp

/-- A globally bounded integrable field belongs to `L²`. -/
theorem memLp_two_of_integrable_of_norm_le
    {f : ℝ → ℂ} {C : ℝ} (hf : Integrable f)
    (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    MemLp f 2 := by
  rw [memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable]
  have hg : Integrable (fun x => C * ‖f x‖) := hf.norm.const_mul C
  apply hg.mono
  · exact (hf.aestronglyMeasurable.norm.pow 2)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    have hx := hbound x
    nlinarith [norm_nonneg (f x)]

/-- Exact spatial signed field is integrable. -/
theorem integrable_signedSlidingDiscrepancy
    {X y : ℝ} (q a : ℕ) (hy : 0 ≤ y) :
    Integrable (fun x : ℝ => signedSlidingDiscrepancy X q a x y) := by
  unfold signedSlidingDiscrepancy
  exact (integrable_twistedPrimeSlidingWindow X q a y).sub
    ((integrable_dyadicContinuousWindowLength hy).const_mul
      (primeMajorCoefficient q))

/-- Uniform spatial bound retaining the signed measure rather than taking
absolute values before the discrepancy is formed. -/
theorem norm_signedSlidingDiscrepancy_le
    {X y : ℝ} (q a : ℕ) (hy : 0 ≤ y) (x : ℝ) :
    ‖signedSlidingDiscrepancy X q a x y‖ ≤
      atomicSlidingBound X + ‖primeMajorCoefficient q‖ * y := by
  unfold signedSlidingDiscrepancy
  calc
    _ ≤ ‖twistedPrimeSlidingWindow X q a x y‖ +
        ‖primeMajorCoefficient q * dyadicContinuousWindowLength X x y‖ :=
      norm_sub_le _ _
    _ ≤ atomicSlidingBound X + ‖primeMajorCoefficient q‖ * y := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (dyadicContinuousWindowLength_nonneg X x y)]
      exact add_le_add (norm_twistedPrimeSlidingWindow_le X q a x y)
        (mul_le_mul_of_nonneg_left (dyadicContinuousWindowLength_le_window hy)
          (norm_nonneg _))

theorem memLp_two_signedSlidingDiscrepancy
    {X y : ℝ} (q a : ℕ) (hy : 0 ≤ y) :
    MemLp (fun x : ℝ => signedSlidingDiscrepancy X q a x y) 2 := by
  apply memLp_two_of_integrable_of_norm_le
    (integrable_signedSlidingDiscrepancy q a hy)
  · exact add_nonneg (atomicSlidingBound_nonneg X)
      (mul_nonneg (norm_nonneg (primeMajorCoefficient q)) hy)
  · exact norm_signedSlidingDiscrepancy_le q a hy

/-! ## Exact signed Fourier pair and its global L² control -/

/-- Fourier transform respects subtraction for integrable real-line fields. -/
theorem fourier_sub_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (beta : ℝ) :
    (𝓕 (fun x => f x - g x)) beta = (𝓕 f) beta - (𝓕 g) beta := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_sub]
  apply MeasureTheory.integral_sub
  · have hc : Continuous (fun x : ℝ =>
        Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I)) := by fun_prop
    have hn : ∀ x : ℝ,
        ‖Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I)‖ ≤ 1 := by
      intro x
      rw [show (↑(-2 * Real.pi * x * beta) : ℂ) * Complex.I =
          ((-2 * Real.pi * x * beta : ℝ) : ℂ) * Complex.I by rfl,
        Complex.norm_exp_ofReal_mul_I]
    simpa only [smul_eq_mul] using
      hf.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  · have hc : Continuous (fun x : ℝ =>
        Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I)) := by fun_prop
    have hn : ∀ x : ℝ,
        ‖Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I)‖ ≤ 1 := by
      intro x
      rw [show (↑(-2 * Real.pi * x * beta) : ℂ) * Complex.I =
          ((-2 * Real.pi * x * beta : ℝ) : ℂ) * Complex.I by rfl,
        Complex.norm_exp_ofReal_mul_I]
    simpa only [smul_eq_mul] using
      hg.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)

/-- Fourier transform of a constant multiple, with Mathlib's convention. -/
theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (beta : ℝ) :
    (𝓕 (fun x => c * f x)) beta = c * (𝓕 f) beta := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  ring

/-- Exact Fourier transform of the full literal signed discrepancy. -/
theorem fourier_signedSlidingDiscrepancy
    (X y : ℝ) (q a : ℕ) (hX : 0 ≤ X) (hy : 0 ≤ y) (beta : ℝ) :
    (𝓕 (fun x : ℝ => signedSlidingDiscrepancy X q a x y)) beta =
      gallagherWindowKernel y beta *
        signedFourierDiscrepancy X q a (-beta) := by
  unfold signedSlidingDiscrepancy
  rw [fourier_sub_of_integrable
      (integrable_twistedPrimeSlidingWindow X q a y)
      ((integrable_dyadicContinuousWindowLength hy).const_mul
        (primeMajorCoefficient q)) beta,
    fourier_twistedPrimeSlidingWindow X q a y beta hy,
    fourier_const_mul,
    fourier_dyadicContinuousWindowLength X y beta hX hy]
  unfold signedFourierDiscrepancy
  push_cast
  ring

/-- Uniform frequency discrepancy bound. -/
theorem norm_signedFourierDiscrepancy_le
    {X : ℝ} (q a : ℕ) (hX : 0 ≤ X) (beta : ℝ) :
    ‖signedFourierDiscrepancy X q a beta‖ ≤
      atomicSlidingBound X + ‖primeMajorCoefficient q‖ * X := by
  unfold signedFourierDiscrepancy
  calc
    _ ≤ ‖primeExponentialSum X
        (rationalCenter q a + (beta : UnitAddCircle))‖ +
        ‖primeMajorCoefficient q * dyadicContinuousAmplitude X beta‖ :=
      norm_sub_le _ _
    _ ≤ atomicSlidingBound X + ‖primeMajorCoefficient q‖ * X := by
      apply add_le_add
      · unfold primeExponentialSum atomicSlidingBound
        calc
          ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
              (ArithmeticFunction.vonMangoldt n : ℂ) *
                fourier (n : ℤ)
                  (rationalCenter q a + (beta : UnitAddCircle))‖ ≤
            ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
              ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
                fourier (n : ℤ)
                  (rationalCenter q a + (beta : UnitAddCircle))‖ :=
            norm_sum_le _ _
          _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
              ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
      · rw [norm_mul]
        gcongr
        simpa only [dyadicContinuousAmplitude] using
          MAPContinuousOverlap.norm_dyadicAmplitude_le_length
            (X := X) (β := beta) hX

/-- Continuity of the real-frequency lift of the signed Fourier discrepancy. -/
theorem continuous_signedFourierDiscrepancy_lift
    (X : ℝ) (q a : ℕ) :
    Continuous (fun beta : ℝ => signedFourierDiscrepancy X q a beta) := by
  unfold signedFourierDiscrepancy
  exact ((MAPHarmonicEndpoint.primeExponentialSum_continuous X).comp
      (by fun_prop : Continuous (fun beta : ℝ =>
        rationalCenter q a + (beta : UnitAddCircle)))).sub
    (continuous_const.mul (by
      simpa only [dyadicContinuousAmplitude] using
        MAPContinuousOverlap.continuous_dyadicAmplitude X))

/-- The exact frequency-side product is globally in `L²`. -/
theorem memLp_two_signedFrequencyProduct
    {X y : ℝ} (q a : ℕ) (hX : 0 ≤ X) (hy : 0 ≤ y) :
    MemLp (fun beta : ℝ => gallagherWindowKernel y beta *
      signedFourierDiscrepancy X q a (-beta)) 2 := by
  rw [memLp_two_iff_integrable_sq_norm]
  · let C : ℝ := atomicSlidingBound X + ‖primeMajorCoefficient q‖ * X
    have hC : 0 ≤ C := add_nonneg (atomicSlidingBound_nonneg X)
      (mul_nonneg (norm_nonneg _) hX)
    have hg : Integrable (fun beta : ℝ =>
        C ^ 2 * ‖gallagherWindowKernel y beta‖ ^ 2) :=
      (integrable_sq_norm_gallagherWindowKernel hy).const_mul (C ^ 2)
    apply hg.mono
    · exact (((continuous_gallagherWindowKernel y).mul
        ((continuous_signedFourierDiscrepancy_lift X q a).comp
          continuous_neg)).norm.pow 2).aestronglyMeasurable
    · filter_upwards with beta
      rw [norm_mul, mul_pow]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (sq_nonneg ‖gallagherWindowKernel y beta‖)
          (sq_nonneg ‖signedFourierDiscrepancy X q a (-beta)‖)),
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg C)
          (sq_nonneg ‖gallagherWindowKernel y beta‖))]
      have hD := norm_signedFourierDiscrepancy_le q a hX (-beta)
      change ‖signedFourierDiscrepancy X q a (-beta)‖ ≤ C at hD
      have hDsq := pow_le_pow_left₀
        (norm_nonneg (signedFourierDiscrepancy X q a (-beta))) hD 2
      calc
        ‖gallagherWindowKernel y beta‖ ^ 2 *
            ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2 ≤
          ‖gallagherWindowKernel y beta‖ ^ 2 * C ^ 2 :=
            mul_le_mul_of_nonneg_left hDsq (sq_nonneg _)
        _ = C ^ 2 * ‖gallagherWindowKernel y beta‖ ^ 2 := by ring
  · exact (continuous_gallagherWindowKernel y).mul
      ((continuous_signedFourierDiscrepancy_lift X q a).comp
        continuous_neg) |>.aestronglyMeasurable

/-- Plancherel equality for the exact signed spatial/frequency pair. -/
theorem signed_gallagher_plancherel_identity
    {X y : ℝ} (q a : ℕ) (hX : 0 ≤ X) (hy : 0 ≤ y) :
    (∫ beta : ℝ,
      ‖gallagherWindowKernel y beta *
        signedFourierDiscrepancy X q a (-beta)‖ ^ 2) =
      ∫ x : ℝ, ‖signedSlidingDiscrepancy X q a x y‖ ^ 2 := by
  exact MAPGallagherPlancherel.integral_norm_sq_fourier_pair
    (integrable_signedSlidingDiscrepancy q a hy)
    (memLp_two_signedSlidingDiscrepancy q a hy)
    (memLp_two_signedFrequencyProduct q a hX hy)
    (fun beta => (fourier_signedSlidingDiscrepancy X y q a hX hy beta).symm)

/-! ## Exact Gallagher inequality with manuscript endpoints and constant 4 -/

/-- Reflection leaves the symmetric closed-band integral unchanged. -/
theorem integral_Icc_comp_neg_eq
    (f : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ beta in Set.Icc (-r) r, f (-beta)) =
      ∫ beta in Set.Icc (-r) r, f beta := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    intervalIntegral.integral_comp_neg]
  norm_num

/-- Direct literal bound with the explicit constant `4`. -/
theorem signedMeasureGallagherInequality_constant_four :
    ∀ (X y : ℝ) (q a : ℕ), 0 ≤ X → 0 < y →
      (∫ beta in Set.Icc (-(1 / (8 * y))) (1 / (8 * y)),
          ‖signedFourierDiscrepancy X q a beta‖ ^ 2) ≤
        4 / y ^ 2 *
          ∫ x : ℝ, ‖signedSlidingDiscrepancy X q a x y‖ ^ 2 := by
  intro X y q a hX hy
  have hy0 : 0 ≤ y := hy.le
  let r : ℝ := 1 / (8 * y)
  have hr : 0 ≤ r := by unfold r; positivity
  have hDcont : Continuous (fun beta : ℝ =>
      ‖signedFourierDiscrepancy X q a beta‖ ^ 2) := by
    exact (continuous_signedFourierDiscrepancy_lift X q a).norm.pow 2
  have hleftInt : IntegrableOn (fun beta : ℝ =>
      ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2) (Set.Icc (-r) r) :=
    (hDcont.comp continuous_neg).integrableOn_Icc
  have hfreq2 := memLp_two_signedFrequencyProduct q a hX hy0
  have hrightInt : Integrable (fun beta : ℝ =>
      ‖gallagherWindowKernel y beta *
        signedFourierDiscrepancy X q a (-beta)‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfreq2.1).1 hfreq2
  have hpoint : ∀ beta ∈ Set.Icc (-r) r,
      ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2 ≤
        4 / y ^ 2 *
          ‖gallagherWindowKernel y beta *
            signedFourierDiscrepancy X q a (-beta)‖ ^ 2 := by
    intro beta hbeta
    have habs : |beta| ≤ 1 / (8 * y) := by
      change |beta| ≤ r
      exact (abs_le).2 hbeta
    have hk := window_sq_le_four_mul_kernel_norm_sq hy habs
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
    rw [norm_mul, mul_pow]
    have hD0 := sq_nonneg ‖signedFourierDiscrepancy X q a (-beta)‖
    have hmul := mul_le_mul_of_nonneg_right hk hD0
    calc
      ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2 =
          y ^ 2 * ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2 /
            y ^ 2 := by field_simp
      _ ≤ (4 * ‖gallagherWindowKernel y beta‖ ^ 2 *
          ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2) / y ^ 2 := by
        exact (div_le_div_iff_of_pos_right hy2).2 hmul
      _ = 4 / y ^ 2 *
          (‖gallagherWindowKernel y beta‖ ^ 2 *
            ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2) := by ring
  have hband :
      (∫ beta in Set.Icc (-r) r,
        ‖signedFourierDiscrepancy X q a (-beta)‖ ^ 2) ≤
      4 / y ^ 2 *
        ∫ beta in Set.Icc (-r) r,
          ‖gallagherWindowKernel y beta *
            signedFourierDiscrepancy X q a (-beta)‖ ^ 2 := by
    calc
      _ ≤ ∫ beta in Set.Icc (-r) r,
          (4 / y ^ 2) *
            ‖gallagherWindowKernel y beta *
              signedFourierDiscrepancy X q a (-beta)‖ ^ 2 := by
        apply MeasureTheory.integral_mono_ae hleftInt
          (hrightInt.integrableOn.const_mul (4 / y ^ 2))
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with beta hbeta
        exact hpoint beta hbeta
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hrestrict :
      (∫ beta in Set.Icc (-r) r,
        ‖gallagherWindowKernel y beta *
          signedFourierDiscrepancy X q a (-beta)‖ ^ 2) ≤
      ∫ beta : ℝ,
        ‖gallagherWindowKernel y beta *
          signedFourierDiscrepancy X q a (-beta)‖ ^ 2 := by
    exact setIntegral_le_integral hrightInt
      (Filter.Eventually.of_forall fun beta => sq_nonneg _)
  have hcoef : 0 ≤ 4 / y ^ 2 := by positivity
  have hcombine := hband.trans (mul_le_mul_of_nonneg_left hrestrict hcoef)
  change (∫ beta in Set.Icc (-r) r,
      ‖signedFourierDiscrepancy X q a beta‖ ^ 2) ≤ _
  rw [← integral_Icc_comp_neg_eq
      (fun beta => ‖signedFourierDiscrepancy X q a beta‖ ^ 2) hr]
  rw [signed_gallagher_plancherel_identity q a hX hy0] at hcombine
  simpa only [r] using hcombine

/-- Literal repaired theorem: positive arithmetic scale, positive window,
closed Fourier band, half-open sliding intervals, signed discrepancy, and
constant `Cg=4`. -/
theorem signedMeasureGallagherInequality_proved :
    SignedMeasureGallagherInequality := by
  exact ⟨4, by norm_num, signedMeasureGallagherInequality_constant_four⟩

end
end MAPNearCollarGallagher
