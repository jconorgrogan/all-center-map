import Mathlib

/-!
# Exact half-open dyadic overlap behind the MAP continuous kernel

This module proves the spatial specialization in the major-arc calculation.
It does not assume a prime-pair or major-arc theorem.
-/

namespace MAPContinuousOverlap

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

/-- The continuous dyadic amplitude used in the paper's major-arc model. -/
def dyadicAmplitude (X β : ℝ) : ℂ :=
  ∫ x in X..2 * X,
    Complex.exp (2 * Real.pi * Complex.I * (β * x))

theorem dyadicAmplitude_eq_quotient
    {X β : ℝ} (hβ : β ≠ 0) :
    dyadicAmplitude X β =
      (Complex.exp ((2 * Real.pi * Complex.I * β) * (2 * X)) -
        Complex.exp ((2 * Real.pi * Complex.I * β) * X)) /
          (2 * Real.pi * Complex.I * β) := by
  unfold dyadicAmplitude
  have hc : (2 * Real.pi * Complex.I * (β : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hβ)
  convert integral_exp_mul_complex (a := X) (b := 2 * X) hc using 1 <;>
    congr 2 <;> push_cast <;> ring_nf

theorem norm_dyadicAmplitude_le_inv
    {X β : ℝ} (hβ : β ≠ 0) :
    ‖dyadicAmplitude X β‖ ≤ 1 / (Real.pi * |β|) := by
  rw [dyadicAmplitude_eq_quotient hβ, norm_div]
  have hnum :
      ‖Complex.exp ((2 * Real.pi * Complex.I * β) * (2 * X)) -
        Complex.exp ((2 * Real.pi * Complex.I * β) * X)‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp ((2 * Real.pi * Complex.I * β) * (2 * X))‖ +
          ‖Complex.exp ((2 * Real.pi * Complex.I * β) * X)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        norm_num
  have hden : ‖(2 * Real.pi * Complex.I * (β : ℂ))‖ =
      2 * Real.pi * |β| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num [abs_of_pos Real.pi_pos]
  rw [hden]
  have hpos : 0 < Real.pi * |β| :=
    mul_pos Real.pi_pos (abs_pos.mpr hβ)
  calc
    ‖Complex.exp ((2 * Real.pi * Complex.I * β) * (2 * X)) -
          Complex.exp ((2 * Real.pi * Complex.I * β) * X)‖ /
        (2 * Real.pi * |β|) ≤ 2 / (2 * Real.pi * |β|) := by
      exact (div_le_div_iff_of_pos_right (by positivity)).2 hnum
    _ = 1 / (Real.pi * |β|) := by
      field_simp

theorem continuous_dyadicAmplitude (X : ℝ) :
    Continuous (dyadicAmplitude X) := by
  unfold dyadicAmplitude
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem norm_dyadicAmplitude_le_length
    {X β : ℝ} (hX : 0 ≤ X) :
    ‖dyadicAmplitude X β‖ ≤ X := by
  unfold dyadicAmplitude
  calc
    ‖∫ x in X..2 * X, Complex.exp
        (2 * Real.pi * Complex.I * (β * x))‖ ≤ 1 * |2 * X - X| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Complex.norm_exp]
      norm_num
    _ = X := by rw [one_mul, show 2 * X - X = X by ring, abs_of_nonneg hX]

theorem dyadicAmplitude_neg
    {X : ℝ} (hX : 0 ≤ X) (β : ℝ) :
    dyadicAmplitude X (-β) = conj (dyadicAmplitude X β) := by
  unfold dyadicAmplitude
  rw [intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by linarith)]
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have harg :
      (2 * Real.pi * Complex.I * (((-β : ℝ) : ℂ) * (x : ℂ))) =
        conj (2 * Real.pi * Complex.I * ((β : ℂ) * (x : ℂ))) := by
    apply Complex.ext <;> simp
  change Complex.exp
      (2 * Real.pi * Complex.I * (((-β : ℝ) : ℂ) * (x : ℂ))) =
    conj (Complex.exp
      (2 * Real.pi * Complex.I * ((β : ℂ) * (x : ℂ))))
  rw [harg, Complex.exp_conj]

theorem norm_dyadicAmplitude_neg
    {X : ℝ} (hX : 0 ≤ X) (β : ℝ) :
    ‖dyadicAmplitude X (-β)‖ = ‖dyadicAmplitude X β‖ := by
  rw [dyadicAmplitude_neg hX, Complex.norm_conj]

theorem sq_norm_dyadicAmplitude_le_inv
    {X β : ℝ} (hβ : β ≠ 0) :
    ‖dyadicAmplitude X β‖ ^ 2 ≤
      (Real.pi ^ 2 * β ^ 2)⁻¹ := by
  have h := norm_dyadicAmplitude_le_inv (X := X) hβ
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  calc
    ‖dyadicAmplitude X β‖ ^ 2 ≤ (1 / (Real.pi * |β|)) ^ 2 := hs
    _ = (Real.pi ^ 2 * β ^ 2)⁻¹ := by
      rw [div_pow]
      field_simp
      rw [sq_abs]

/-- One-sided Fourier tail mass. -/
def positiveAmplitudeTail (X R : ℝ) : ℝ :=
  ∫ β in Ioi R, ‖dyadicAmplitude X β‖ ^ 2

theorem integrableOn_positiveAmplitudeTail
    {X R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun β => ‖dyadicAmplitude X β‖ ^ 2) (Ioi R) := by
  let g : ℝ → ℝ := fun β => (Real.pi ^ 2)⁻¹ * β ^ (-2 : ℝ)
  have hg : IntegrableOn g (Ioi R) := by
    exact (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hR).const_mul _
  apply hg.mono'
  · exact ((continuous_dyadicAmplitude X).norm.pow 2).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with β hβ
    have hβpos : 0 < β := hR.trans hβ
    have hbound := sq_norm_dyadicAmplitude_le_inv (X := X) hβpos.ne'
    have hrpow : β ^ (-2 : ℝ) = (β ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hβpos.le, Real.rpow_two]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [g, hrpow]
    calc
      ‖dyadicAmplitude X β‖ ^ 2 ≤ (Real.pi ^ 2 * β ^ 2)⁻¹ := hbound
      _ = (Real.pi ^ 2)⁻¹ * (β ^ 2)⁻¹ := by rw [mul_inv_rev]; ring

theorem positiveAmplitudeTail_le
    {X R : ℝ} (hR : 0 < R) :
    positiveAmplitudeTail X R ≤ 1 / (Real.pi ^ 2 * R) := by
  let g : ℝ → ℝ := fun β => (Real.pi ^ 2)⁻¹ * β ^ (-2 : ℝ)
  have hf := integrableOn_positiveAmplitudeTail (X := X) hR
  have hg : IntegrableOn g (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hR).const_mul _
  have hmono : positiveAmplitudeTail X R ≤ ∫ β in Ioi R, g β := by
    unfold positiveAmplitudeTail
    apply integral_mono_ae hf hg
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with β hβ
    have hβpos : 0 < β := hR.trans hβ
    have hbound := sq_norm_dyadicAmplitude_le_inv (X := X) hβpos.ne'
    have hrpow : β ^ (-2 : ℝ) = (β ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hβpos.le, Real.rpow_two]
    simp only [g, hrpow]
    calc
      ‖dyadicAmplitude X β‖ ^ 2 ≤ (Real.pi ^ 2 * β ^ 2)⁻¹ := hbound
      _ = (Real.pi ^ 2)⁻¹ * (β ^ 2)⁻¹ := by rw [mul_inv_rev]; ring
  calc
    positiveAmplitudeTail X R ≤ ∫ β in Ioi R, g β := hmono
    _ = (Real.pi ^ 2)⁻¹ * (∫ β in Ioi R, β ^ (-2 : ℝ)) := by
      exact MeasureTheory.integral_const_mul _ _
    _ = (Real.pi ^ 2)⁻¹ * R⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hR]
      norm_num
      rw [Real.rpow_neg_one]
    _ = 1 / (Real.pi ^ 2 * R) := by
      field_simp

/-- The two tails `β>R` and `β<-R`, written after reflection of the negative
tail to `β>R`. -/
def symmetricAmplitudeTail (X R : ℝ) : ℝ :=
  (∫ β in Ioi R, ‖dyadicAmplitude X β‖ ^ 2) +
    ∫ β in Ioi R, ‖dyadicAmplitude X (-β)‖ ^ 2

theorem symmetricAmplitudeTail_le
    {X R : ℝ} (hR : 0 < R) :
    symmetricAmplitudeTail X R ≤ 2 / (Real.pi ^ 2 * R) := by
  have hpos := positiveAmplitudeTail_le (X := X) hR
  have hneg :
      (∫ β in Ioi R, ‖dyadicAmplitude X (-β)‖ ^ 2) ≤
        1 / (Real.pi ^ 2 * R) := by
    let g : ℝ → ℝ := fun β => (Real.pi ^ 2)⁻¹ * β ^ (-2 : ℝ)
    have hg : IntegrableOn g (Ioi R) :=
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hR).const_mul _
    have hf : IntegrableOn (fun β => ‖dyadicAmplitude X (-β)‖ ^ 2) (Ioi R) := by
      apply hg.mono'
      · exact (((continuous_dyadicAmplitude X).comp continuous_neg).norm.pow 2).aestronglyMeasurable
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with β hβ
        have hβpos : 0 < β := hR.trans hβ
        have hbound := sq_norm_dyadicAmplitude_le_inv
          (X := X) (neg_ne_zero.mpr hβpos.ne')
        have hrpow : β ^ (-2 : ℝ) = (β ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
            Real.rpow_neg hβpos.le, Real.rpow_two]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simp only [g, hrpow]
        calc
          ‖dyadicAmplitude X (-β)‖ ^ 2 ≤
              (Real.pi ^ 2 * (-β) ^ 2)⁻¹ := hbound
          _ = (Real.pi ^ 2)⁻¹ * (β ^ 2)⁻¹ := by
            rw [neg_sq, mul_inv_rev]
            ring
    have hmono :
        (∫ β in Ioi R, ‖dyadicAmplitude X (-β)‖ ^ 2) ≤
          ∫ β in Ioi R, g β := by
      apply integral_mono_ae hf hg
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with β hβ
      have hβpos : 0 < β := hR.trans hβ
      have hbound := sq_norm_dyadicAmplitude_le_inv
        (X := X) (neg_ne_zero.mpr hβpos.ne')
      have hrpow : β ^ (-2 : ℝ) = (β ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
          Real.rpow_neg hβpos.le, Real.rpow_two]
      simp only [g, hrpow]
      calc
        ‖dyadicAmplitude X (-β)‖ ^ 2 ≤
            (Real.pi ^ 2 * (-β) ^ 2)⁻¹ := hbound
        _ = (Real.pi ^ 2)⁻¹ * (β ^ 2)⁻¹ := by
          rw [neg_sq, mul_inv_rev]
          ring
    calc
      _ ≤ ∫ β in Ioi R, g β := hmono
      _ = (Real.pi ^ 2)⁻¹ * (∫ β in Ioi R, β ^ (-2 : ℝ)) := by
        exact MeasureTheory.integral_const_mul _ _
      _ = (Real.pi ^ 2)⁻¹ * R⁻¹ := by
        rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hR]
        norm_num
        rw [Real.rpow_neg_one]
      _ = 1 / (Real.pi ^ 2 * R) := by field_simp
  have hpos' :
      (∫ β in Ioi R, ‖dyadicAmplitude X β‖ ^ 2) ≤
        1 / (Real.pi ^ 2 * R) := by
    simpa only [positiveAmplitudeTail] using hpos
  unfold symmetricAmplitudeTail
  calc
    _ ≤ 1 / (Real.pi ^ 2 * R) + 1 / (Real.pi ^ 2 * R) :=
      add_le_add hpos' hneg
    _ = 2 / (Real.pi ^ 2 * R) := by ring

theorem integrable_sq_norm_dyadicAmplitude
    {X : ℝ} (hX : 0 ≤ X) :
    Integrable (fun β => ‖dyadicAmplitude X β‖ ^ 2) := by
  let f : ℝ → ℝ := fun β => ‖dyadicAmplitude X β‖ ^ 2
  have hpos : IntegrableOn f (Ioi (1 : ℝ)) := by
    simpa only [f] using
      (integrableOn_positiveAmplitudeTail (X := X) (show (0 : ℝ) < 1 by norm_num))
  have hneg : IntegrableOn f (Iio (-1 : ℝ)) := by
    have hmp := ((volume : Measure ℝ).measurePreserving_neg).restrict_preimage
      (s := Ioi (1 : ℝ)) measurableSet_Ioi
    have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hcomp : Integrable (fun β => f (-β))
        (volume.restrict ((fun x : ℝ => -x) ⁻¹' Ioi (1 : ℝ))) :=
      (hmp.integrable_comp_emb hemb).2 hpos
    have hpre : ((fun x : ℝ => -x) ⁻¹' Ioi (1 : ℝ)) = Iio (-1 : ℝ) := by
      ext x
      simp
    rw [hpre] at hcomp
    apply hcomp.congr
    filter_upwards with β
    simp only [f]
    rw [norm_dyadicAmplitude_neg hX]
  have hmid : IntegrableOn f (Icc (-1 : ℝ) 1) := by
    exact ((continuous_dyadicAmplitude X).norm.pow 2).integrableOn_Icc
  have hall : IntegrableOn f
      ((Iio (-1 : ℝ) ∪ Icc (-1 : ℝ) 1) ∪ Ioi (1 : ℝ)) :=
    (hneg.union hmid).union hpos
  have huniv : ((Iio (-1 : ℝ) ∪ Icc (-1 : ℝ) 1) ∪ Ioi (1 : ℝ)) = univ := by
    ext x
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases hx : x < -1
    · exact Or.inl (Or.inl hx)
    by_cases hx' : x ≤ 1
    · exact Or.inl (Or.inr ⟨le_of_not_gt hx, hx'⟩)
    · exact Or.inr (lt_of_not_ge hx')
  rw [huniv, integrableOn_univ] at hall
  exact hall

def oscillatoryKernelIntegrand (X h β : ℝ) : ℂ :=
  ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * (h * β))

theorem integrable_oscillatoryKernelIntegrand
    {X h : ℝ} (hX : 0 ≤ X) :
    Integrable (oscillatoryKernelIntegrand X h) := by
  have hf : Integrable (fun β : ℝ => ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ)) :=
    (integrable_sq_norm_dyadicAmplitude hX).ofReal
  have hphase : Continuous (fun β : ℝ =>
      Complex.exp (-2 * Real.pi * Complex.I * (h * β))) := by
    fun_prop
  have hbound : ∀ᵐ β : ℝ ∂volume,
      ‖Complex.exp (-2 * Real.pi * Complex.I * (h * β))‖ ≤ 1 := by
    apply ae_of_all
    intro β
    rw [Complex.norm_exp]
    norm_num
  unfold oscillatoryKernelIntegrand
  exact hf.mul_bdd hphase.aestronglyMeasurable hbound

def fullDyadicBetaKernel (X h : ℝ) : ℂ :=
  ∫ β : ℝ, oscillatoryKernelIntegrand X h β

def truncatedDyadicBetaKernel (X R h : ℝ) : ℂ :=
  ∫ β in -R..R, oscillatoryKernelIntegrand X h β

theorem norm_oscillatoryKernelIntegrand (X h β : ℝ) :
    ‖oscillatoryKernelIntegrand X h β‖ = ‖dyadicAmplitude X β‖ ^ 2 := by
  unfold oscillatoryKernelIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), Complex.norm_exp]
  norm_num

/-- The complete continuous beta-kernel differs from its symmetric truncation
by no more than the literal two-tail mass.  This is the MAP-owned truncation
weld: the proof uses only integrability, the exact interval decomposition, and
the unit norm of the oscillatory phase. -/
theorem norm_fullDyadicBetaKernel_sub_truncated_le_symmetricTail
    {X R h : ℝ} (hX : 0 ≤ X) :
    ‖fullDyadicBetaKernel X h - truncatedDyadicBetaKernel X R h‖ ≤
      symmetricAmplitudeTail X R := by
  let k : ℝ → ℂ := oscillatoryKernelIntegrand X h
  have hk : Integrable k := integrable_oscillatoryKernelIntegrand hX
  have hfull := intervalIntegral.integral_Iic_add_Ioi
    (b := R) hk.integrableOn hk.integrableOn
  have hcenter := intervalIntegral.integral_Iic_sub_Iic
    (a := -R) (b := R) hk.integrableOn hk.integrableOn
  have hdecomp :
      fullDyadicBetaKernel X h - truncatedDyadicBetaKernel X R h =
        (∫ β in Iic (-R), k β) + ∫ β in Ioi R, k β := by
    unfold fullDyadicBetaKernel truncatedDyadicBetaKernel
    change (∫ β : ℝ, k β) - (∫ β in -R..R, k β) = _
    rw [← hfull, ← hcenter]
    abel
  have hpos :
      ‖∫ β in Ioi R, k β‖ ≤
        ∫ β in Ioi R, ‖dyadicAmplitude X β‖ ^ 2 := by
    calc
      ‖∫ β in Ioi R, k β‖ ≤ ∫ β in Ioi R, ‖k β‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ β in Ioi R, ‖dyadicAmplitude X β‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro β hβ
        exact norm_oscillatoryKernelIntegrand X h β
  have hneg :
      ‖∫ β in Iic (-R), k β‖ ≤
        ∫ β in Ioi R, ‖dyadicAmplitude X (-β)‖ ^ 2 := by
    calc
      ‖∫ β in Iic (-R), k β‖ =
          ‖∫ β in Ioi R, k (-β)‖ := by
            rw [integral_comp_neg_Ioi]
      _ ≤ ∫ β in Ioi R, ‖k (-β)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ β in Ioi R, ‖dyadicAmplitude X (-β)‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro β hβ
        exact norm_oscillatoryKernelIntegrand X h (-β)
  rw [hdecomp]
  calc
    ‖(∫ β in Iic (-R), k β) + ∫ β in Ioi R, k β‖ ≤
        ‖∫ β in Iic (-R), k β‖ + ‖∫ β in Ioi R, k β‖ :=
      norm_add_le _ _
    _ ≤ (∫ β in Ioi R, ‖dyadicAmplitude X (-β)‖ ^ 2) +
        ∫ β in Ioi R, ‖dyadicAmplitude X β‖ ^ 2 :=
      add_le_add hneg hpos
    _ = symmetricAmplitudeTail X R := by
      unfold symmetricAmplitudeTail
      ac_rfl

theorem norm_fullDyadicBetaKernel_sub_truncated_le
    {X R h : ℝ} (hX : 0 ≤ X) (hR : 0 < R) :
    ‖fullDyadicBetaKernel X h - truncatedDyadicBetaKernel X R h‖ ≤
      2 / (Real.pi ^ 2 * R) := by
  exact (norm_fullDyadicBetaKernel_sub_truncated_le_symmetricTail hX).trans
    (symmetricAmplitudeTail_le hR)

/-- The exact half-open support overlap appearing after Plancherel. -/
def dyadicOverlapSet (X h : ℝ) : Set ℝ :=
  {x | x ∈ Ioc X (2 * X) ∧ x + h ∈ Ioc X (2 * X)}

theorem dyadicOverlapSet_eq_Ioc (X h : ℝ) :
    dyadicOverlapSet X h =
      Ioc (max X (X - h)) (min (2 * X) (2 * X - h)) := by
  ext x
  simp only [dyadicOverlapSet, mem_setOf_eq, mem_Ioc]
  constructor
  · rintro ⟨⟨hXx, hx2X⟩, hshiftX, hshift2X⟩
    exact ⟨(max_lt_iff.mpr ⟨hXx, by linarith⟩),
      (le_min_iff.mpr ⟨hx2X, by linarith⟩)⟩
  · rintro ⟨hlo, hhi⟩
    rw [max_lt_iff] at hlo
    rw [le_min_iff] at hhi
    exact ⟨⟨hlo.1, hhi.1⟩, by constructor <;> linarith⟩

/-- Lebesgue length of the exact half-open overlap. -/
def dyadicOverlapLength (X h : ℝ) : ℝ :=
  (volume (dyadicOverlapSet X h)).toReal

theorem dyadicOverlapLength_eq_general (X h : ℝ) :
    dyadicOverlapLength X h =
      ENNReal.toReal (ENNReal.ofReal
        (min (2 * X) (2 * X - h) - max X (X - h))) := by
  rw [dyadicOverlapLength, dyadicOverlapSet_eq_Ioc, Real.volume_Ioc]

/-- Exact `X-|h|` coefficient, including the endpoint `|h|=X` where the
half-open intersection has measure zero. -/
theorem dyadicOverlapLength_eq_sub_abs
    {X h : ℝ} (hh : |h| ≤ X) :
    dyadicOverlapLength X h = X - |h| := by
  rw [dyadicOverlapLength_eq_general]
  have hnonneg : 0 ≤ X - |h| := sub_nonneg.mpr hh
  rcases le_total 0 h with hhpos | hhneg
  · rw [max_eq_left (by linarith), min_eq_right (by linarith),
      abs_of_nonneg hhpos]
    have hsub : 0 ≤ X - h := by
      rw [← abs_of_nonneg hhpos]
      exact hnonneg
    rw [show 2 * X - h - X = X - h by ring,
      ENNReal.toReal_ofReal hsub]
  · rw [max_eq_right (by linarith), min_eq_left (by linarith),
      abs_of_nonpos hhneg]
    have heq : 2 * X - (X - h) = X - -h := by ring
    have hsub : 0 ≤ X - -h := by
      rw [← abs_of_nonpos hhneg]
      exact hnonneg
    rw [heq, ENNReal.toReal_ofReal hsub]

theorem dyadicOverlapLength_eq_zero_of_abs_eq
    {X h : ℝ} (hh : |h| = X) :
    dyadicOverlapLength X h = 0 := by
  rw [dyadicOverlapLength_eq_sub_abs hh.le, hh, sub_self]

/-- The spatial autocorrelation integral is literally the overlap length. -/
theorem integral_indicator_mul_shifted_indicator
    (X h : ℝ) :
    (∫ x : ℝ,
      (Ioc X (2 * X)).indicator (fun _ => (1 : ℝ)) x *
      (Ioc X (2 * X)).indicator (fun _ => (1 : ℝ)) (x + h)) =
      dyadicOverlapLength X h := by
  rw [dyadicOverlapLength]
  calc
    (∫ x : ℝ,
      (Ioc X (2 * X)).indicator (fun _ => (1 : ℝ)) x *
        (Ioc X (2 * X)).indicator (fun _ => (1 : ℝ)) (x + h)) =
      ∫ x : ℝ, (dyadicOverlapSet X h).indicator (fun _ => (1 : ℝ)) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioc X (2 * X)
        · by_cases hs : x + h ∈ Ioc X (2 * X)
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hs,
              Set.indicator_of_mem (show x ∈ dyadicOverlapSet X h from ⟨hx, hs⟩)]
            norm_num
          · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hs,
              Set.indicator_of_notMem
                (show x ∉ dyadicOverlapSet X h from fun hx' => hs hx'.2)]
            norm_num
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem
              (show x ∉ dyadicOverlapSet X h from fun hx' => hx hx'.1)]
          norm_num
    _ = volume.real (dyadicOverlapSet X h) := by
      change (∫ x : ℝ, (dyadicOverlapSet X h).indicator (1 : ℝ → ℝ) x) = _
      apply integral_indicator_one
      rw [dyadicOverlapSet_eq_Ioc]
      exact measurableSet_Ioc
    _ = (volume (dyadicOverlapSet X h)).toReal := rfl

/-! ## General Wiener--Khinchin interface and exact dyadic specialization -/

def dyadicIndicator (X : ℝ) : ℝ → ℂ :=
  (Ioc X (2 * X)).indicator (fun _ => (1 : ℂ))

/-- Positive-sign Fourier transform, matching `dyadicAmplitude`. -/
def positiveFourier (f : ℝ → ℂ) (β : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (2 * Real.pi * Complex.I * (β * x)) * f x

def spectralAutocorrelation (f : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ β : ℝ,
    ((‖positiveFourier f β‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (-2 * Real.pi * Complex.I * (h * β))

def physicalAutocorrelation (f : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ x : ℝ, conj (f x) * f (x + h)

theorem dyadicIndicator_integrable (X : ℝ) : Integrable (dyadicIndicator X) := by
  unfold dyadicIndicator
  exact continuous_const.integrableOn_Ioc.integrable_indicator measurableSet_Ioc

theorem dyadicIndicator_memLp_two (X : ℝ) : MemLp (dyadicIndicator X) 2 := by
  rw [memLp_two_iff_integrable_sq_norm
    ((dyadicIndicator_integrable X).aestronglyMeasurable)]
  have hi : Integrable ((Ioc X (2 * X)).indicator (fun _ => (1 : ℝ))) :=
    continuous_const.integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ Ioc X (2 * X)
  · simp [dyadicIndicator, hx]
  · simp [dyadicIndicator, hx]

theorem dyadicAmplitude_eq_positiveFourier
    {X : ℝ} (hX : 0 ≤ X) (β : ℝ) :
    dyadicAmplitude X β = positiveFourier (dyadicIndicator X) β := by
  unfold dyadicAmplitude positiveFourier dyadicIndicator
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioc X (2 * X)
  · simp [hx]
  · simp [hx]

theorem physicalAutocorrelation_dyadicIndicator_eq
    (X h : ℝ) :
    physicalAutocorrelation (dyadicIndicator X) h =
      (dyadicOverlapLength X h : ℂ) := by
  unfold physicalAutocorrelation dyadicIndicator dyadicOverlapLength
  calc
    (∫ x : ℝ,
      conj ((Ioc X (2 * X)).indicator (fun _ => (1 : ℂ)) x) *
        (Ioc X (2 * X)).indicator (fun _ => (1 : ℂ)) (x + h)) =
      ∫ x : ℝ, (dyadicOverlapSet X h).indicator (fun _ => (1 : ℂ)) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioc X (2 * X)
        · by_cases hs : x + h ∈ Ioc X (2 * X)
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hs,
              Set.indicator_of_mem (show x ∈ dyadicOverlapSet X h from ⟨hx, hs⟩)]
            norm_num
          · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hs,
              Set.indicator_of_notMem
                (show x ∉ dyadicOverlapSet X h from fun hx' => hs hx'.2)]
            norm_num
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem
              (show x ∉ dyadicOverlapSet X h from fun hx' => hx hx'.1)]
          norm_num
    _ = (volume.real (dyadicOverlapSet X h) : ℂ) := by
      change (∫ x : ℝ,
        (dyadicOverlapSet X h).indicator (1 : ℝ → ℂ) x) = _
      have hm : MeasurableSet (dyadicOverlapSet X h) := by
        rw [dyadicOverlapSet_eq_Ioc]
        exact measurableSet_Ioc
      simpa using (integral_indicator_const (μ := volume) (1 : ℂ) hm)
    _ = ((volume (dyadicOverlapSet X h)).toReal : ℂ) := rfl

/-- Exact Fourier/Plancherel specialization.  The sole premise is the general
Wiener--Khinchin theorem for every integrable `L²` function, a standard
external Fourier-analysis contract.  It does not mention dyadic intervals,
prime pairs, major arcs, or the desired `X-|h|` conclusion. -/
theorem spectralAutocorrelation_dyadic_eq_sub_abs_of_wienerKhinchin
    (wienerKhinchin :
      ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
        ∀ t : ℝ, spectralAutocorrelation f t = physicalAutocorrelation f t)
    {X h : ℝ} (hh : |h| ≤ X) :
    spectralAutocorrelation (dyadicIndicator X) h = ((X - |h| : ℝ) : ℂ) := by
  rw [wienerKhinchin (dyadicIndicator X) (dyadicIndicator_integrable X)
    (dyadicIndicator_memLp_two X) h,
    physicalAutocorrelation_dyadicIndicator_eq,
    dyadicOverlapLength_eq_sub_abs hh]

/-- The paper's full continuous beta-kernel is the preceding spectral
autocorrelation after rewriting the interval amplitude. -/
theorem full_dyadic_beta_kernel_eq_sub_abs_of_wienerKhinchin
    (wienerKhinchin :
      ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
        ∀ t : ℝ, spectralAutocorrelation f t = physicalAutocorrelation f t)
    {X h : ℝ} (hX : 0 ≤ X) (hh : |h| ≤ X) :
    (∫ β : ℝ,
      ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (h * β))) =
      ((X - |h| : ℝ) : ℂ) := by
  rw [← spectralAutocorrelation_dyadic_eq_sub_abs_of_wienerKhinchin
    wienerKhinchin hh]
  unfold spectralAutocorrelation
  apply integral_congr_ae
  filter_upwards with β
  rw [dyadicAmplitude_eq_positiveFourier hX]

/-- The manuscript's truncated continuous major-arc kernel has the exact
`X - |h|` main term and an explicit `2/(π²R)` tail.  All interval and tail
welding is proved above; only the general Wiener--Khinchin identity remains as
an external Fourier-analysis contract. -/
theorem truncated_dyadic_beta_kernel_approximates_sub_abs_of_wienerKhinchin
    (wienerKhinchin :
      ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
        ∀ t : ℝ, spectralAutocorrelation f t = physicalAutocorrelation f t)
    {X R h : ℝ} (hX : 0 ≤ X) (hh : |h| ≤ X) (hR : 0 < R) :
    ‖truncatedDyadicBetaKernel X R h - ((X - |h| : ℝ) : ℂ)‖ ≤
      2 / (Real.pi ^ 2 * R) := by
  have hfull : fullDyadicBetaKernel X h = ((X - |h| : ℝ) : ℂ) := by
    unfold fullDyadicBetaKernel
    exact full_dyadic_beta_kernel_eq_sub_abs_of_wienerKhinchin
      wienerKhinchin hX hh
  calc
    ‖truncatedDyadicBetaKernel X R h - ((X - |h| : ℝ) : ℂ)‖ =
        ‖truncatedDyadicBetaKernel X R h - fullDyadicBetaKernel X h‖ := by
      rw [hfull]
    _ = ‖fullDyadicBetaKernel X h - truncatedDyadicBetaKernel X R h‖ :=
      norm_sub_rev _ _
    _ ≤ 2 / (Real.pi ^ 2 * R) :=
      norm_fullDyadicBetaKernel_sub_truncated_le hX hR

end

end MAPContinuousOverlap
