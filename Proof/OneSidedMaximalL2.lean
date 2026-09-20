import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OneSidedMaximalL2

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Right-moving average, parameterized by the offset `u ∈ (0,Y]`. -/
def rightAverage (f : ℝ → ℝ≥0∞) (Y x : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal Y)⁻¹ * ∫⁻ u in Ioc 0 Y, f (x + u)

/-- The quadratic moving-energy average. -/
def rightSquareAverage (f : ℝ → ℝ≥0∞) (Y x : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal Y)⁻¹ * ∫⁻ u in Ioc 0 Y, (f (x + u)) ^ 2

/-- Exact interval/offset normalization adapter. -/
theorem rightAverage_eq_interval (f : ℝ → ℝ≥0∞) (Y x : ℝ) :
    rightAverage f Y x =
      (ENNReal.ofReal Y)⁻¹ * ∫⁻ t in Ioc x (x + Y), f t := by
  unfold rightAverage
  congr 1
  rw [← lintegral_indicator measurableSet_Ioc,
    ← lintegral_indicator measurableSet_Ioc]
  have hpoint (u : ℝ) :
      (Ioc (0 : ℝ) Y).indicator (fun v => f (x + v)) u =
        (Ioc x (x + Y)).indicator f (x + u) := by
    by_cases hu : u ∈ Ioc (0 : ℝ) Y
    · have hxu : x + u ∈ Ioc x (x + Y) := by
        constructor <;> linarith [hu.1, hu.2]
      simp [hu, hxu]
    · have hxu : x + u ∉ Ioc x (x + Y) := by
        intro hxumem
        apply hu
        constructor <;> linarith [hxumem.1, hxumem.2]
      simp [hu, hxu]
  simp_rw [hpoint]
  exact lintegral_add_left_eq_self
    ((Ioc x (x + Y)).indicator f) x

lemma volume_Ioc_zero (Y : ℝ) :
    volume (Ioc (0 : ℝ) Y) = ENNReal.ofReal Y := by
  rw [Real.volume_Ioc]
  simp

lemma holder_rightAverage_aux (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {Y x : ℝ} :
    (∫⁻ u in Ioc 0 Y, f (x + u)) ≤
      (∫⁻ u in Ioc 0 Y, (f (x + u)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal Y) ^ (1 / (2 : ℝ)) := by
  have hcomp : Measurable (fun u : ℝ => f (x + u)) :=
    hf.comp (measurable_const.add measurable_id)
  have hone : Measurable (fun _u : ℝ => (1 : ℝ≥0∞)) := measurable_const
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Ioc (0 : ℝ) Y)) hholder hcomp.aemeasurable hone.aemeasurable
  simpa [Pi.mul_apply, lintegral_const, Measure.restrict_apply_univ,
    volume_Ioc_zero] using h

lemma rpow_half_sq (a : ℝ≥0∞) :
    (a ^ (1 / (2 : ℝ))) ^ (2 : ℕ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy--Schwarz on one right interval, in the exact normalized form
needed before integrating in the base point. -/
theorem rightAverage_sq_le_rightSquareAverage
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) {Y x : ℝ} (hY : 0 < Y) :
    (rightAverage f Y x) ^ 2 ≤ rightSquareAverage f Y x := by
  let y : ℝ≥0∞ := ENNReal.ofReal Y
  let A : ℝ≥0∞ := ∫⁻ u in Ioc 0 Y, f (x + u)
  let B : ℝ≥0∞ := ∫⁻ u in Ioc 0 Y, (f (x + u)) ^ 2
  have hy0 : y ≠ 0 := by simp [y, hY]
  have hytop : y ≠ ⊤ := ENNReal.ofReal_ne_top
  have hAB : A ≤ B ^ (1 / (2 : ℝ)) * y ^ (1 / (2 : ℝ)) := by
    simpa [A, B, y] using holder_rightAverage_aux f hf (Y := Y) (x := x)
  have hsq : A ^ 2 ≤ B * y := by
    have := pow_le_pow_left' hAB 2
    rw [mul_pow, rpow_half_sq, rpow_half_sq] at this
    exact this
  change (y⁻¹ * A) ^ 2 ≤ y⁻¹ * B
  rw [mul_pow]
  calc
    y⁻¹ ^ 2 * A ^ 2 ≤ y⁻¹ ^ 2 * (B * y) :=
      mul_le_mul_left' hsq _
    _ = y⁻¹ * B := by
      rw [pow_two]
      calc
        y⁻¹ * y⁻¹ * (B * y) = y⁻¹ * B * (y⁻¹ * y) := by
          ac_rfl
        _ = y⁻¹ * B := by rw [ENNReal.inv_mul_cancel hy0 hytop, mul_one]

lemma measurable_rightSquareIntegral (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (Y : ℝ) :
    Measurable fun x : ℝ => ∫⁻ u in Ioc 0 Y, (f (x + u)) ^ 2 := by
  have hprod : Measurable fun p : ℝ × ℝ => (f (p.1 + p.2)) ^ 2 := by
    fun_prop
  exact hprod.lintegral_prod_right'

/-- A fixed right-moving average is an `L²` contraction.  This is the exact
translation/Fubini adapter absent from Mathlib's public API. -/
theorem lintegral_rightSquareAverage_eq
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) {Y : ℝ} (hY : 0 < Y) :
    (∫⁻ x : ℝ, rightSquareAverage f Y x) =
      ∫⁻ x : ℝ, (f x) ^ 2 := by
  let y : ℝ≥0∞ := ENNReal.ofReal Y
  have hy0 : y ≠ 0 := by simp [y, hY]
  have hytop : y ≠ ⊤ := ENNReal.ofReal_ne_top
  have hprod : AEMeasurable
      (Function.uncurry fun x u : ℝ => (f (x + u)) ^ 2)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) Y))) := by
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => (f (p.1 + p.2)) ^ 2).aemeasurable
  have hswap :
      (∫⁻ x : ℝ, ∫⁻ u in Ioc 0 Y, (f (x + u)) ^ 2) =
        ∫⁻ u in Ioc 0 Y, ∫⁻ x : ℝ, (f (x + u)) ^ 2 :=
    lintegral_lintegral_swap hprod
  have htranslate (u : ℝ) :
      (∫⁻ x : ℝ, (f (x + u)) ^ 2) = ∫⁻ x : ℝ, (f x) ^ 2 := by
    exact lintegral_add_right_eq_self (fun x : ℝ => (f x) ^ 2) u
  change (∫⁻ x : ℝ, y⁻¹ *
      (∫⁻ u in Ioc 0 Y, (f (x + u)) ^ 2)) = _
  rw [lintegral_const_mul y⁻¹ (measurable_rightSquareIntegral f hf Y)]
  rw [hswap]
  simp_rw [htranslate]
  rw [setLIntegral_const, Real.volume_Ioc]
  simp only [sub_zero]
  calc
    y⁻¹ * ((∫⁻ x : ℝ, (f x) ^ 2) * y) =
        (y⁻¹ * y) * ∫⁻ x : ℝ, (f x) ^ 2 := by ac_rfl
    _ = ∫⁻ x : ℝ, (f x) ^ 2 := by
      rw [ENNReal.inv_mul_cancel hy0 hytop, one_mul]

/-- Fixed-scale `L²` contraction for right averages. -/
theorem lintegral_rightAverage_sq_le
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) {Y : ℝ} (hY : 0 < Y) :
    (∫⁻ x : ℝ, (rightAverage f Y x) ^ 2) ≤
      ∫⁻ x : ℝ, (f x) ^ 2 := by
  calc
    (∫⁻ x : ℝ, (rightAverage f Y x) ^ 2) ≤
        ∫⁻ x : ℝ, rightSquareAverage f Y x := by
      apply lintegral_mono
      intro x
      exact rightAverage_sq_le_rightSquareAverage f hf hY
    _ = ∫⁻ x : ℝ, (f x) ^ 2 := lintegral_rightSquareAverage_eq f hf hY

lemma measurable_rightAverage (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (Y : ℝ) : Measurable (rightAverage f Y) := by
  unfold rightAverage
  fun_prop

/-- The square of the maximum over a finite family of right-moving scales. -/
def finiteRightMaxSq {n : ℕ} (f : ℝ → ℝ≥0∞) (D : Fin n → ℝ)
    (x : ℝ) : ℝ≥0∞ :=
  ⨆ j : Fin n, (rightAverage f (D j) x) ^ 2

lemma measurable_finiteRightMaxSq {n : ℕ} (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) (D : Fin n → ℝ) :
    Measurable (finiteRightMaxSq f D) := by
  unfold finiteRightMaxSq
  exact Measurable.iSup fun j => (measurable_rightAverage f hf (D j)).pow_const 2

/-- A finite scale maximum costs only the number of scales in squared `L²`
energy.  This is the sufficient logarithmic-loss substitute for the full
Hardy--Littlewood theorem in Proposition 2.2. -/
theorem lintegral_finiteRightMaxSq_le {n : ℕ}
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (D : Fin n → ℝ)
    (hD : ∀ j, 0 < D j) :
    (∫⁻ x : ℝ, finiteRightMaxSq f D x) ≤
      (n : ℝ≥0∞) * ∫⁻ x : ℝ, (f x) ^ 2 := by
  have hpoint (x : ℝ) : finiteRightMaxSq f D x ≤
      ∑ j : Fin n, (rightAverage f (D j) x) ^ 2 := by
    unfold finiteRightMaxSq
    apply iSup_le
    intro j
    have hj := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun i : Fin n => (rightAverage f (D i) x) ^ 2)
      (fun i _ => (zero_le : (0 : ℝ≥0∞) ≤ (rightAverage f (D i) x) ^ 2))
      (Finset.mem_univ j)
    simpa using hj
  calc
    (∫⁻ x : ℝ, finiteRightMaxSq f D x) ≤
        ∫⁻ x : ℝ, ∑ j : Fin n, (rightAverage f (D j) x) ^ 2 :=
      lintegral_mono hpoint
    _ = ∑ j : Fin n, ∫⁻ x : ℝ, (rightAverage f (D j) x) ^ 2 := by
      exact lintegral_finsetSum Finset.univ
        (fun j _ => (measurable_rightAverage f hf (D j)).pow_const 2)
    _ ≤ ∑ _j : Fin n, ∫⁻ x : ℝ, (f x) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact lintegral_rightAverage_sq_le f hf (hD j)
    _ = (n : ℝ≥0∞) * ∫⁻ x : ℝ, (f x) ^ 2 := by simp

/-- Enlarging a right interval by at most a factor two enlarges its normalized
nonnegative average by at most two. -/
theorem rightAverage_le_two_of_le_scale
    (f : ℝ → ℝ≥0∞) {x Y D : ℝ} (hY : 0 < Y)
    (hYD : Y ≤ D) (hDtwo : D ≤ 2 * Y) :
    rightAverage f Y x ≤ 2 * rightAverage f D x := by
  let y : ℝ≥0∞ := ENNReal.ofReal Y
  let d : ℝ≥0∞ := ENNReal.ofReal D
  let AY : ℝ≥0∞ := ∫⁻ u in Ioc 0 Y, f (x + u)
  let AD : ℝ≥0∞ := ∫⁻ u in Ioc 0 D, f (x + u)
  have hD : 0 < D := hY.trans_le hYD
  have hset : Ioc (0 : ℝ) Y ⊆ Ioc 0 D := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hYD⟩
  have hA : AY ≤ AD := by
    exact lintegral_mono_set hset
  have hinvReal : Y⁻¹ ≤ 2 * D⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hD).2
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hY).2 hDtwo
  have hinv : y⁻¹ ≤ 2 * d⁻¹ := by
    have h := ENNReal.ofReal_le_ofReal hinvReal
    rw [ENNReal.ofReal_inv_of_pos hY,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_inv_of_pos hD] at h
    exact h
  change y⁻¹ * AY ≤ 2 * (d⁻¹ * AD)
  calc
    y⁻¹ * AY ≤ y⁻¹ * AD := mul_le_mul_left' hA _
    _ ≤ (2 * d⁻¹) * AD := mul_le_mul_right' hinv _
    _ = 2 * (d⁻¹ * AD) := by ac_rfl

/-- Geometric right-moving scales.  Index `j` represents `2^(j+1) H`, so
the smallest scale already covers the endpoint `Y=H` with factor two. -/
def dyadicRightScales (H : ℝ) (N : ℕ) (j : Fin (N + 1)) : ℝ :=
  (2 : ℝ) ^ (j.1 + 1) * H

/-- Every aperture in `[H,X]` is covered by one of the finitely many geometric
scales, provided the last scale reaches `X`. -/
theorem exists_dyadicRightScale
    {H X Y : ℝ} {N : ℕ} (hH : 0 < H) (hHY : H ≤ Y) (hYX : Y ≤ X)
    (hXN : X / H < (2 : ℝ) ^ (N + 1)) :
    ∃ j : Fin (N + 1),
      Y ≤ dyadicRightScales H N j ∧ dyadicRightScales H N j ≤ 2 * Y := by
  have hratio : 1 ≤ Y / H := (le_div_iff₀ hH).2 (by simpa using hHY)
  obtain ⟨j, hjlow, hjhigh⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hjNpow : (2 : ℝ) ^ j < (2 : ℝ) ^ (N + 1) :=
    hjlow.trans_lt ((div_le_div_iff_of_pos_right hH).2 hYX |>.trans_lt hXN)
  have hjN : j ≤ N := by
    exact Nat.lt_succ_iff.mp ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hjNpow)
  let jf : Fin (N + 1) := ⟨j, Nat.lt_succ_iff.mpr hjN⟩
  refine ⟨jf, ?_, ?_⟩
  · dsimp [dyadicRightScales, jf]
    exact (div_lt_iff₀ hH).mp hjhigh |>.le
  · dsimp [dyadicRightScales, jf]
    rw [pow_succ]
    nlinarith [(le_div_iff₀ hH).mp hjlow]

/-- The continuum supremum of squared right averages over the exact legal
aperture interval.  No measurability is built into the definition; the
pointwise dyadic domination below supplies a measurable majorant. -/
def rightMaxSqBetween (f : ℝ → ℝ≥0∞) (H X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hHY : H ≤ Y) (_hYX : Y ≤ X),
    (rightAverage f Y x) ^ 2

/-- The continuum legal-aperture supremum is pointwise dominated by four
times the finite dyadic maximum. -/
theorem rightMaxSqBetween_le_dyadic
    (f : ℝ → ℝ≥0∞) {H X x : ℝ} {N : ℕ} (hH : 0 < H)
    (hXN : X / H < (2 : ℝ) ^ (N + 1)) :
    rightMaxSqBetween f H X x ≤
      4 * finiteRightMaxSq f (dyadicRightScales H N) x := by
  unfold rightMaxSqBetween
  apply iSup_le
  intro Y
  apply iSup_le
  intro hHY
  apply iSup_le
  intro hYX
  obtain ⟨j, hYDj, hDjY⟩ :=
    exists_dyadicRightScale hH hHY hYX hXN
  have hY : 0 < Y := hH.trans_le hHY
  have havg := rightAverage_le_two_of_le_scale f (x := x) hY hYDj hDjY
  have hsq := pow_le_pow_left' havg 2
  calc
    rightAverage f Y x ^ 2 ≤
        (2 * rightAverage f (dyadicRightScales H N j) x) ^ 2 := hsq
    _ = 4 * (rightAverage f (dyadicRightScales H N j) x) ^ 2 := by
      ring
    _ ≤ 4 * finiteRightMaxSq f (dyadicRightScales H N) x := by
      apply mul_le_mul_left'
      exact le_iSup (fun i : Fin (N + 1) =>
        (rightAverage f (dyadicRightScales H N i) x) ^ 2) j

/-- Truncated one-sided Hardy--Littlewood `L²` theorem sufficient for the MAP
aperture range.  The price is the explicit number `N+1` of geometric scales;
this is only logarithmic and is absorbed by requesting one more logarithm in
the zero-density input. -/
theorem lintegral_rightMaxSqBetween_le_dyadic
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) {H X : ℝ} {N : ℕ}
    (hH : 0 < H) (hXN : X / H < (2 : ℝ) ^ (N + 1)) :
    (∫⁻ x : ℝ, rightMaxSqBetween f H X x) ≤
      4 * (N + 1 : ℝ≥0∞) * ∫⁻ x : ℝ, (f x) ^ 2 := by
  let D : Fin (N + 1) → ℝ := dyadicRightScales H N
  have hD : ∀ j, 0 < D j := by
    intro j
    exact mul_pos (pow_pos (by norm_num) _) hH
  calc
    (∫⁻ x : ℝ, rightMaxSqBetween f H X x) ≤
        ∫⁻ x : ℝ, 4 * finiteRightMaxSq f D x := by
      apply lintegral_mono
      intro x
      exact rightMaxSqBetween_le_dyadic f hH hXN
    _ = 4 * ∫⁻ x : ℝ, finiteRightMaxSq f D x := by
      rw [lintegral_const_mul 4 (measurable_finiteRightMaxSq f hf D)]
    _ ≤ 4 * ((N + 1 : ℝ≥0∞) * ∫⁻ x : ℝ, (f x) ^ 2) := by
      have hfinite := lintegral_finiteRightMaxSq_le f hf D hD
      have hmul := mul_le_mul_left' hfinite (4 : ℝ≥0∞)
      simpa using hmul
    _ = 4 * (N + 1 : ℝ≥0∞) * ∫⁻ x : ℝ, (f x) ^ 2 := by
      rw [mul_assoc]

/-- Family-level consumer for a field-energy estimate such as manuscript
equation (2.8).  It converts the sum of the individual square energies into
the sum of the legal-aperture maximal square energies, with no contour or
zero-count assumptions hidden inside. -/
theorem lintegral_sum_rightMaxSqBetween_le_dyadic
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) {H X : ℝ} {N : ℕ}
    (hH : 0 < H) (hXN : X / H < (2 : ℝ) ^ (N + 1)) :
    (∫⁻ x : ℝ, ∑ i : ι, rightMaxSqBetween (f i) H X x) ≤
      4 * (N + 1 : ℝ≥0∞) *
        ∑ i : ι, ∫⁻ x : ℝ, (f i x) ^ 2 := by
  let D : Fin (N + 1) → ℝ := dyadicRightScales H N
  have hD : ∀ j, 0 < D j := by
    intro j
    exact mul_pos (pow_pos (by norm_num) _) hH
  have hpoint (x : ℝ) :
      (∑ i : ι, rightMaxSqBetween (f i) H X x) ≤
        ∑ i : ι, 4 * finiteRightMaxSq (f i) D x := by
    apply Finset.sum_le_sum
    intro i _
    exact rightMaxSqBetween_le_dyadic (f i) hH hXN
  calc
    (∫⁻ x : ℝ, ∑ i : ι, rightMaxSqBetween (f i) H X x) ≤
        ∫⁻ x : ℝ, ∑ i : ι, 4 * finiteRightMaxSq (f i) D x :=
      lintegral_mono hpoint
    _ = ∑ i : ι, ∫⁻ x : ℝ, 4 * finiteRightMaxSq (f i) D x := by
      exact lintegral_finsetSum Finset.univ fun i _ =>
        measurable_const.mul (measurable_finiteRightMaxSq (f i) (hf i) D)
    _ = ∑ i : ι, 4 * ∫⁻ x : ℝ, finiteRightMaxSq (f i) D x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_const_mul 4 (measurable_finiteRightMaxSq (f i) (hf i) D)]
    _ ≤ ∑ i : ι, 4 * ((N + 1 : ℝ≥0∞) *
          ∫⁻ x : ℝ, (f i x) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hfinite := lintegral_finiteRightMaxSq_le (f i) (hf i) D hD
      have hmul := mul_le_mul_left' hfinite (4 : ℝ≥0∞)
      simpa using hmul
    _ = 4 * (N + 1 : ℝ≥0∞) *
        ∑ i : ι, ∫⁻ x : ℝ, (f i x) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc]

/-- Canonical number of geometric scales needed below `X`. -/
def dyadicScaleCount (X : ℝ) : ℕ :=
  ⌈Real.logb 2 X⌉₊

/-- The canonical final dyadic scale strictly exceeds `X`. -/
theorem lt_two_pow_dyadicScaleCount_add_one {X : ℝ} (hX : 1 ≤ X) :
    X < (2 : ℝ) ^ (dyadicScaleCount X + 1) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hlog0 : 0 ≤ Real.logb 2 X :=
    Real.logb_nonneg (by norm_num) hX
  have hlogceil :
      Real.logb 2 X ≤ (dyadicScaleCount X : ℝ) := by
    exact Nat.le_ceil _
  have hXpowR : X ≤ (2 : ℝ) ^ (dyadicScaleCount X : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hXpos).mp hlogceil
  have hXpow : X ≤ (2 : ℝ) ^ dyadicScaleCount X := by
    simpa [Real.rpow_natCast] using hXpowR
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (dyadicScaleCount X)]

/-- The number of scales is explicitly logarithmic. -/
theorem dyadicScaleCount_cast_lt_logb_add_one {X : ℝ} (hX : 1 ≤ X) :
    (dyadicScaleCount X : ℝ) < Real.logb 2 X + 1 := by
  exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hX)

/-- Canonical exact-domain version of the truncated one-sided maximal theorem;
no externally chosen scale count remains. -/
theorem lintegral_rightMaxSqBetween_le
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) {H X : ℝ}
    (hH : 1 ≤ H) (hHX : H ≤ X) :
    (∫⁻ x : ℝ, rightMaxSqBetween f H X x) ≤
      4 * (dyadicScaleCount X + 1 : ℝ≥0∞) *
        ∫⁻ x : ℝ, (f x) ^ 2 := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hX : 1 ≤ X := hH.trans hHX
  have hdiv : X / H ≤ X := by
    exact (div_le_iff₀ hHpos).2 (by nlinarith)
  have hreach : X / H < (2 : ℝ) ^ (dyadicScaleCount X + 1) :=
    hdiv.trans_lt (lt_two_pow_dyadicScaleCount_add_one hX)
  exact lintegral_rightMaxSqBetween_le_dyadic f hf hHpos hreach

/-- Canonical family-level consumer for equation (2.8). -/
theorem lintegral_sum_rightMaxSqBetween_le
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) {H X : ℝ}
    (hH : 1 ≤ H) (hHX : H ≤ X) :
    (∫⁻ x : ℝ, ∑ i : ι, rightMaxSqBetween (f i) H X x) ≤
      4 * (dyadicScaleCount X + 1 : ℝ≥0∞) *
        ∑ i : ι, ∫⁻ x : ℝ, (f i x) ^ 2 := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hX : 1 ≤ X := hH.trans hHX
  have hdiv : X / H ≤ X := by
    exact (div_le_iff₀ hHpos).2 (by nlinarith)
  have hreach : X / H < (2 : ℝ) ^ (dyadicScaleCount X + 1) :=
    hdiv.trans_lt (lt_two_pow_dyadicScaleCount_add_one hX)
  exact lintegral_sum_rightMaxSqBetween_le_dyadic f hf hHpos hreach

end
end OneSidedMaximalL2

#print axioms OneSidedMaximalL2.rightAverage_sq_le_rightSquareAverage
#print axioms OneSidedMaximalL2.rightAverage_eq_interval
#print axioms OneSidedMaximalL2.lintegral_rightAverage_sq_le
#print axioms OneSidedMaximalL2.exists_dyadicRightScale
#print axioms OneSidedMaximalL2.rightMaxSqBetween_le_dyadic
#print axioms OneSidedMaximalL2.lintegral_rightMaxSqBetween_le_dyadic
#print axioms OneSidedMaximalL2.lintegral_sum_rightMaxSqBetween_le_dyadic
#print axioms OneSidedMaximalL2.lintegral_rightMaxSqBetween_le
#print axioms OneSidedMaximalL2.lintegral_sum_rightMaxSqBetween_le
