import MRTProposition51Source
import SignedGallagherCore

/-!
# First proved analytic layer of MRT Proposition 5.1

This staging-only module proves the exact arbitrary-coefficient Gallagher--
Plancherel inequality which is the first smoothing step in the published proof
of Proposition 5.1(i).  It is an actual theorem, with no theorem-valued premise.
The paper uses a smooth cutoff; the compact interval kernel below gives a fully
explicit constant and is sufficient for the same initial reduction.
-/

namespace MAPMRTProposition51FirstAnalytic

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal
open MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPNearCollarGallagher

noncomputable section

/-- The arbitrary-coefficient sliding field
`∑_{X<n≤2X, x<n≤x+y} f(n)`. -/
def coefficientSlidingField
    (X : ℝ) (f : ℕ → ℂ) (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    f n * slidingAtom (n : ℝ) y x

/-- Total coefficient mass on the exact source support. -/
def coefficientMass (X : ℝ) (f : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖

theorem coefficientMass_nonneg (X : ℝ) (f : ℕ → ℂ) :
    0 ≤ coefficientMass X f := by
  unfold coefficientMass
  positivity

theorem integrable_coefficientSlidingField
    (X : ℝ) (f : ℕ → ℂ) (y : ℝ) :
    Integrable (fun x : ℝ ↦ coefficientSlidingField X f x y) := by
  unfold coefficientSlidingField
  apply integrable_finset_sum
  intro n hn
  exact (integrable_slidingAtom (n : ℝ) y).const_mul (f n)

theorem norm_coefficientSlidingField_le
    (X : ℝ) (f : ℕ → ℂ) (x y : ℝ) :
    ‖coefficientSlidingField X f x y‖ ≤ coefficientMass X f := by
  unfold coefficientSlidingField coefficientMass
  calc
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        f n * slidingAtom (n : ℝ) y x‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n * slidingAtom (n : ℝ) y x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      by_cases h : x < (n : ℝ) ∧ (n : ℝ) ≤ x + y
      · rw [slidingAtom_apply, if_pos h]
        simp
      · rw [slidingAtom_apply, if_neg h]
        simp

theorem memLp_two_coefficientSlidingField
    (X : ℝ) (f : ℕ → ℂ) (y : ℝ) :
    MemLp (fun x : ℝ ↦ coefficientSlidingField X f x y) 2 := by
  exact memLp_two_of_integrable_of_norm_le
    (integrable_coefficientSlidingField X f y)
    (coefficientMass_nonneg X f)
    (fun x ↦ norm_coefficientSlidingField_le X f x y)

/-- Exact Fourier pair, with Mathlib's negative transform convention. -/
theorem fourier_coefficientSlidingField
    (X : ℝ) (f : ℕ → ℂ) (y xi : ℝ) (hy : 0 ≤ y) :
    (𝓕 (fun x : ℝ ↦ coefficientSlidingField X f x y)) xi =
      gallagherWindowKernel y xi * exponentialSum X f (-xi) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold coefficientSlidingField
  simp_rw [Finset.smul_sum]
  rw [integral_finset_sum]
  · simp_rw [← Real.fourier_real_eq_integral_exp_smul,
      fourier_const_mul_slidingAtom _ _ _ _ hy]
    unfold exponentialSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hphase :
        Complex.exp (-2 * Real.pi * Complex.I * (xi * (n : ℝ))) =
          fourier (n : ℤ) ((-xi : ℝ) : UnitAddCircle) := by
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  · intro n hn
    have hi := (integrable_slidingAtom (n : ℝ) y).const_mul (f n)
    have hc : Continuous
        (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)) := by
      fun_prop
    have hnorm : ∀ x : ℝ,
        ‖Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)‖ ≤ 1 := by
      intro x
      rw [show (↑(-2 * Real.pi * x * xi) : ℂ) * Complex.I =
          ((-2 * Real.pi * x * xi : ℝ) : ℂ) * Complex.I by rfl,
        Complex.norm_exp_ofReal_mul_I]
    simpa only [smul_eq_mul] using
      hi.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hnorm)

theorem norm_exponentialSum_le_coefficientMass
    (X : ℝ) (f : ℕ → ℂ) (theta : ℝ) :
    ‖exponentialSum X f theta‖ ≤ coefficientMass X f := by
  unfold exponentialSum coefficientMass
  calc
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        f n * fourier (n : ℤ) (theta : UnitAddCircle)‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n * fourier (n : ℤ) (theta : UnitAddCircle)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp

theorem continuous_exponentialSum_real
    (X : ℝ) (f : ℕ → ℂ) :
    Continuous (fun theta : ℝ ↦ exponentialSum X f theta) := by
  unfold exponentialSum
  fun_prop

theorem memLp_two_coefficientFrequencyProduct
    (X : ℝ) (f : ℕ → ℂ) {y : ℝ} (hy : 0 ≤ y) :
    MemLp (fun xi : ℝ ↦
      gallagherWindowKernel y xi * exponentialSum X f (-xi)) 2 := by
  rw [memLp_two_iff_integrable_sq_norm]
  · let C := coefficientMass X f
    have hC : 0 ≤ C := coefficientMass_nonneg X f
    have hmajorant : Integrable (fun xi : ℝ ↦
        C ^ 2 * ‖gallagherWindowKernel y xi‖ ^ 2) :=
      (integrable_sq_norm_gallagherWindowKernel hy).const_mul (C ^ 2)
    apply hmajorant.mono
    · exact (((continuous_gallagherWindowKernel y).mul
        ((continuous_exponentialSum_real X f).comp continuous_neg)).norm.pow 2)
          |>.aestronglyMeasurable
    · filter_upwards with xi
      rw [norm_mul, mul_pow]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (sq_nonneg ‖gallagherWindowKernel y xi‖)
          (sq_nonneg ‖exponentialSum X f (-xi)‖)),
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg C)
          (sq_nonneg ‖gallagherWindowKernel y xi‖))]
      have hsum := norm_exponentialSum_le_coefficientMass X f (-xi)
      change ‖exponentialSum X f (-xi)‖ ≤ C at hsum
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
      nlinarith [sq_nonneg ‖gallagherWindowKernel y xi‖]
  · exact (continuous_gallagherWindowKernel y).mul
      ((continuous_exponentialSum_real X f).comp continuous_neg)
      |>.aestronglyMeasurable

theorem coefficient_gallagher_plancherel_identity
    (X : ℝ) (f : ℕ → ℂ) {y : ℝ} (hy : 0 ≤ y) :
    (∫ xi : ℝ,
      ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2) =
      ∫ x : ℝ, ‖coefficientSlidingField X f x y‖ ^ 2 := by
  exact MAPGallagherPlancherel.integral_norm_sq_fourier_pair
    (integrable_coefficientSlidingField X f y)
    (memLp_two_coefficientSlidingField X f y)
    (memLp_two_coefficientFrequencyProduct X f hy)
    (fun xi ↦ (fourier_coefficientSlidingField X f y xi hy).symm)

/-- Arbitrary-coefficient Gallagher--Plancherel inequality with the explicit
constant `4` and band `|θ|≤1/(8y)`. -/
theorem coefficientGallagherInequality_constant_four
    (X : ℝ) (f : ℕ → ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ theta in Set.Icc (-(1 / (8 * y))) (1 / (8 * y)),
        ‖exponentialSum X f theta‖ ^ 2) ≤
      4 / y ^ 2 *
        ∫ x : ℝ, ‖coefficientSlidingField X f x y‖ ^ 2 := by
  let r : ℝ := 1 / (8 * y)
  have hr : 0 ≤ r := by unfold r; positivity
  have hsumCont : Continuous (fun theta : ℝ ↦
      ‖exponentialSum X f theta‖ ^ 2) :=
    (continuous_exponentialSum_real X f).norm.pow 2
  have hleftInt : IntegrableOn (fun xi : ℝ ↦
      ‖exponentialSum X f (-xi)‖ ^ 2) (Set.Icc (-r) r) :=
    (hsumCont.comp continuous_neg).integrableOn_Icc
  have hfreq2 := memLp_two_coefficientFrequencyProduct X f hy.le
  have hrightInt : Integrable (fun xi : ℝ ↦
      ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfreq2.1).1 hfreq2
  have hpoint : ∀ xi ∈ Set.Icc (-r) r,
      ‖exponentialSum X f (-xi)‖ ^ 2 ≤
        4 / y ^ 2 *
          ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2 := by
    intro xi hxi
    have habs : |xi| ≤ 1 / (8 * y) := by
      change |xi| ≤ r
      exact (abs_le).2 hxi
    have hk := window_sq_le_four_mul_kernel_norm_sq hy habs
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
    rw [norm_mul, mul_pow]
    have hE0 := sq_nonneg ‖exponentialSum X f (-xi)‖
    have hmul := mul_le_mul_of_nonneg_right hk hE0
    calc
      ‖exponentialSum X f (-xi)‖ ^ 2 =
          y ^ 2 * ‖exponentialSum X f (-xi)‖ ^ 2 / y ^ 2 := by field_simp
      _ ≤ (4 * ‖gallagherWindowKernel y xi‖ ^ 2 *
          ‖exponentialSum X f (-xi)‖ ^ 2) / y ^ 2 := by
        exact (div_le_div_iff_of_pos_right hy2).2 hmul
      _ = 4 / y ^ 2 *
          (‖gallagherWindowKernel y xi‖ ^ 2 *
            ‖exponentialSum X f (-xi)‖ ^ 2) := by ring
  have hband :
      (∫ xi in Set.Icc (-r) r,
        ‖exponentialSum X f (-xi)‖ ^ 2) ≤
      4 / y ^ 2 *
        ∫ xi in Set.Icc (-r) r,
          ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2 := by
    calc
      _ ≤ ∫ xi in Set.Icc (-r) r,
          (4 / y ^ 2) *
            ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2 := by
        apply MeasureTheory.integral_mono_ae hleftInt
          (hrightInt.integrableOn.const_mul (4 / y ^ 2))
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with xi hxi
        exact hpoint xi hxi
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hrestrict :
      (∫ xi in Set.Icc (-r) r,
        ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2) ≤
      ∫ xi : ℝ,
        ‖gallagherWindowKernel y xi * exponentialSum X f (-xi)‖ ^ 2 :=
    setIntegral_le_integral hrightInt
      (Filter.Eventually.of_forall fun xi ↦ sq_nonneg _)
  have hcombine := hband.trans
    (mul_le_mul_of_nonneg_left hrestrict (by positivity))
  change (∫ theta in Set.Icc (-r) r,
      ‖exponentialSum X f theta‖ ^ 2) ≤ _
  rw [← integral_Icc_comp_neg_eq
      (fun theta ↦ ‖exponentialSum X f theta‖ ^ 2) hr]
  rw [coefficient_gallagher_plancherel_identity X f hy.le] at hcombine
  simpa only [r] using hcombine

/-! ## Translation to the literal Proposition 5.1 arc -/

/-- Coefficient twist by an arbitrary real center. -/
def realPhaseTwist (beta : ℝ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f n * fourier (n : ℤ) ((beta : ℝ) : UnitAddCircle)

theorem norm_realPhaseTwist
    (beta : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    ‖realPhaseTwist beta f n‖ = ‖f n‖ := by
  simp [realPhaseTwist]

theorem exponentialSum_realPhaseTwist
    (X beta theta : ℝ) (f : ℕ → ℂ) :
    exponentialSum X (realPhaseTwist beta f) theta =
      exponentialSum X f (beta + theta) := by
  unfold exponentialSum realPhaseTwist
  apply Finset.sum_congr rfl
  intro n hn
  rw [show (((beta + theta : ℝ) : UnitAddCircle)) =
      ((beta : ℝ) : UnitAddCircle) + ((theta : ℝ) : UnitAddCircle) by
      exact AddCircle.coe_add 1 beta theta]
  rw [fourier_apply, fourier_apply, fourier_apply]
  rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  ring

theorem coefficientGallagherInterval_constant_four
    (X : ℝ) (f : ℕ → ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ theta in (-(1 / (8 * y)))..(1 / (8 * y)),
        ‖exponentialSum X f theta‖ ^ 2) ≤
      4 / y ^ 2 *
        ∫ x : ℝ, ‖coefficientSlidingField X f x y‖ ^ 2 := by
  have h := coefficientGallagherInequality_constant_four X f hy
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by
      have : 0 ≤ 1 / (8 * y) := by positivity
      linarith)] at h
  exact h

/-- Centered version of the exact Gallagher reduction. -/
theorem centeredCoefficientGallagher_constant_four
    (X beta : ℝ) (f : ℕ → ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ theta in (beta - 1 / (8 * y))..(beta + 1 / (8 * y)),
        ‖exponentialSum X f theta‖ ^ 2) ≤
      4 / y ^ 2 *
        ∫ x : ℝ,
          ‖coefficientSlidingField X (realPhaseTwist beta f) x y‖ ^ 2 := by
  have h := coefficientGallagherInterval_constant_four
    X (realPhaseTwist beta f) hy
  have hshift := intervalIntegral.integral_comp_add_right
    (fun theta : ℝ ↦ ‖exponentialSum X f theta‖ ^ 2) beta
    (a := -(1 / (8 * y))) (b := 1 / (8 * y))
  have hleft :
      (∫ theta in (beta - 1 / (8 * y))..(beta + 1 / (8 * y)),
          ‖exponentialSum X f theta‖ ^ 2) =
        ∫ theta in (-(1 / (8 * y)))..(1 / (8 * y)),
          ‖exponentialSum X f (beta + theta)‖ ^ 2 := by
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hshift.symm
  rw [hleft]
  simpa only [exponentialSum_realPhaseTwist] using h

/-- The literal `β±1/H` arc in Proposition 5.1, obtained with the explicit
compact window `y=H/8`.  This is the first analytic reduction in the source
proof, with the harmless absolute constant made explicit as `256`. -/
theorem proposition51_initial_gallagher_reduction
    (X H beta : ℝ) (f : ℕ → ℂ) (hH : 0 < H) :
    (∫ theta in (beta - 1 / H)..(beta + 1 / H),
        ‖exponentialSum X f theta‖ ^ 2) ≤
      256 / H ^ 2 *
        ∫ x : ℝ,
          ‖coefficientSlidingField X (realPhaseTwist beta f) x (H / 8)‖ ^ 2 := by
  have h := centeredCoefficientGallagher_constant_four
    X beta f (y := H / 8) (by positivity)
  convert h using 1 <;> field_simp <;> ring

/-- The triangle-inequality step immediately following the initial
Gallagher--Plancherel reduction.  It retains the exact half-open source window
`x<n≤x+y`; endpoint changes occur only after integration. -/
theorem norm_phaseTwistedSlidingField_le
    (X beta : ℝ) (f : ℕ → ℂ) (x y : ℝ) :
    ‖coefficientSlidingField X (realPhaseTwist beta f) x y‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        if x < (n : ℝ) ∧ (n : ℝ) ≤ x + y then ‖f n‖ else 0 := by
  unfold coefficientSlidingField
  calc
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        realPhaseTwist beta f n * slidingAtom (n : ℝ) y x‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖realPhaseTwist beta f n * slidingAtom (n : ℝ) y x‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        if x < (n : ℝ) ∧ (n : ℝ) ≤ x + y then ‖f n‖ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_realPhaseTwist, slidingAtom_apply]
      split_ifs <;> simp

/-- The literal nonnegative window sum inside `ordinarySlidingMass`. -/
def ordinaryWindowSum
    (X H : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H then ‖f n‖ else 0

theorem ordinaryWindowSum_nonneg
    (X H : ℝ) (f : ℕ → ℂ) (x : ℝ) :
    0 ≤ ordinaryWindowSum X H f x := by
  unfold ordinaryWindowSum
  apply Finset.sum_nonneg
  intro n hn
  split_ifs <;> positivity

theorem ordinaryWindowSum_le_coefficientMass
    (X H : ℝ) (f : ℕ → ℂ) (x : ℝ) :
    ordinaryWindowSum X H f x ≤ coefficientMass X f := by
  unfold ordinaryWindowSum coefficientMass
  apply Finset.sum_le_sum
  intro n hn
  split_ifs <;> simp

theorem integrable_ordinaryWindowTerm
    (H : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    Integrable (fun x : ℝ ↦
      if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H then ‖f n‖ else 0) := by
  have hindicator :
      (fun x : ℝ ↦
        if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H then ‖f n‖ else 0) =
      (Set.Icc ((n : ℝ) - H) n).indicator (fun _ ↦ ‖f n‖) := by
    funext x
    by_cases hx : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H
    · have hmem : x ∈ Set.Icc ((n : ℝ) - H) n := by
        constructor <;> linarith [hx.1, hx.2]
      simp [hx, Set.indicator_of_mem hmem]
    · have hnot : x ∉ Set.Icc ((n : ℝ) - H) n := by
        intro hmem
        apply hx
        constructor <;> linarith [hmem.1, hmem.2]
      simp [hx, Set.indicator_of_notMem hnot]
  rw [hindicator]
  exact (integrableOn_const (C := ‖f n‖) measure_Icc_lt_top.ne)
    |>.integrable_indicator measurableSet_Icc

theorem integrable_ordinaryWindowSum
    (X H : ℝ) (f : ℕ → ℂ) :
    Integrable (ordinaryWindowSum X H f) := by
  unfold ordinaryWindowSum
  apply integrable_finset_sum
  intro n hn
  exact integrable_ordinaryWindowTerm H f n

theorem integrable_sq_ordinaryWindowSum
    (X H : ℝ) (f : ℕ → ℂ) :
    Integrable (fun x : ℝ ↦ ordinaryWindowSum X H f x ^ 2) := by
  have hg := integrable_ordinaryWindowSum X H f
  have hbound : ∀ x : ℝ,
      ‖ordinaryWindowSum X H f x‖ ≤ coefficientMass X f := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (ordinaryWindowSum_nonneg X H f x)]
    exact ordinaryWindowSum_le_coefficientMass X H f x
  have hmul := hg.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  simpa [pow_two] using hmul

theorem ordinarySlidingMass_eq_integral_ordinaryWindowSum
    (X H : ℝ) (f : ℕ → ℂ) :
    ordinarySlidingMass X H f =
      ∫ x : ℝ, ordinaryWindowSum X H f x ^ 2 := by
  rfl

/-- A shorter half-open Gallagher window is pointwise dominated by the exact
closed ordinary window in Corollary 5.3. -/
theorem phaseTwistedSlidingEnergy_le_ordinarySlidingMass
    (X beta : ℝ) (f : ℕ → ℂ) {y H : ℝ}
    (hy : 0 ≤ y) (hyH : y ≤ H) :
    (∫ x : ℝ,
        ‖coefficientSlidingField X (realPhaseTwist beta f) x y‖ ^ 2) ≤
      ordinarySlidingMass X H f := by
  rw [ordinarySlidingMass_eq_integral_ordinaryWindowSum]
  apply MeasureTheory.integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  · exact integrable_sq_ordinaryWindowSum X H f
  · filter_upwards with x
    have hnorm := norm_phaseTwistedSlidingField_le X beta f x y
    have hwindow :
        (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          if x < (n : ℝ) ∧ (n : ℝ) ≤ x + y then ‖f n‖ else 0) ≤
        ordinaryWindowSum X H f x := by
      unfold ordinaryWindowSum
      apply Finset.sum_le_sum
      intro n hn
      by_cases hshort : x < (n : ℝ) ∧ (n : ℝ) ≤ x + y
      · have hlong : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H := by
          constructor
          · exact hshort.1.le
          · linarith [hshort.2]
        rw [if_pos hshort, if_pos hlong]
      · rw [if_neg hshort]
        positivity
    have hnorm' :
        ‖coefficientSlidingField X (realPhaseTwist beta f) x y‖ ≤
          ordinaryWindowSum X H f x := hnorm.trans hwindow
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm' 2

/-- Fully proved first branch of Proposition 5.1: the literal arc is bounded
by the published ordinary sliding mass with constant `256/H²`. -/
theorem proposition51_initial_ordinary_reduction
    (X H beta : ℝ) (f : ℕ → ℂ) (hH : 0 < H) :
    (∫ theta in (beta - 1 / H)..(beta + 1 / H),
        ‖exponentialSum X f theta‖ ^ 2) ≤
      256 / H ^ 2 * ordinarySlidingMass X H f := by
  have hfirst := proposition51_initial_gallagher_reduction X H beta f hH
  have hmass := phaseTwistedSlidingEnergy_le_ordinarySlidingMass
    X beta f (y := H / 8) (H := H) (by positivity) (by linarith)
  exact hfirst.trans
    (mul_le_mul_of_nonneg_left hmass (by positivity))

/-- In the two easy regimes discarded on MRT page 43, the printed ordinary
coefficient dominates `1/H²` up to the explicit absolute factor `10000`. -/
theorem inv_H_sq_le_easy_ordinaryCoefficient
    {H beta eta : ℝ} (hH : 0 < H) (hbeta : beta ≠ 0) (heta : 0 ≤ eta)
    (heasy : |beta| * H ≤ 1 ∨ 1 / 100 ≤ eta) :
    1 / H ^ 2 ≤
      10000 * ((eta + 1 / (|beta| * H)) ^ 2 / H ^ 2) := by
  have hU : 0 < |beta| * H := mul_pos (abs_pos.mpr hbeta) hH
  have hterm : 1 / 100 ≤ eta + 1 / (|beta| * H) := by
    rcases heasy with hsmall | hetaLarge
    · have hinv : 1 ≤ 1 / (|beta| * H) := by
        apply (le_div_iff₀ hU).2
        simpa using hsmall
      linarith
    · have hinv0 : 0 ≤ 1 / (|beta| * H) := by positivity
      linarith
  have hsq : 1 ≤ 10000 * (eta + 1 / (|beta| * H)) ^ 2 := by
    nlinarith
  have hHinv : 0 ≤ 1 / H ^ 2 := by positivity
  calc
    1 / H ^ 2 ≤
        (10000 * (eta + 1 / (|beta| * H)) ^ 2) * (1 / H ^ 2) := by
      nlinarith
    _ = 10000 * ((eta + 1 / (|beta| * H)) ^ 2 / H ^ 2) := by ring

/-- Actual easy branch of Proposition 5.1(i), with no analytic premise.  The
remaining branch is exactly `1 < |β|H` and `η < 1/100`, where the paper begins
the duality/Littlewood--Paley stationary-phase argument. -/
theorem proposition51_easy_regime
    (X H beta eta : ℝ) (f : ℕ → ℂ)
    (hH : 0 < H) (hbeta : beta ≠ 0) (heta : 0 ≤ eta)
    (heasy : |beta| * H ≤ 1 ∨ 1 / 100 ≤ eta) :
    (∫ theta in (beta - 1 / H)..(beta + 1 / H),
        ‖exponentialSum X f theta‖ ^ 2) ≤
      2560000 * ordinaryError X H f beta eta := by
  have hfirst := proposition51_initial_ordinary_reduction X H beta f hH
  have hcoef := inv_H_sq_le_easy_ordinaryCoefficient
    hH hbeta heta heasy
  have hmass : 0 ≤ ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    exact MeasureTheory.integral_nonneg fun x ↦ sq_nonneg _
  unfold ordinaryError
  calc
    (∫ theta in (beta - 1 / H)..(beta + 1 / H),
        ‖exponentialSum X f theta‖ ^ 2) ≤
        256 / H ^ 2 * ordinarySlidingMass X H f := hfirst
    _ ≤ 256 *
        (10000 * ((eta + 1 / (|beta| * H)) ^ 2 / H ^ 2)) *
          ordinarySlidingMass X H f := by
      have := mul_le_mul_of_nonneg_right hcoef hmass
      calc
        256 / H ^ 2 * ordinarySlidingMass X H f =
            256 * ((1 / H ^ 2) * ordinarySlidingMass X H f) := by ring
        _ ≤ 256 *
            ((10000 * ((eta + 1 / (|beta| * H)) ^ 2 / H ^ 2)) *
              ordinarySlidingMass X H f) :=
          mul_le_mul_of_nonneg_left this (by norm_num)
        _ = _ := by ring
    _ = 2560000 *
        (((eta + 1 / (|beta| * H)) ^ 2 / H ^ 2) *
          ordinarySlidingMass X H f) := by ring

end

end MAPMRTProposition51FirstAnalytic
