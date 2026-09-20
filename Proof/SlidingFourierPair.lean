import NearCollarGallagherFiniteUnion
import Mathlib.Analysis.Fourier.LpSpace
import GallagherKernelBounds

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Set
open scoped BigOperators FourierTransform ArithmeticFunction ENNReal
noncomputable section
open PrimePairEndpoints MAPMajorArcWeld

/-- Exact spatial interval selected by the literal condition `x < t ≤ x+y`. -/
def slidingAtom (t y x : ℝ) : ℂ :=
  (Set.Ico (t - y) t).indicator (fun _ => (1 : ℂ)) x

theorem sliding_condition_iff_mem_Ico
    {t x y : ℝ} :
    (x < t ∧ t ≤ x + y) ↔ x ∈ Set.Ico (t - y) t := by
  simp only [Set.mem_Ico]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

@[simp] theorem slidingAtom_apply {t y x : ℝ} :
    slidingAtom t y x = if x < t ∧ t ≤ x + y then 1 else 0 := by
  unfold slidingAtom
  by_cases h : x < t ∧ t ≤ x + y
  · rw [if_pos h, Set.indicator_of_mem (sliding_condition_iff_mem_Ico.mp h)]
  · rw [if_neg h, Set.indicator_of_notMem]
    exact mt sliding_condition_iff_mem_Ico.mpr h

/-- A sliding atom is integrable for every real endpoint/window. -/
theorem integrable_slidingAtom (t y : ℝ) : Integrable (slidingAtom t y) := by
  unfold slidingAtom
  exact (integrableOn_const (C := (1 : ℂ)) measure_Ico_lt_top.ne).integrable_indicator
    measurableSet_Ico

/-- Its Fourier transform is the exact Gallagher interval multiplier times
Mathlib's negative Fourier phase at the atom. -/
theorem fourier_slidingAtom (t y beta : ℝ) (hy : 0 ≤ y) :
    (𝓕 (slidingAtom t y)) beta =
      Complex.exp (-2 * Real.pi * Complex.I * (beta * t)) *
        gallagherWindowKernel y beta := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold slidingAtom
  have hrewrite :
      (fun x : ℝ =>
          Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
            (Set.Ico (t - y) t).indicator (fun _ => (1 : ℂ)) x) =
        (Set.Ico (t - y) t).indicator
          (fun x : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (beta * x))) := by
    funext x
    by_cases hx : x ∈ Set.Ico (t - y) t <;> simp [hx]
    push_cast
    ring_nf
  rw [hrewrite, MeasureTheory.integral_indicator measurableSet_Ico,
    MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le] 
  · have hsub := intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (beta * x))) t
        (a := 0) (b := y)
    have hfactor :
        (∫ u in (0 : ℝ)..y,
          Complex.exp (-2 * Real.pi * Complex.I * (beta * (t - u)))) =
          Complex.exp (-2 * Real.pi * Complex.I * (beta * t)) *
            gallagherWindowKernel y beta := by
      unfold gallagherWindowKernel
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      change Complex.exp (-2 * Real.pi * Complex.I * (beta * (t - u))) =
        Complex.exp (-2 * Real.pi * Complex.I * (beta * t)) *
          Complex.exp (2 * Real.pi * Complex.I * (beta * u))
      rw [← Complex.exp_add]
      congr 1
      ring
    have hsub' :
        (∫ x in t - y..t,
          Complex.exp (-2 * Real.pi * Complex.I * (beta * x))) =
          ∫ u in (0 : ℝ)..y,
            Complex.exp (-2 * Real.pi * Complex.I * (beta * (t - u))) := by
      simpa using hsub.symm
    exact hsub'.trans hfactor
  · linarith

/-- The literal continuous overlap length is the real volume of the exact
intersection `(X,2X] ∩ (x,x+y]`. -/
theorem dyadicContinuousWindowLength_eq_volume_inter
    (X x y : ℝ) :
    dyadicContinuousWindowLength X x y =
      (volume (Set.Ioc X (2 * X) ∩ Set.Ioc x (x + y))).toReal := by
  rw [Set.Ioc_inter_Ioc, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal']
  unfold dyadicContinuousWindowLength
  rw [max_comm]

/-- Integral form of the overlap length, retaining the literal half-open
endpoints. -/
theorem integral_slidingAtom_dyadic
    (X x y : ℝ) :
    (∫ t in Set.Ioc X (2 * X), slidingAtom t y x) =
      (dyadicContinuousWindowLength X x y : ℂ) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  have hfun :
      (Set.Ioc X (2 * X)).indicator (fun t => slidingAtom t y x) =
        (Set.Ioc X (2 * X) ∩ Set.Ioc x (x + y)).indicator
          (fun _ => (1 : ℂ)) := by
    funext t
    by_cases ht : t ∈ Set.Ioc X (2 * X)
    · by_cases hw : x < t ∧ t ≤ x + y
      · simp [ht, hw, slidingAtom_apply]
      · have hnot : t ∉ Set.Ioc x (x + y) := by simpa [Set.mem_Ioc] using hw
        simp [ht, hnot, slidingAtom_apply, hw]
    · simp [ht]
  rw [hfun, MeasureTheory.integral_indicator_const (1 : ℂ)
    (measurableSet_Ioc.inter measurableSet_Ioc)]
  rw [dyadicContinuousWindowLength_eq_volume_inter]
  simp [MeasureTheory.measureReal_def]


/-- Exact indicator expansion of the atomic sliding window. -/
theorem twistedPrimeSlidingWindow_eq_sum_slidingAtom
    (X : ℝ) (q a : ℕ) (x y : ℝ) :
    twistedPrimeSlidingWindow X q a x y =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          fourier (n : ℤ) (rationalCenter q a)) *
            slidingAtom (n : ℝ) y x := by
  unfold twistedPrimeSlidingWindow
  apply Finset.sum_congr rfl
  intro n hn
  rw [slidingAtom_apply]
  split_ifs <;> ring

/-- The atomic sliding field is integrable. -/
theorem integrable_twistedPrimeSlidingWindow
    (X : ℝ) (q a : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => twistedPrimeSlidingWindow X q a x y) := by
  simp_rw [twistedPrimeSlidingWindow_eq_sum_slidingAtom]
  apply integrable_finset_sum
  intro n hn
  exact (integrable_slidingAtom (n : ℝ) y).const_mul _

/-- Fourier transform of a scalar sliding atom. -/
theorem fourier_const_mul_slidingAtom
    (c : ℂ) (t y beta : ℝ) (hy : 0 ≤ y) :
    (𝓕 (fun x : ℝ => c * slidingAtom t y x)) beta =
      c * Complex.exp (-2 * Real.pi * Complex.I * (beta * t)) *
        gallagherWindowKernel y beta := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfa := fourier_slidingAtom t y beta hy
  rw [Real.fourier_real_eq_integral_exp_smul] at hfa
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
        (c * slidingAtom t y x)) =
      c * ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
        slidingAtom t y x := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ = c * (Complex.exp (-2 * Real.pi * Complex.I * (beta * t)) *
        gallagherWindowKernel y beta) := by rw [hfa]
    _ = _ := by ring

/-- The negative real phase combines with the rational center exactly as in
`signedFourierDiscrepancy X q a (-beta)`. -/
theorem rational_phase_mul_exp_neg_eq
    (q a n : ℕ) (beta : ℝ) :
    fourier (n : ℤ) (rationalCenter q a) *
        Complex.exp (-2 * Real.pi * Complex.I *
          (((beta * (n : ℝ)) : ℝ) : ℂ)) =
      fourier (n : ℤ)
        (rationalCenter q a + ((-beta : ℝ) : UnitAddCircle)) := by
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
  congr 1
  have hphase :
      Complex.exp (-2 * Real.pi * Complex.I *
          (((beta * (n : ℝ)) : ℝ) : ℂ)) =
        fourier (n : ℤ) ((-beta : ℝ) : UnitAddCircle) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  simpa only [fourier_apply] using hphase

/-- Exact Fourier transform of the literal atomic sliding discrepancy. -/
theorem fourier_twistedPrimeSlidingWindow
    (X : ℝ) (q a : ℕ) (y beta : ℝ) (hy : 0 ≤ y) :
    (𝓕 (fun x : ℝ => twistedPrimeSlidingWindow X q a x y)) beta =
      gallagherWindowKernel y beta *
        primeExponentialSum X
          (rationalCenter q a + ((-beta : ℝ) : UnitAddCircle)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [twistedPrimeSlidingWindow_eq_sum_slidingAtom]
  simp_rw [Finset.smul_sum]
  rw [integral_finset_sum]
  · simp_rw [← Real.fourier_real_eq_integral_exp_smul,
      fourier_const_mul_slidingAtom _ _ _ _ hy]
    unfold primeExponentialSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    calc
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
          fourier (n : ℤ) (rationalCenter q a)) *
            Complex.exp (-2 * Real.pi * Complex.I * (beta * (n : ℝ))) *
              gallagherWindowKernel y beta =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (fourier (n : ℤ) (rationalCenter q a) *
              Complex.exp (-2 * Real.pi * Complex.I * (beta * (n : ℝ)))) *
                gallagherWindowKernel y beta := by ring
      _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
            fourier (n : ℤ)
              (rationalCenter q a + ((-beta : ℝ) : UnitAddCircle)) *
                gallagherWindowKernel y beta := by
          have hp := rational_phase_mul_exp_neg_eq q a n beta
          push_cast at hp ⊢
          rw [hp]
      _ = gallagherWindowKernel y beta *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              fourier (n : ℤ)
                (rationalCenter q a + ((-beta : ℝ) : UnitAddCircle))) := by ring
  · intro n hn
    have hi := (integrable_slidingAtom (n : ℝ) y).const_mul
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        fourier (n : ℤ) (rationalCenter q a))
    have hc : Continuous
        (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I)) := by
      fun_prop
    have hn : ∀ x : ℝ,
        ‖Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I)‖ ≤ 1 := by
      intro x
      rw [show (↑(-2 * Real.pi * x * beta) : ℂ) * Complex.I =
          ((-2 * Real.pi * x * beta : ℝ) : ℂ) * Complex.I by rfl,
        Complex.norm_exp_ofReal_mul_I]
    simpa only [smul_eq_mul] using
      hi.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)

end
end MAPNearCollarGallagher
