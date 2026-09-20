import SlidingFourierPair

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Set
open scoped BigOperators FourierTransform ArithmeticFunction ENNReal
noncomputable section
open PrimePairEndpoints MAPMajorArcWeld

/-- The exact two-dimensional support of the continuous sliding integral. -/
def continuousSlidingSupport (X y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioc X (2 * X) ∧ p.2 ∈ Set.Ico (p.1 - y) p.1}

theorem measurableSet_continuousSlidingSupport (X y : ℝ) :
    MeasurableSet (continuousSlidingSupport X y) := by
  unfold continuousSlidingSupport
  simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_Ico]
  measurability

theorem continuousSlidingSupport_subset_rectangle
    {X y : ℝ} (hy : 0 ≤ y) :
    continuousSlidingSupport X y ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc (X - y) (2 * X) := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  constructor
  · exact ⟨ht.1.le, ht.2⟩
  · constructor
    · linarith [ht.1, hx.1]
    · linarith [ht.2, hx.2]

/-- The compact support argument needed for the literal Fubini swap. -/
theorem integrable_continuousSlidingSupport_indicator
    {X y beta : ℝ} (hy : 0 ≤ y) :
    Integrable (fun p : ℝ × ℝ =>
      (continuousSlidingSupport X y).indicator
        (fun p => Complex.exp
          (↑(-2 * Real.pi * p.2 * beta) * Complex.I)) p) := by
  let R : Set (ℝ × ℝ) :=
    Set.Icc X (2 * X) ×ˢ Set.Icc (X - y) (2 * X)
  have hRcompact : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℂ)) R :=
    integrableOn_const hRcompact.measure_lt_top.ne
  have hsupport : continuousSlidingSupport X y ⊆ R :=
    continuousSlidingSupport_subset_rectangle hy
  have hone : Integrable
      ((continuousSlidingSupport X y).indicator (fun _ => (1 : ℂ))) :=
    (hconst.mono_set hsupport).integrable_indicator
      (measurableSet_continuousSlidingSupport X y)
  apply hone.mono
  · exact ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (↑(-2 * Real.pi * p.2 * beta) * Complex.I))).measurable.indicator
      (measurableSet_continuousSlidingSupport X y)).aestronglyMeasurable
  · filter_upwards with p
    by_cases hp : p ∈ continuousSlidingSupport X y
    · simp only [Set.indicator_of_mem hp]
      rw [show (↑(-2 * Real.pi * p.2 * beta) : ℂ) * Complex.I =
          ((-2 * Real.pi * p.2 * beta : ℝ) : ℂ) * Complex.I by rfl,
        Complex.norm_exp_ofReal_mul_I, norm_one]
    · simp [Set.indicator_of_notMem hp]

/-- The product integrand in the Fubini step is exactly the support indicator. -/
theorem phase_smul_sliding_indicator_eq_support_indicator
    (X y beta t x : ℝ) :
    Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
        (Set.Ioc X (2 * X)).indicator (fun t => slidingAtom t y x) t =
      (continuousSlidingSupport X y).indicator
        (fun p => Complex.exp
          (↑(-2 * Real.pi * p.2 * beta) * Complex.I)) (t, x) := by
  by_cases ht : t ∈ Set.Ioc X (2 * X)
  · by_cases hx : x ∈ Set.Ico (t - y) t
    · have hs : (t, x) ∈ continuousSlidingSupport X y := ⟨ht, hx⟩
      simp [Set.indicator_of_mem ht, Set.indicator_of_mem hx,
        Set.indicator_of_mem hs, slidingAtom]
    · have hs : (t, x) ∉ continuousSlidingSupport X y := by
        intro h
        exact hx h.2
      simp [Set.indicator_of_mem ht, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hs, slidingAtom]
  · have hs : (t, x) ∉ continuousSlidingSupport X y := by
      intro h
      exact ht h.1
    simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem hs]

/-- Exact Fourier transform of the continuous overlap field. -/
theorem fourier_dyadicContinuousWindowLength
    (X y beta : ℝ) (hX : 0 ≤ X) (hy : 0 ≤ y) :
    (𝓕 (fun x : ℝ =>
      (dyadicContinuousWindowLength X x y : ℂ))) beta =
      gallagherWindowKernel y beta * dyadicContinuousAmplitude X (-beta) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let F : ℝ → ℝ → ℂ := fun x t =>
    Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
      (Set.Ioc X (2 * X)).indicator (fun t => slidingAtom t y x) t
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hs := integrable_continuousSlidingSupport_indicator
      (X := X) (y := y) (beta := beta) hy
    apply hs.swap.congr
    filter_upwards with p
    rcases p with ⟨x, t⟩
    simpa only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair, F]
      using (phase_smul_sliding_indicator_eq_support_indicator
        X y beta t x).symm
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
        (dyadicContinuousWindowLength X x y : ℂ)) =
      ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
        (∫ t in Set.Ioc X (2 * X), slidingAtom t y x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [integral_slidingAtom_dyadic]
    _ = ∫ x : ℝ, ∫ t : ℝ, F x t := by
          apply integral_congr_ae
          filter_upwards with x
          unfold F
          rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
          rw [MeasureTheory.integral_smul]
    _ = ∫ t : ℝ, ∫ x : ℝ, F x t :=
      MeasureTheory.integral_integral_swap hF
    _ = ∫ t in Set.Ioc X (2 * X),
        ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * beta) * Complex.I) •
          slidingAtom t y x := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
          apply integral_congr_ae
          filter_upwards with t
          by_cases ht : t ∈ Set.Ioc X (2 * X)
          · simp only [Set.indicator_of_mem ht]
            unfold F
            apply integral_congr_ae
            filter_upwards with x
            rw [Set.indicator_of_mem ht]
          · simp only [Set.indicator_of_notMem ht]
            unfold F
            simp [Set.indicator_of_notMem ht]
    _ = ∫ t in Set.Ioc X (2 * X),
        Complex.exp (-2 * Real.pi * Complex.I * (beta * t)) *
          gallagherWindowKernel y beta := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          simpa only [← Real.fourier_real_eq_integral_exp_smul] using
            fourier_slidingAtom t y beta hy
    _ = gallagherWindowKernel y beta * dyadicContinuousAmplitude X (-beta) := by
          rw [← intervalIntegral.integral_of_le (by linarith : X ≤ 2 * X)]
          unfold dyadicContinuousAmplitude
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp only
          have he : Complex.exp (-2 * Real.pi * Complex.I *
                ((beta : ℂ) * (t : ℂ))) =
              Complex.exp (2 * Real.pi * Complex.I *
                (((-beta : ℝ) : ℂ) * (t : ℂ))) := by
            congr 1
            push_cast
            ring
          rw [he]
          ring

end
end MAPNearCollarGallagher
