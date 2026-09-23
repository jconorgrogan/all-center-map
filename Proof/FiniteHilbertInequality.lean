import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MontgomeryVaughanFiniteReduction

noncomputable section

open scoped BigOperators ComplexConjugate Interval Real
open MeasureTheory intervalIntegral AddCircle Complex

private theorem fourierCoeffOn_zero (k : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (0 : ℝ → ℂ) k = 0 := by
  unfold fourierCoeffOn fourierCoeff
  apply integral_eq_zero_of_ae
  filter_upwards with t
  simp [AddCircle.liftIoc]

private theorem fourierCoeffOn_const_nonzero
    (c : ℂ) (k : ℤ) (hk : k ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun _ : ℝ ↦ c) k = 0 := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hk
    (f' := fun _ : ℝ ↦ (0 : ℂ))]
  · rw [show (fun _ : ℝ ↦ (0 : ℂ)) = 0 by rfl, fourierCoeffOn_zero]
    simp
  · intro x hx
    simpa using (hasDerivAt_const x c)
  · exact intervalIntegrable_const

theorem fourierCoeffOn_sawtooth
    (k : ℤ) (hk : k ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun x : ℝ ↦ ((1 - 2 * x : ℝ) : ℂ)) k =
      -Complex.I / (Real.pi * (k : ℂ)) := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hk
    (f' := fun _ : ℝ ↦ (-2 : ℂ))]
  · rw [fourierCoeffOn_const_nonzero (-2) k hk]
    simp
    field_simp [hk, Real.pi_ne_zero]
  · intro x hx
    convert (hasDerivAt_const x (1 : ℂ)).sub
      ((hasDerivAt_id x).ofReal_comp.const_mul (2 : ℂ)) using 1
    · funext y
      simp [id_eq]
    · norm_num
  · exact intervalIntegrable_const

theorem intKernel_eq_sawtoothIntegral
    (n m : ℤ) (hne : n ≠ m) :
    (1 : ℂ) / ((n - m : ℤ) : ℂ) =
      -Real.pi * Complex.I *
        ∫ x in (0 : ℝ)..1,
          ((1 - 2 * x : ℝ) : ℂ) *
            @fourier (1 : ℝ) (n - m) (x : AddCircle (1 : ℝ)) := by
  have hmn : m - n ≠ 0 := sub_ne_zero.mpr hne.symm
  have hcoeff := fourierCoeffOn_sawtooth (m - n) hmn
  rw [fourierCoeffOn_eq_integral] at hcoeff
  norm_num [smul_eq_mul] at hcoeff
  have hintegral :
      (∫ x in (0 : ℝ)..1,
          ((1 - 2 * x : ℝ) : ℂ) *
          @fourier (1 : ℝ) (n - m) (x : AddCircle (1 : ℝ))) =
        -Complex.I / (Real.pi * ((m : ℂ) - n)) := by
    calc
      _ = ∫ x in (0 : ℝ)..1,
          Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * x) *
            (1 - 2 * (x : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp only
          rw [fourier_coe_apply]
          push_cast
          ring
      _ = _ := hcoeff
  rw [hintegral]
  push_cast
  have hnmC : (n : ℂ) - m ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hne
  have hmnC : (m : ℂ) - n ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hne.symm
  field_simp [hnmC, hmnC, Real.pi_ne_zero]
  simp [Complex.I_mul_I]

theorem inv_log_sub_eq_logMeanIntegral
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    (1 : ℂ) / ((Real.log x - Real.log y : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..1,
        Complex.exp
          (((t * Real.log x + (1 - t) * Real.log y : ℝ) : ℂ)) /
            ((x - y : ℝ) : ℂ) := by
  have hlogne : Real.log x - Real.log y ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hlog
    exact hne <| Real.strictMonoOn_log.injOn
      (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) hlog
  have hc : (((Real.log x - Real.log y : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hlogne
  have hlogC : ((Real.log x : ℂ) - (Real.log y : ℂ)) ≠ 0 := by
    exact_mod_cast hlogne
  have hxyC : (((x - y : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hxexp : Complex.exp ((Real.log x : ℝ) : ℂ) = (x : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hx]
  have hyexp : Complex.exp ((Real.log y : ℝ) : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hy]
  have hexp := integral_exp_mul_complex
    (a := (0 : ℝ)) (b := 1) hc
  rw [intervalIntegral.integral_div]
  have hform :
      (∫ t in (0 : ℝ)..1,
          Complex.exp
            (((t * Real.log x + (1 - t) * Real.log y : ℝ) : ℂ))) =
        ((x - y : ℝ) : ℂ) /
          ((Real.log x - Real.log y : ℝ) : ℂ) := by
    calc
      _ = (y : ℂ) *
          ∫ t in (0 : ℝ)..1,
            Complex.exp
              ((((Real.log x - Real.log y : ℝ) : ℂ)) * t) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t ht
            dsimp only
            rw [← hyexp]
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
      _ = (y : ℂ) *
          ((Complex.exp (((Real.log x - Real.log y : ℝ) : ℂ)) - 1) /
            ((Real.log x - Real.log y : ℝ) : ℂ)) := by
            rw [hexp]
            norm_num
      _ = ((x - y : ℝ) : ℂ) /
          ((Real.log x - Real.log y : ℝ) : ℂ) := by
            rw [show (((Real.log x - Real.log y : ℝ) : ℂ)) =
              ((Real.log x : ℝ) : ℂ) - ((Real.log y : ℝ) : ℂ) by norm_cast]
            rw [Complex.exp_sub, hxexp, hyexp]
            field_simp [Complex.ofReal_ne_zero.mpr hx.ne',
              Complex.ofReal_ne_zero.mpr hy.ne', hlogC]
            norm_cast
  rw [hform]
  field_simp [hc, hxyC]

def trigPoly (s : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, a n * @fourier (1 : ℝ) n (x : AddCircle (1 : ℝ))

private theorem intervalIntegral_fourier (k : ℤ) :
    (∫ x in (0 : ℝ)..1,
      @fourier (1 : ℝ) k (x : AddCircle (1 : ℝ))) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [fourier_zero]
  · have hcoeff := fourierCoeffOn_const_nonzero (1 : ℂ) (-k) (neg_ne_zero.mpr hk)
    rw [fourierCoeffOn_eq_integral] at hcoeff
    norm_num [smul_eq_mul] at hcoeff
    rw [if_neg hk]
    convert hcoeff using 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [fourier_coe_apply]
    norm_num

theorem intervalIntegral_trigPoly_mul_conj
    (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..1, trigPoly s a x * star (trigPoly s a x)) =
      (∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) := by
  classical
  have hexpand (x : ℝ) :
      trigPoly s a x * star (trigPoly s a x) =
        ∑ n ∈ s, ∑ m ∈ s,
          (a n * star (a m)) *
            @fourier (1 : ℝ) (n - m) (x : AddCircle (1 : ℝ)) := by
    unfold trigPoly
    rw [star_sum]
    simp_rw [star_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hstar : star (@fourier (1 : ℝ) m (x : AddCircle (1 : ℝ))) =
        @fourier (1 : ℝ) (-m) (x : AddCircle (1 : ℝ)) := by
      change conj (@fourier (1 : ℝ) m (x : AddCircle (1 : ℝ))) = _
      exact fourier_neg.symm
    rw [hstar]
    calc
      _ = (a n * star (a m)) *
          (@fourier (1 : ℝ) n (x : AddCircle (1 : ℝ)) *
            @fourier (1 : ℝ) (-m) (x : AddCircle (1 : ℝ))) := by ring
      _ = _ := by
        rw [← fourier_add]
        congr 2
  rw [intervalIntegral.integral_congr (fun x hx ↦ hexpand x)]
  rw [intervalIntegral.integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, intervalIntegral_fourier]
      simp [sub_eq_zero, hn, Complex.mul_conj, ← Complex.sq_norm]
    · intro m hm
      apply Continuous.intervalIntegrable
      fun_prop
  · intro n hn
    apply Continuous.intervalIntegrable
    fun_prop

theorem intervalIntegral_norm_sq_trigPoly
    (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖trigPoly s a x‖ ^ 2) =
      ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have h := intervalIntegral_trigPoly_mul_conj s a
  have hpoint : (fun x : ℝ ↦ trigPoly s a x * star (trigPoly s a x)) =
      fun x : ℝ ↦ ((‖trigPoly s a x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    change trigPoly s a x * conj (trigPoly s a x) = _
    rw [Complex.mul_conj, ← Complex.sq_norm]
  rw [hpoint, intervalIntegral.integral_ofReal] at h
  exact Complex.ofReal_injective h

def discreteHilbertForm (s : Finset ℤ) (a b : ℤ → ℂ) : ℂ :=
  ∑ n ∈ s, ∑ m ∈ s.erase n,
    (a n * star (b m)) / ((n - m : ℤ) : ℂ)

private theorem intervalIntegral_sawtooth_complex :
    (∫ x in (0 : ℝ)..1, ((1 - 2 * x : ℝ) : ℂ)) = 0 := by
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    norm_num
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_const.mul continuous_id).intervalIntegrable _ _

theorem discreteHilbertForm_eq_sawtoothIntegral
    (s : Finset ℤ) (a b : ℤ → ℂ) :
    discreteHilbertForm s a b =
      -Real.pi * Complex.I *
        ∫ x in (0 : ℝ)..1,
          ((1 - 2 * x : ℝ) : ℂ) *
            trigPoly s a x * star (trigPoly s b x) := by
  classical
  have hexpand (x : ℝ) :
      ((1 - 2 * x : ℝ) : ℂ) * trigPoly s a x * star (trigPoly s b x) =
        ∑ n ∈ s, ∑ m ∈ s,
          (a n * star (b m)) *
            (((1 - 2 * x : ℝ) : ℂ) *
              @fourier (1 : ℝ) (n - m) (x : AddCircle (1 : ℝ))) := by
    unfold trigPoly
    rw [star_sum]
    simp_rw [star_mul]
    rw [show
      ((1 - 2 * x : ℝ) : ℂ) *
          (∑ n ∈ s, a n * @fourier (1 : ℝ) n (x : AddCircle (1 : ℝ))) *
          (∑ m ∈ s,
            star (@fourier (1 : ℝ) m (x : AddCircle (1 : ℝ))) * star (b m)) =
        ((∑ n ∈ s, a n * @fourier (1 : ℝ) n (x : AddCircle (1 : ℝ))) *
          (∑ m ∈ s,
            star (@fourier (1 : ℝ) m (x : AddCircle (1 : ℝ))) * star (b m))) *
          ((1 - 2 * x : ℝ) : ℂ) by ring]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    have hstar : star (@fourier (1 : ℝ) m (x : AddCircle (1 : ℝ))) =
        @fourier (1 : ℝ) (-m) (x : AddCircle (1 : ℝ)) := by
      change conj (@fourier (1 : ℝ) m (x : AddCircle (1 : ℝ))) = _
      exact fourier_neg.symm
    rw [hstar]
    calc
      _ = (a n * star (b m)) *
          (((1 - 2 * x : ℝ) : ℂ) *
            (@fourier (1 : ℝ) n (x : AddCircle (1 : ℝ)) *
              @fourier (1 : ℝ) (-m) (x : AddCircle (1 : ℝ)))) := by ring
      _ = _ := by
        rw [← fourier_add]
        congr 2
  rw [intervalIntegral.integral_congr (fun x hx ↦ hexpand x)]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    unfold discreteHilbertForm
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      have hfull :
          (∑ m ∈ s.erase n,
              (a n * star (b m)) / ((n - m : ℤ) : ℂ)) =
            ∑ m ∈ s,
              if n = m then 0
              else (a n * star (b m)) / ((n - m : ℤ) : ℂ) := by
          rw [← Finset.sum_erase_add _ _ hn]
          rw [if_pos rfl, add_zero]
          apply Finset.sum_congr rfl
          intro m hm
          rw [if_neg (Finset.mem_erase.mp hm).1.symm]
      rw [hfull]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hnm : n = m
      · subst m
        rw [if_pos rfl, sub_self]
        simp_rw [fourier_zero]
        rw [intervalIntegral.integral_const_mul]
        rw [show (∫ x in (0 : ℝ)..1,
            ((1 - 2 * x : ℝ) : ℂ) * 1) = 0 by
          simpa using intervalIntegral_sawtooth_complex]
        simp
      · rw [if_neg hnm, intervalIntegral.integral_const_mul]
        calc
          (a n * star (b m)) / ((n - m : ℤ) : ℂ) =
              (a n * star (b m)) *
                ((1 : ℂ) / ((n - m : ℤ) : ℂ)) := by ring
          _ = _ := by
            rw [intKernel_eq_sawtoothIntegral n m hnm]
            ring
    · intro m hm
      apply Continuous.intervalIntegrable
      fun_prop
  · intro n hn
    apply Continuous.intervalIntegrable
    fun_prop

private theorem continuous_trigPoly (s : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (trigPoly s a) := by
  unfold trigPoly
  fun_prop

private theorem norm_trigPoly_le_sum (s : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) :
    ‖trigPoly s a x‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  unfold trigPoly
  calc
    ‖∑ n ∈ s, a n * @fourier (1 : ℝ) n (x : AddCircle (1 : ℝ))‖ ≤
        ∑ n ∈ s, ‖a n * @fourier (1 : ℝ) n (x : AddCircle (1 : ℝ))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ s, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

private theorem trigPoly_memLp_two_Ioc (s : Finset ℤ) (a : ℤ → ℂ) :
    MemLp (trigPoly s a) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound (p := (2 : ENNReal))
    (continuous_trigPoly s a).aestronglyMeasurable
    (∑ n ∈ s, ‖a n‖)
  exact Filter.Eventually.of_forall (norm_trigPoly_le_sum s a)

private theorem intervalIntegral_norm_trigPoly_mul_norm_le
    (s : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖trigPoly s a x‖ * ‖trigPoly s b x‖) ≤
      Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) *
        Real.sqrt (∑ n ∈ s, ‖b n‖ ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := trigPoly s a) (g := trigPoly s b)
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) hpq
    (by simpa using trigPoly_memLp_two_Ioc s a)
    (by simpa using trigPoly_memLp_two_Ioc s b)
  simp_rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  simpa [intervalIntegral_norm_sq_trigPoly, Real.sqrt_eq_rpow] using h

theorem finiteDiscreteHilbertBilinear
    (s : Finset ℤ) (a b : ℤ → ℂ) :
    ‖discreteHilbertForm s a b‖ ≤
      Real.pi * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) *
        Real.sqrt (∑ n ∈ s, ‖b n‖ ^ 2) := by
  rw [discreteHilbertForm_eq_sawtoothIntegral]
  have hsaw :
      ‖∫ x in (0 : ℝ)..1,
          ((1 - 2 * x : ℝ) : ℂ) * trigPoly s a x * star (trigPoly s b x)‖ ≤
        ∫ x in (0 : ℝ)..1, ‖trigPoly s a x‖ * ‖trigPoly s b x‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards with x hx
      have hw : |1 - 2 * x| ≤ (1 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      calc
        ‖((1 - 2 * x : ℝ) : ℂ) * trigPoly s a x * star (trigPoly s b x)‖ =
            |1 - 2 * x| * (‖trigPoly s a x‖ * ‖trigPoly s b x‖) := by
              rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
                Real.norm_eq_abs]
              ring
        _ ≤ 1 * (‖trigPoly s a x‖ * ‖trigPoly s b x‖) := by
              gcongr
        _ = _ := one_mul _
    · exact ((continuous_trigPoly s a).norm.mul
        (continuous_trigPoly s b).norm).intervalIntegrable _ _
  have hholder := intervalIntegral_norm_trigPoly_mul_norm_le s a b
  calc
    ‖-Real.pi * Complex.I *
        ∫ x in (0 : ℝ)..1,
          ((1 - 2 * x : ℝ) : ℂ) * trigPoly s a x * star (trigPoly s b x)‖ =
        Real.pi * ‖∫ x in (0 : ℝ)..1,
          ((1 - 2 * x : ℝ) : ℂ) * trigPoly s a x * star (trigPoly s b x)‖ := by
          rw [norm_mul]
          norm_num [abs_of_pos Real.pi_pos]
    _ ≤ Real.pi *
        (∫ x in (0 : ℝ)..1, ‖trigPoly s a x‖ * ‖trigPoly s b x‖) := by
          exact mul_le_mul_of_nonneg_left hsaw Real.pi_nonneg
    _ ≤ Real.pi *
        (Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) *
          Real.sqrt (∑ n ∈ s, ‖b n‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hholder Real.pi_nonneg
    _ = _ := by ring

def natDiscreteHilbertForm (s : Finset ℕ) (a b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ s, ∑ m ∈ s.erase n,
    (a n * star (b m)) / (((n : ℤ) - (m : ℤ) : ℤ) : ℂ)

theorem finiteNatDiscreteHilbertBilinear
    (s : Finset ℕ) (a b : ℕ → ℂ) :
    ‖natDiscreteHilbertForm s a b‖ ≤
      Real.pi * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) *
        Real.sqrt (∑ n ∈ s, ‖b n‖ ^ 2) := by
  let e : ℕ ↪ ℤ := ⟨fun n ↦ (n : ℤ), by
    intro n m h
    exact Int.ofNat_inj.mp h⟩
  have he (n : ℕ) : e n = (n : ℤ) := rfl
  have hform :
      discreteHilbertForm (s.map e)
          (fun z ↦ a z.natAbs) (fun z ↦ b z.natAbs) =
        natDiscreteHilbertForm s a b := by
    classical
    unfold discreteHilbertForm natDiscreteHilbertForm
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.map_erase]
    rw [Finset.sum_map]
    simp only [he, Int.natAbs_natCast]
  have henergyA :
      (∑ z ∈ s.map e, ‖a z.natAbs‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    simp only [Finset.sum_map, he, Int.natAbs_natCast]
  have henergyB :
      (∑ z ∈ s.map e, ‖b z.natAbs‖ ^ 2) = ∑ n ∈ s, ‖b n‖ ^ 2 := by
    simp only [Finset.sum_map, he, Int.natAbs_natCast]
  have h := finiteDiscreteHilbertBilinear (s.map e)
    (fun z ↦ a z.natAbs) (fun z ↦ b z.natAbs)
  rw [hform, henergyA, henergyB] at h
  exact h

namespace MontgomeryVaughanFiniteReduction

def normalizedLogWeight (N n : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (((u * (Real.log n - Real.log N) : ℝ) : ℂ))

private theorem normalizedLogWeight_norm_le_two
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ dyadicSupport N)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizedLogWeight N n u‖ ≤ 2 := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hnIoc := Finset.mem_Ioc.mp hn
  have hnpos : 0 < n := lt_trans hNpos hnIoc.1
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hnIoc.1.le
  have hnupperR : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnIoc.2
  have hlog_nonneg : 0 ≤ Real.log n - Real.log N := by
    exact sub_nonneg.mpr (Real.log_le_log hNposR hNnR)
  have hlog_le : Real.log n - Real.log N ≤ Real.log 2 := by
    have h := Real.log_le_log hnposR hnupperR
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNposR.ne'] at h
    linarith
  have hexponent : u * (Real.log n - Real.log N) ≤ Real.log 2 := by
    calc
      u * (Real.log n - Real.log N) ≤
          1 * (Real.log n - Real.log N) := by
            exact mul_le_mul_of_nonneg_right hu.2 hlog_nonneg
      _ ≤ Real.log 2 := by simpa using hlog_le
  unfold normalizedLogWeight
  rw [Complex.norm_exp, Complex.ofReal_re]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr hexponent

private theorem normalizedWeightedEnergy_le
    (N : ℕ) (a : ℕ → ℂ) (hN : 1 ≤ N)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∑ n ∈ dyadicSupport N, ‖normalizedLogWeight N n u * a n‖ ^ 2) ≤
      4 * coefficientEnergy a N := by
  unfold coefficientEnergy
  calc
    (∑ n ∈ dyadicSupport N, ‖normalizedLogWeight N n u * a n‖ ^ 2) ≤
        ∑ n ∈ dyadicSupport N, 4 * ‖a n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hw := normalizedLogWeight_norm_le_two hN hn hu
      rw [norm_mul]
      nlinarith [norm_nonneg (normalizedLogWeight N n u), norm_nonneg (a n),
        sq_nonneg (2 * ‖a n‖ - ‖normalizedLogWeight N n u‖ * ‖a n‖)]
    _ = 4 * ∑ n ∈ dyadicSupport N, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem normalizedNatDiscreteHilbert_le_four_pi_energy
    (N : ℕ) (a : ℕ → ℂ) (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖natDiscreteHilbertForm (dyadicSupport N)
        (fun n ↦ normalizedLogWeight N n t * a n)
        (fun n ↦ normalizedLogWeight N n (1 - t) * a n)‖ ≤
      4 * Real.pi * coefficientEnergy a N := by
  have hut : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hu1t : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hleft := normalizedWeightedEnergy_le N a hN hut
  have hright := normalizedWeightedEnergy_le N a hN hu1t
  have hE : 0 ≤ coefficientEnergy a N := by
    unfold coefficientEnergy
    positivity
  have hsqrt : Real.sqrt (4 * coefficientEnergy a N) =
      2 * Real.sqrt (coefficientEnergy a N) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hbase := finiteNatDiscreteHilbertBilinear (dyadicSupport N)
    (fun n ↦ normalizedLogWeight N n t * a n)
    (fun n ↦ normalizedLogWeight N n (1 - t) * a n)
  calc
    _ ≤ Real.pi *
        Real.sqrt (∑ n ∈ dyadicSupport N,
          ‖normalizedLogWeight N n t * a n‖ ^ 2) *
        Real.sqrt (∑ n ∈ dyadicSupport N,
          ‖normalizedLogWeight N n (1 - t) * a n‖ ^ 2) := hbase
    _ ≤ Real.pi * Real.sqrt (4 * coefficientEnergy a N) *
        Real.sqrt (4 * coefficientEnergy a N) := by
          gcongr
    _ = 4 * Real.pi * coefficientEnergy a N := by
      rw [hsqrt]
      calc
        Real.pi * (2 * Real.sqrt (coefficientEnergy a N)) *
            (2 * Real.sqrt (coefficientEnergy a N)) =
          4 * Real.pi * Real.sqrt (coefficientEnergy a N) ^ 2 := by ring
        _ = 4 * Real.pi * coefficientEnergy a N := by
          rw [Real.sq_sqrt hE]

private theorem inv_logGap_eq_normalizedMean
    {N n m : ℕ} (hN : 1 ≤ N)
    (hn : n ∈ dyadicSupport N) (hm : m ∈ dyadicSupport N)
    (hne : n ≠ m) :
    (1 : ℂ) / (logGap n m : ℂ) =
      (N : ℂ) * ∫ t in (0 : ℝ)..1,
        (normalizedLogWeight N n t *
          star (normalizedLogWeight N m (1 - t))) /
            (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hnIoc := Finset.mem_Ioc.mp hn
  have hmIoc := Finset.mem_Ioc.mp hm
  have hnpos : 0 < n := lt_trans hNpos hnIoc.1
  have hmpos : 0 < m := lt_trans hNpos hmIoc.1
  have hmean := inv_log_sub_eq_logMeanIntegral
    (x := (n : ℝ)) (y := (m : ℝ))
    (by exact_mod_cast hnpos) (by exact_mod_cast hmpos)
    (by exact_mod_cast hne)
  change (1 : ℂ) / (logGap n m : ℂ) = _
  rw [logGap]
  rw [hmean]
  rw [← intervalIntegral.integral_const_mul]
  have hden : ((((n : ℝ) - (m : ℝ) : ℝ) : ℂ)) =
      ((((n : ℤ) - (m : ℤ) : ℤ) : ℂ)) := by
    norm_cast
  apply intervalIntegral.integral_congr
  intro t ht
  have hNexp : Complex.exp ((Real.log N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hNpos)]
    norm_cast
  have hstar : star (normalizedLogWeight N m (1 - t)) =
      normalizedLogWeight N m (1 - t) := by
    unfold normalizedLogWeight
    change conj (Complex.exp (Complex.ofReal
      ((1 - t) * (Real.log m - Real.log N)))) =
        Complex.exp (Complex.ofReal
          ((1 - t) * (Real.log m - Real.log N)))
    rw [← Complex.ofReal_exp]
    exact conj_ofReal _
  dsimp only
  rw [hden, hstar]
  have hnum :
      Complex.exp
          (((t * Real.log n + (1 - t) * Real.log m : ℝ) : ℂ)) =
        (N : ℂ) *
          (normalizedLogWeight N n t * normalizedLogWeight N m (1 - t)) := by
    rw [← hNexp]
    unfold normalizedLogWeight
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hnum]
  simp only [div_eq_mul_inv, mul_assoc]

private theorem logHilbertForm_eq_normalizedIntegral
    (N : ℕ) (a : ℕ → ℂ) (hN : 1 ≤ N) :
    (∑ n ∈ dyadicSupport N,
        ∑ m ∈ (dyadicSupport N).erase n,
          (a n * star (a m)) / (logGap n m : ℂ)) =
      (N : ℂ) * ∫ t in (0 : ℝ)..1,
        natDiscreteHilbertForm (dyadicSupport N)
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m) := by
  classical
  have hterm (n : ℕ) (hn : n ∈ dyadicSupport N)
      (m : ℕ) (hm : m ∈ (dyadicSupport N).erase n) :
      (a n * star (a m)) / (logGap n m : ℂ) =
        (N : ℂ) * ∫ t in (0 : ℝ)..1,
          ((normalizedLogWeight N n t * a n) *
            star (normalizedLogWeight N m (1 - t) * a m)) /
              (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) := by
    have hm' := Finset.mem_erase.mp hm
    have hinv := inv_logGap_eq_normalizedMean hN hn hm'.2 hm'.1.symm
    calc
      (a n * star (a m)) / (logGap n m : ℂ) =
          (a n * star (a m)) * ((1 : ℂ) / (logGap n m : ℂ)) := by
            ring
      _ = (a n * star (a m)) *
          ((N : ℂ) * ∫ t in (0 : ℝ)..1,
            (normalizedLogWeight N n t *
              star (normalizedLogWeight N m (1 - t))) /
                (((n : ℤ) - (m : ℤ) : ℤ) : ℂ)) := by
            rw [hinv]
      _ = (N : ℂ) * ∫ t in (0 : ℝ)..1,
          (a n * star (a m)) *
            ((normalizedLogWeight N n t *
              star (normalizedLogWeight N m (1 - t))) /
                (((n : ℤ) - (m : ℤ) : ℤ) : ℂ)) := by
            rw [intervalIntegral.integral_const_mul]
            ring
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t ht
        simp_rw [star_mul]
        ring
  unfold natDiscreteHilbertForm
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm n hn m hm
    · intro m hm
      apply Continuous.intervalIntegrable
      unfold normalizedLogWeight
      fun_prop
  · intro n hn
    apply Continuous.intervalIntegrable
    unfold normalizedLogWeight
    fun_prop

theorem finiteLogHilbertInequality_via_integerHilbert :
    FiniteLogHilbertInequality := by
  refine ⟨4 * Real.pi, mul_pos (by norm_num) Real.pi_pos, ?_⟩
  intro N a hN
  change
    ‖∑ n ∈ dyadicSupport N,
        ∑ m ∈ (dyadicSupport N).erase n,
          (a n * star (a m)) / (logGap n m : ℂ)‖ ≤
      4 * Real.pi * N * coefficientEnergy a N
  rw [logHilbertForm_eq_normalizedIntegral N a hN]
  have hint :
      ‖∫ t in (0 : ℝ)..1,
        natDiscreteHilbertForm (dyadicSupport N)
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ ≤
        4 * Real.pi * coefficientEnergy a N := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1,
          4 * Real.pi * coefficientEnergy a N := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          exact normalizedNatDiscreteHilbert_le_four_pi_energy N a hN ht
        · exact intervalIntegrable_const
      _ = 4 * Real.pi * coefficientEnergy a N := by simp
  calc
    ‖(N : ℂ) * ∫ t in (0 : ℝ)..1,
        natDiscreteHilbertForm (dyadicSupport N)
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ =
      (N : ℝ) * ‖∫ t in (0 : ℝ)..1,
        natDiscreteHilbertForm (dyadicSupport N)
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ := by
        rw [norm_mul]
        norm_cast
    _ ≤ (N : ℝ) * (4 * Real.pi * coefficientEnergy a N) := by
      exact mul_le_mul_of_nonneg_left hint (Nat.cast_nonneg N)
    _ = 4 * Real.pi * N * coefficientEnergy a N := by ring

end MontgomeryVaughanFiniteReduction

end

#print axioms finiteDiscreteHilbertBilinear
#print axioms finiteNatDiscreteHilbertBilinear
#print axioms MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
