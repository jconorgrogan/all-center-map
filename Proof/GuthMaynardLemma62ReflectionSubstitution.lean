import GuthMaynardLemma62Fubini
import GuthMaynardReflectionKernelVdC

/-!
# The common reflection interval in Guth--Maynard Lemma 6.2

For `1 ≤ m ≤ M`, the source first enlarges the cutoff integral from `[1,2]`
to `[1/m,2M/m]`.  This is an exact equality because the cutoff vanishes off
`[1,2]`.  Mellin inversion and Fubini may then be applied on that positive
compact interval, after which `v=Nmu` gives the common interval `[N,2NM]`.
-/

namespace GuthMaynardLemma62ReflectionSubstitution

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma62FarTail
open GuthMaynardLemma62MellinInversion
open GuthMaynardLemma62MellinInsertion
open GuthMaynardLemma62Fubini
open GuthMaynardReflectionKernelVdC
open MAPMRTCorollary53Source

noncomputable section

def sectionThreeBaseIntegrand (t xi u : ℝ) : ℂ :=
  sectionThreeFourierPhase xi u * sectionThreeOscillatory t u

theorem sectionThreeBaseIntegrand_eq_zero_of_not_mem
    (t xi u : ℝ) (hu : u ∉ Set.Icc (1 : ℝ) 2) :
    sectionThreeBaseIntegrand t xi u = 0 := by
  unfold sectionThreeBaseIntegrand
  rw [sectionThreeOscillatory_supported t u hu, mul_zero]

/-- Exact support enlargement used before Mellin inversion in the source. -/
theorem sectionThreeFourierCoefficient_eq_extendedIntegral
    (t xi : ℝ) {a b : ℝ} (ha : a ≤ 1) (hb : 2 ≤ b) :
    sectionThreeFourierCoefficient t xi =
      ∫ u : ℝ in Set.Icc a b, sectionThreeBaseIntegrand t xi u := by
  rw [sectionThreeFourierCoefficient_eq_integral]
  change (∫ u : ℝ, sectionThreeBaseIntegrand t xi u) = _
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases huBig : u ∈ Set.Icc a b
  · simp [huBig]
  · have huSmall : u ∉ Set.Icc (1 : ℝ) 2 := by
      intro hu
      exact huBig ⟨ha.trans hu.1, hu.2.trans hb⟩
    rw [sectionThreeBaseIntegrand_eq_zero_of_not_mem t xi u huSmall]
    simp [huBig]

/-- Mellin insertion on an arbitrary positive enlarged interval. -/
theorem sectionThreeFourierCoefficient_eq_mellinInserted_Icc
    (t xi : ℝ) {a b : ℝ}
    (haPos : 0 < a) (ha : a ≤ 1) (hb : 2 ≤ b) :
    sectionThreeFourierCoefficient t xi =
      ∫ u : ℝ in Set.Icc a b,
        sectionThreeFourierPhase xi u *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            sectionThreeMellinLineIntegral u) *
          (u : ℂ) ^ (Complex.I * (t : ℂ)) := by
  rw [sectionThreeFourierCoefficient_eq_extendedIntegral t xi ha hb]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have huPos : 0 < u := haPos.trans_le hu.1
  unfold sectionThreeBaseIntegrand sectionThreeOscillatory
  rw [sectionThreeCutoff_mellin_inversion huPos]
  unfold sectionThreeMellinLineIntegral
  ring

/-- Exact Fubini formula on the source interval `[1/m,2M/m]`. -/
theorem sectionThreeFourierCoefficient_eq_mellinFubini_Icc
    (t xi : ℝ) {a b : ℝ}
    (haPos : 0 < a) (ha : a ≤ 1) (hb : 2 ≤ b) :
    sectionThreeFourierCoefficient t xi =
      ∫ r : ℝ,
        ∫ u : ℝ in Set.Icc a b,
          sectionThreeMellinFubiniKernel t xi u r := by
  rw [sectionThreeFourierCoefficient_eq_mellinInserted_Icc t xi haPos ha hb]
  calc
    (∫ u : ℝ in Set.Icc a b,
        sectionThreeFourierPhase xi u *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            sectionThreeMellinLineIntegral u) *
          (u : ℂ) ^ (Complex.I * (t : ℂ))) =
      ∫ u : ℝ in Set.Icc a b,
        ∫ r : ℝ, sectionThreeMellinFubiniKernel t xi u r := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have huPos : 0 < u := haPos.trans_le hu.1
      unfold sectionThreeMellinFubiniKernel sectionThreeMellinLineIntegral
      simp_rw [← mellinPowerExp_eq_cpow huPos]
      rw [← oscillatoryPowerExp_eq_cpow huPos]
      rw [MeasureTheory.integral_mul_const]
      rw [← MeasureTheory.integral_const_mul]
      rw [← MeasureTheory.integral_const_mul]
    _ = _ := sectionThreeMellinFubini_swap_Icc t xi haPos
      (le_trans ha (le_trans (by norm_num) hb))

/-- Source-specialized common interval.  The next deterministic step is the
linear substitution `v=Nmu`; its endpoints are now literally `N` and `2NM`. -/
theorem sectionThreeFourierCoefficient_eq_sourceCommonInterval
    (t N m M : ℝ) (_hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    sectionThreeFourierCoefficient t (m * N) =
      ∫ r : ℝ,
        ∫ u : ℝ in Set.Icc (1 / m) (2 * M / m),
          sectionThreeMellinFubiniKernel t (m * N) u r := by
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  apply sectionThreeFourierCoefficient_eq_mellinFubini_Icc
  · positivity
  · exact (div_le_iff₀ hmPos).2 (by simpa using hm)
  · rw [le_div_iff₀ hmPos]
    nlinarith

def reflectionScalePhase (tau c : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (tau : ℂ) * (Real.log c : ℂ))

theorem norm_reflectionScalePhase (tau c : ℝ) :
    ‖reflectionScalePhase tau c‖ = 1 := by
  unfold reflectionScalePhase
  rw [Complex.norm_exp]
  simp

/-- Pointwise algebra behind `v=Nmu`: the Jacobian cancels the `u⁻¹`
factor, leaving the scale phase times the literal reflection kernel. -/
theorem sourceKernel_after_substitution
    {t r N m v : ℝ} (hN : 0 < N) (hm : 0 < m) (hv : 0 < v) :
    (((m * N)⁻¹ : ℝ) : ℂ) *
        sectionThreeMellinFubiniKernel t (m * N) (v / (m * N)) r =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
          reflectionScalePhase (t - r) (m * N)) *
        (additivePhase (reflectionPhase (t - r) v) *
          reflectionAmplitude v) := by
  have hc : 0 < m * N := mul_pos hm hN
  have hvDiv : 0 < v / (m * N) := div_pos hv hc
  rw [reflectionKernel_eq_exp_form hv]
  unfold sectionThreeMellinFubiniKernel sectionThreeFourierPhase
    mellinPowerExp oscillatoryPowerExp reflectionScalePhase
  have hphaseArg :
      (-2 * Real.pi * (v / (m * N)) * (m * N) : ℝ) =
        -2 * Real.pi * v := by field_simp [hc.ne']
  rw [hphaseArg]
  have hlogDiv : Real.log (v / (m * N)) =
      Real.log v - Real.log (m * N) := by
    rw [Real.log_div hv.ne' hc.ne']
  rw [hlogDiv]
  have hExp :
      Complex.exp
          ((-(1 : ℂ) - (r : ℂ) * Complex.I) *
            ((Real.log v : ℂ) - (Real.log (m * N) : ℂ))) *
        Complex.exp
          (Complex.I * (t : ℂ) *
            ((Real.log v : ℂ) - (Real.log (m * N) : ℂ))) =
      Complex.exp ((-(1 : ℂ)) * (-(Real.log (m * N) : ℂ))) *
        Complex.exp
          (Complex.I * ((t - r : ℝ) : ℂ) * (Real.log v : ℂ)) *
        Complex.exp
          (-Complex.I * ((t - r : ℝ) : ℂ) *
            (Real.log (m * N) : ℂ)) *
        Complex.exp ((-(1 : ℂ)) * (Real.log v : ℂ)) := by
    rw [← Complex.exp_add]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hInv : (((m * N)⁻¹ : ℝ) : ℂ) *
      Complex.exp ((-(1 : ℂ)) * (-(Real.log (m * N) : ℂ))) = 1 := by
    rw [show (-(1 : ℂ)) * (-(Real.log (m * N) : ℂ)) =
      (Real.log (m * N) : ℂ) by ring]
    rw [← Complex.ofReal_exp, Real.exp_log hc]
    push_cast
    have hcC : (m : ℂ) * (N : ℂ) ≠ 0 := by
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hm.ne')
        (Complex.ofReal_ne_zero.mpr hN.ne')
    exact inv_mul_cancel₀ hcC
  have hvInv : Complex.exp ((-(1 : ℂ)) * (Real.log v : ℂ)) =
      ((v⁻¹ : ℝ) : ℂ) := by
    rw [show (-(1 : ℂ)) * (Real.log v : ℂ) =
      (-(Real.log v) : ℝ) by push_cast; ring]
    rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hv]
  let E1 : ℂ := Complex.exp
    ((-(1 : ℂ) - (r : ℂ) * Complex.I) *
      ((Real.log v - Real.log (m * N) : ℝ) : ℂ))
  let E2 : ℂ := Complex.exp
    (Complex.I * (t : ℂ) *
      ((Real.log v - Real.log (m * N) : ℝ) : ℂ))
  let P : ℂ :=
    Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I)
  let H : ℂ := mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)
  let C : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  change (((m * N)⁻¹ : ℝ) : ℂ) * (P * (C * (E1 * H)) * E2) = _
  calc
    _ = (((m * N)⁻¹ : ℝ) : ℂ) * C * H * P * (E1 * E2) := by ring
    _ = (((m * N)⁻¹ : ℝ) : ℂ) * C * H * P *
        (Complex.exp ((-(1 : ℂ)) * (-(Real.log (m * N) : ℂ))) *
          Complex.exp
            (Complex.I * ((t - r : ℝ) : ℂ) * (Real.log v : ℂ)) *
          Complex.exp
            (-Complex.I * ((t - r : ℝ) : ℂ) *
              (Real.log (m * N) : ℂ)) *
          Complex.exp ((-(1 : ℂ)) * (Real.log v : ℂ))) := by
            rw [show E1 * E2 = _ by
              unfold E1 E2
              push_cast
              exact hExp]
    _ = ((((m * N)⁻¹ : ℝ) : ℂ) *
          Complex.exp ((-(1 : ℂ)) * (-(Real.log (m * N) : ℂ)))) *
        C * H * P *
        Complex.exp
          (Complex.I * ((t - r : ℝ) : ℂ) * (Real.log v : ℂ)) *
        Complex.exp
          (-Complex.I * ((t - r : ℝ) : ℂ) *
            (Real.log (m * N) : ℂ)) *
        Complex.exp ((-(1 : ℂ)) * (Real.log v : ℂ)) := by ring
    _ = _ := by rw [hInv, hvInv]; unfold C H P; push_cast; ring

/-- Exact linear change of variables for the source kernel, with common
endpoints `[N,2NM]`. -/
theorem sourceKernel_integral_substitution
    {t r N m M : ℝ} (hN : 0 < N) (hm : 0 < m) (hM : 1 ≤ M) :
    (∫ u : ℝ in (1 / m)..(2 * M / m),
        sectionThreeMellinFubiniKernel t (m * N) u r) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
          reflectionScalePhase (t - r) (m * N)) *
        (∫ v : ℝ in N..(2 * N * M),
          additivePhase (reflectionPhase (t - r) v) *
            reflectionAmplitude v) := by
  let c : ℝ := m * N
  have hc : 0 < c := mul_pos hm hN
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun v : ℝ => sectionThreeMellinFubiniKernel t (m * N) (v / c) r)
    hc.ne'
    (a := 1 / m) (b := 2 * M / m)
  have hleft :
      (fun u : ℝ =>
        sectionThreeMellinFubiniKernel t (m * N) ((c * u) / c) r) =
      fun u : ℝ => sectionThreeMellinFubiniKernel t (m * N) u r := by
    funext u
    rw [mul_div_cancel_left₀ u hc.ne']
  rw [hleft] at hsub
  rw [show c * (1 / m) = N by unfold c; field_simp [hm.ne']] at hsub
  rw [show c * (2 * M / m) = 2 * N * M by
    unfold c; field_simp [hm.ne']] at hsub
  rw [hsub]
  change (((c⁻¹ : ℝ) : ℂ) *
      ∫ v : ℝ in N..2 * N * M,
        sectionThreeMellinFubiniKernel t (m * N) (v / c) r) = _
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hvMem
  have hEnds : N ≤ 2 * N * M := by nlinarith [mul_pos hN (show 0 < M by linarith)]
  rw [Set.uIcc_of_le hEnds] at hvMem
  have hvPos : 0 < v := hN.trans_le hvMem.1
  change (((c⁻¹ : ℝ) : ℂ) *
      sectionThreeMellinFubiniKernel t (m * N) (v / c) r) = _
  unfold c
  exact sourceKernel_after_substitution hN hm hvPos

/-- Exact positive-frequency reflected Mellin formula, including the common
`[N,2NM]` interval and every normalization factor. -/
theorem sectionThreeFourierCoefficient_eq_positiveReflectedMellin
    {t N m M : ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    sectionThreeFourierCoefficient t (m * N) =
      ∫ r : ℝ,
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
            reflectionScalePhase (t - r) (m * N)) *
          (∫ v : ℝ in N..(2 * N * M),
            additivePhase (reflectionPhase (t - r) v) *
              reflectionAmplitude v) := by
  rw [sectionThreeFourierCoefficient_eq_sourceCommonInterval
    t N m M hN hm hmM]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hM : 1 ≤ M := hm.trans hmM
  have hab : 1 / m ≤ 2 * M / m := by
    rw [div_le_div_iff_of_pos_right hmPos]
    nlinarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact sourceKernel_integral_substitution hN hmPos hM

theorem integrable_positiveReflectedMellin
    {t N m M : ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (fun r : ℝ =>
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
          reflectionScalePhase (t - r) (m * N)) *
        (∫ v : ℝ in N..(2 * N * M),
          additivePhase (reflectionPhase (t - r) v) *
            reflectionAmplitude v)) := by
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have haPos : 0 < 1 / m := by positivity
  have hM : 1 ≤ M := hm.trans hmM
  have hab : 1 / m ≤ 2 * M / m := by
    rw [div_le_div_iff_of_pos_right hmPos]
    nlinarith
  have hprod := integrable_sectionThreeMellinFubiniKernel_Icc
    t (m * N) haPos hab
  have hrInt := hprod.integral_prod_right
  apply hrInt.congr
  filter_upwards with r
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact sourceKernel_integral_substitution hN hmPos hM

/-- Exact negative-frequency symmetry.  This is the clean source-faithful way
to retain the negative `m` branch: no sign is discarded, and the positive
reflection formula is applied to `-t` before conjugation. -/
theorem sectionThreeBaseIntegrand_neg_eq_conj
    (t xi u : ℝ) :
    sectionThreeBaseIntegrand t (-xi) u =
      starRingEnd ℂ (sectionThreeBaseIntegrand (-t) xi u) := by
  by_cases hu : u ∈ Set.Icc (1 : ℝ) 2
  · have huPos : 0 < u := by linarith [hu.1]
    unfold sectionThreeBaseIntegrand sectionThreeFourierPhase
      sectionThreeOscillatory sectionThreeCutoff
    rw [map_mul]
    have harg : (u : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg huPos.le]
      exact ne_of_lt Real.pi_pos
    have hpow := Complex.conj_cpow (u : ℂ)
      (Complex.I * (t : ℂ)) harg
    rw [Complex.conj_ofReal] at hpow
    have hpow' :
        (u : ℂ) ^ (Complex.I * (t : ℂ)) =
          starRingEnd ℂ
            ((u : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))) := by
      rw [hpow]
      congr 2
      simp
    rw [map_mul, map_pow, Complex.conj_ofReal, hpow']
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [sectionThreeBaseIntegrand_eq_zero_of_not_mem t (-xi) u hu,
      sectionThreeBaseIntegrand_eq_zero_of_not_mem (-t) xi u hu]
    simp

theorem sectionThreeFourierCoefficient_neg_eq_conj
    (t xi : ℝ) :
    sectionThreeFourierCoefficient t (-xi) =
      starRingEnd ℂ (sectionThreeFourierCoefficient (-t) xi) := by
  rw [sectionThreeFourierCoefficient_eq_integral,
    sectionThreeFourierCoefficient_eq_integral]
  change (∫ u : ℝ, sectionThreeBaseIntegrand t (-xi) u) = _
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  exact sectionThreeBaseIntegrand_neg_eq_conj t xi u

/-- Exact negative-frequency Lemma 6.2 formula, expressed as the conjugate of
the fully expanded positive reflected Mellin formula at `-t`. -/
theorem sectionThreeFourierCoefficient_eq_negativeReflectedMellin
    {t N m M : ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    sectionThreeFourierCoefficient t (-(m * N)) =
      starRingEnd ℂ
        (∫ r : ℝ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
              reflectionScalePhase (-t - r) (m * N)) *
            (∫ v : ℝ in N..(2 * N * M),
              additivePhase (reflectionPhase (-t - r) v) *
                reflectionAmplitude v)) := by
  rw [sectionThreeFourierCoefficient_neg_eq_conj]
  rw [sectionThreeFourierCoefficient_eq_positiveReflectedMellin hN hm hmM]

end

end GuthMaynardLemma62ReflectionSubstitution

#print axioms GuthMaynardLemma62ReflectionSubstitution.sectionThreeFourierCoefficient_eq_extendedIntegral
#print axioms GuthMaynardLemma62ReflectionSubstitution.sectionThreeFourierCoefficient_eq_sourceCommonInterval
#print axioms GuthMaynardLemma62ReflectionSubstitution.sectionThreeFourierCoefficient_eq_positiveReflectedMellin
#print axioms GuthMaynardLemma62ReflectionSubstitution.sectionThreeFourierCoefficient_eq_negativeReflectedMellin
