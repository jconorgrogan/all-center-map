import MRTSourceWholeLineExtension
import MRTOffDiagonalTwoIBP
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Source-faithful whole-line cutoff autocorrelation

MRT extend the `x`-energy to the whole real line before Cauchy--Schwarz.
Opening the two packets then produces the translated cutoff autocorrelation

`phi₂(delta) = ∫_{-1}^{1} phi(y) phi(y + delta) dy`.

The common translation is the key point: with
`delta(w,h) = (X exp w - X exp (w+h))/H`, one has
`delta' = delta'' = delta`.  Thus, on the overlap support `|delta| ≤ 2`,
the first two `w` derivatives cost only fixed cutoff constants.  There is no
`X/H` boundary derivative.
-/

namespace MAPMRTWholeLineCutoffAutocorrelation

open MeasureTheory Set

noncomputable section

/-- The literal `phi₂` in MRT p.50, restricted to the support of its first
factor.  For a cutoff supported on `[-1,1]` this equals the full-line
integral. -/
def wholeLineCutoffAutocorrelation (cutoff : ℝ → ℝ) (delta : ℝ) : ℝ :=
  ∫ y : ℝ in (-1)..1, cutoff y * cutoff (y + delta)

/-- The first translated derivative of `phi₂`. -/
def wholeLineCutoffAutocorrelationDeriv
    (cutoff cutoff' : ℝ → ℝ) (delta : ℝ) : ℝ :=
  ∫ y : ℝ in (-1)..1, cutoff y * cutoff' (y + delta)

/-- The second translated derivative of `phi₂`. -/
def wholeLineCutoffAutocorrelationSecond
    (cutoff cutoff'' : ℝ → ℝ) (delta : ℝ) : ℝ :=
  ∫ y : ℝ in (-1)..1, cutoff y * cutoff'' (y + delta)

/-- The source displacement after `w' = w+h`.  The sign agrees with the
displayed argument `X e^w-X e^{w'}` on MRT p.50. -/
def wholeLinePacketShift (X H h w : ℝ) : ℝ :=
  (X * Real.exp w - X * Real.exp (w + h)) / H

theorem hasDerivAt_wholeLinePacketShift
    {X H h w : ℝ} :
    HasDerivAt (wholeLinePacketShift X H h)
      (wholeLinePacketShift X H h w) w := by
  unfold wholeLinePacketShift
  convert (((Real.hasDerivAt_exp w).const_mul X).sub
    (((Real.hasDerivAt_exp (w + h)).scomp w
      ((hasDerivAt_id w).add_const h)).const_mul X)).div_const H using 1 <;>
    (try funext y) <;> simp only [Function.comp_def, Pi.sub_apply, id_eq, smul_eq_mul] <;> ring

theorem hasDerivAt_wholeLineCutoffAutocorrelation
    {cutoff cutoff' : ℝ → ℝ} {B1 delta : ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y) :
    HasDerivAt (wholeLineCutoffAutocorrelation cutoff)
      (wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta) delta := by
  unfold wholeLineCutoffAutocorrelation wholeLineCutoffAutocorrelationDeriv
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y : ℝ ↦ cutoff y * cutoff (y + z))
    (F' := fun z y : ℝ ↦ cutoff y * cutoff' (y + z))
    (bound := fun _y : ℝ ↦ B1)
    (s := Set.univ) (x₀ := delta) (a := (-1 : ℝ)) (b := 1)
    Filter.univ_mem ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · exact Filter.Eventually.of_forall fun z ↦ by
      have hc : Continuous (fun y : ℝ ↦ cutoff y * cutoff (y + z)) := by
        fun_prop
      exact hc.aestronglyMeasurable.restrict
  · have hc : Continuous (fun y : ℝ ↦ cutoff y * cutoff (y + delta)) := by
      fun_prop
    exact hc.intervalIntegrable _ _
  · have hc : Continuous (fun y : ℝ ↦ cutoff y * cutoff' (y + delta)) := by
      fun_prop
    exact hc.aestronglyMeasurable.restrict
  · exact ae_of_all _ fun y _hy z _hz ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |cutoff y| * |cutoff' (y + z)| ≤ 1 * B1 := by
          gcongr
          · exact hcutoffBound y
          · exact hcutoff'Bound (y + z)
        _ = B1 := one_mul _
  · exact ae_of_all _ fun y _hy z _hz ↦ by
      convert (hasDerivAt_const z (cutoff y)).mul
        ((hcutoffDeriv (y + z)).scomp z
          ((hasDerivAt_const z y).add (hasDerivAt_id z))) using 1 <;>
        (try funext v) <;> simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply, id_eq, smul_eq_mul] <;> ring

theorem hasDerivAt_wholeLineCutoffAutocorrelationDeriv
    {cutoff cutoff' cutoff'' : ℝ → ℝ} {B2 delta : ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoff''Cont : Continuous cutoff'')
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ B2)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y) :
    HasDerivAt (wholeLineCutoffAutocorrelationDeriv cutoff cutoff')
      (wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta) delta := by
  unfold wholeLineCutoffAutocorrelationDeriv wholeLineCutoffAutocorrelationSecond
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y : ℝ ↦ cutoff y * cutoff' (y + z))
    (F' := fun z y : ℝ ↦ cutoff y * cutoff'' (y + z))
    (bound := fun _y : ℝ ↦ B2)
    (s := Set.univ) (x₀ := delta) (a := (-1 : ℝ)) (b := 1)
    Filter.univ_mem ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · exact Filter.Eventually.of_forall fun z ↦ by
      have hc : Continuous (fun y : ℝ ↦ cutoff y * cutoff' (y + z)) := by
        fun_prop
      exact hc.aestronglyMeasurable.restrict
  · have hc : Continuous (fun y : ℝ ↦ cutoff y * cutoff' (y + delta)) := by
      fun_prop
    exact hc.intervalIntegrable _ _
  · have hc : Continuous (fun y : ℝ ↦ cutoff y * cutoff'' (y + delta)) := by
      fun_prop
    exact hc.aestronglyMeasurable.restrict
  · exact ae_of_all _ fun y _hy z _hz ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |cutoff y| * |cutoff'' (y + z)| ≤ 1 * B2 := by
          gcongr
          · exact hcutoffBound y
          · exact hcutoff''Bound (y + z)
        _ = B2 := one_mul _
  · exact ae_of_all _ fun y _hy z _hz ↦ by
      convert (hasDerivAt_const z (cutoff y)).mul
        ((hcutoffSecond (y + z)).scomp z
          ((hasDerivAt_const z y).add (hasDerivAt_id z))) using 1 <;>
        (try funext v) <;> simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply, id_eq, smul_eq_mul] <;> ring

/-! ## Exact whole-line change of variables -/

private theorem cutoff_eq_zero_of_not_mem_Ioc
    {cutoff : ℝ → ℝ} (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    {y : ℝ} (hy : y ∉ Set.Ioc (-1 : ℝ) 1) : cutoff y = 0 := by
  apply hcutoffSupport
  simp only [Set.mem_Ioc, not_and_or, not_lt] at hy
  rcases hy with hy | hy
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    exact (not_le.mp hy).le

theorem integral_cutoffPair_eq_wholeLineCutoffAutocorrelation
    {X0 X1 H : ℝ} {cutoff : ℝ → ℝ}
    (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    (∫ x : ℝ, cutoff ((X0 - x) / H) * cutoff ((X1 - x) / H)) =
      H * wholeLineCutoffAutocorrelation cutoff ((X1 - X0) / H) := by
  let delta : ℝ := (X1 - X0) / H
  let G : ℝ → ℝ := fun y ↦ cutoff y * cutoff (y + delta)
  have hpoint : ∀ x : ℝ,
      cutoff ((X0 - x) / H) * cutoff ((X1 - x) / H) =
        G ((X0 - x) / H) := by
    intro x
    unfold G delta
    congr 2
    field_simp [ne_of_gt hH]
    ring
  have htranslate :
      (∫ x : ℝ, G ((X0 - x) / H)) = ∫ x : ℝ, G (-x / H) := by
    let f : ℝ → ℝ := fun x ↦ G (-x / H)
    have h := MeasureTheory.integral_add_right_eq_self (μ := volume) f (-X0)
    have hfg : ∀ x : ℝ, f (x + -X0) = G ((X0 - x) / H) := by
      intro x
      unfold f
      congr 1
      ring
    rw [show (fun x : ℝ ↦ G ((X0 - x) / H)) =
        (fun x : ℝ ↦ f (x + -X0)) by funext x; exact (hfg x).symm]
    exact h
  have hscale : (∫ x : ℝ, G (-x / H)) = H * ∫ y : ℝ, G y := by
    have hmul := Measure.integral_comp_mul_left G (-1 / H)
    have hfun : (fun x : ℝ ↦ G (-x / H)) = fun x : ℝ ↦ G ((-1 / H) * x) := by
      funext x
      congr 1
      ring
    rw [hfun, hmul]
    simp only [inv_div]
    rw [show H / -1 = -H by ring, abs_neg, abs_of_pos hH]
    rfl
  have hrestrict : (∫ y : ℝ, G y) =
      ∫ y : ℝ in (-1)..1, cutoff y * cutoff (y + delta) := by
    have hG : G = Set.indicator (Set.Ioc (-1 : ℝ) 1) G := by
      funext y
      by_cases hy : y ∈ Set.Ioc (-1 : ℝ) 1
      · simp [hy]
      · have hz := cutoff_eq_zero_of_not_mem_Ioc hcutoffSupport hy
        simp [G, hy, hz]
    rw [hG, MeasureTheory.integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), htranslate,
    hscale, hrestrict]
  rfl

/-! ## Fixed support and scalar correlation bounds -/

private theorem one_le_abs_or_one_le_abs_add_of_two_lt_abs
    {y delta : ℝ} (hdelta : 2 < |delta|) :
    1 ≤ |y| ∨ 1 ≤ |y + delta| := by
  by_contra h
  push_neg at h
  have htri : |delta| ≤ |y + delta| + |y| := by
    calc
      |delta| = |(y + delta) - y| := by congr 1 <;> ring
      _ ≤ |y + delta| + |y| := abs_sub _ _
  linarith

theorem wholeLineCutoffAutocorrelation_eq_zero_of_two_lt_abs
    {cutoff : ℝ → ℝ} {delta : ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hdelta : 2 < |delta|) :
    wholeLineCutoffAutocorrelation cutoff delta = 0 := by
  unfold wholeLineCutoffAutocorrelation
  rw [show (∫ y : ℝ in (-1)..1, cutoff y * cutoff (y + delta)) =
      ∫ _y : ℝ in (-1)..1, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro y _hy
    change cutoff y * cutoff (y + delta) = 0
    rcases one_le_abs_or_one_le_abs_add_of_two_lt_abs hdelta with hy | hyd
    · rw [hcutoffSupport y hy, zero_mul]
    · rw [hcutoffSupport (y + delta) hyd, mul_zero]]
  simp

theorem wholeLineCutoffAutocorrelationDeriv_eq_zero_of_two_lt_abs
    {cutoff cutoff' : ℝ → ℝ} {delta : ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hdelta : 2 < |delta|) :
    wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta = 0 := by
  unfold wholeLineCutoffAutocorrelationDeriv
  rw [show (∫ y : ℝ in (-1)..1, cutoff y * cutoff' (y + delta)) =
      ∫ _y : ℝ in (-1)..1, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro y _hy
    change cutoff y * cutoff' (y + delta) = 0
    rcases one_le_abs_or_one_le_abs_add_of_two_lt_abs hdelta with hy | hyd
    · rw [hcutoffSupport y hy, zero_mul]
    · rw [hcutoff'Support (y + delta) hyd, mul_zero]]
  simp

theorem wholeLineCutoffAutocorrelationSecond_eq_zero_of_two_lt_abs
    {cutoff cutoff'' : ℝ → ℝ} {delta : ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hdelta : 2 < |delta|) :
    wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta = 0 := by
  unfold wholeLineCutoffAutocorrelationSecond
  rw [show (∫ y : ℝ in (-1)..1, cutoff y * cutoff'' (y + delta)) =
      ∫ _y : ℝ in (-1)..1, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro y _hy
    change cutoff y * cutoff'' (y + delta) = 0
    rcases one_le_abs_or_one_le_abs_add_of_two_lt_abs hdelta with hy | hyd
    · rw [hcutoffSupport y hy, zero_mul]
    · rw [hcutoff''Support (y + delta) hyd, mul_zero]]
  simp

private theorem abs_interval_cutoffProduct_le
    {f g : ℝ → ℝ} {B delta : ℝ}
    (hf : ∀ y, |f y| ≤ 1) (hg : ∀ y, |g y| ≤ B) :
    |∫ y : ℝ in (-1)..1, f y * g (y + delta)| ≤ 2 * B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1) (C := B)
    (f := fun y : ℝ ↦ f y * g (y + delta)) (by
      intro y _hy
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |f y| * |g (y + delta)| ≤ 1 * B := by
          gcongr
          · exact hf y
          · exact hg (y + delta)
        _ = B := one_mul B)
  have hab : |(1 : ℝ) - (-1)| = 2 := by norm_num
  rw [Real.norm_eq_abs, hab, mul_comm] at h
  exact h

theorem abs_wholeLineCutoffAutocorrelation_le_two
    {cutoff : ℝ → ℝ} {delta : ℝ}
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1) :
    |wholeLineCutoffAutocorrelation cutoff delta| ≤ 2 := by
  simpa [wholeLineCutoffAutocorrelation] using
    (abs_interval_cutoffProduct_le (delta := delta)
      hcutoffBound hcutoffBound)

theorem abs_wholeLineCutoffAutocorrelationDeriv_le
    {cutoff cutoff' : ℝ → ℝ} {B1 delta : ℝ}
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1) :
    |wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta| ≤ 2 * B1 := by
  simpa [wholeLineCutoffAutocorrelationDeriv] using
    (abs_interval_cutoffProduct_le (delta := delta)
      hcutoffBound hcutoff'Bound)

theorem abs_wholeLineCutoffAutocorrelationSecond_le
    {cutoff cutoff'' : ℝ → ℝ} {B2 delta : ℝ}
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ B2) :
    |wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta| ≤ 2 * B2 := by
  simpa [wholeLineCutoffAutocorrelationSecond] using
    (abs_interval_cutoffProduct_le (delta := delta)
      hcutoffBound hcutoff''Bound)

#print axioms hasDerivAt_wholeLinePacketShift
#print axioms hasDerivAt_wholeLineCutoffAutocorrelation
#print axioms hasDerivAt_wholeLineCutoffAutocorrelationDeriv
#print axioms integral_cutoffPair_eq_wholeLineCutoffAutocorrelation
#print axioms wholeLineCutoffAutocorrelation_eq_zero_of_two_lt_abs
#print axioms abs_wholeLineCutoffAutocorrelationSecond_le

end
end MAPMRTWholeLineCutoffAutocorrelation
