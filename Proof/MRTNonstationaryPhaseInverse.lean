import MRTNonstationaryPhaseTwoIBP

/-! Exact inverse first-phase-derivative multiplier for nonstationary phase. -/

namespace MAPMRTNonstationaryPhaseInverse

open MeasureTheory Set
open MAPMRTCorollary53Source

noncomputable section

def inversePhaseDerivative (p : ℝ → ℝ) (w : ℝ) : ℂ :=
  -(((1 / (2 * Real.pi * p w) : ℝ) : ℂ) * Complex.I)

def inversePhaseDerivativeDeriv (p p' : ℝ → ℝ) (w : ℝ) : ℂ :=
  (((p' w / (2 * Real.pi * p w ^ 2) : ℝ) : ℂ) * Complex.I)

def inversePhaseDerivativeSecond
    (p p' p'' : ℝ → ℝ) (w : ℝ) : ℂ :=
  ((((p'' w * p w - 2 * p' w ^ 2) /
      (2 * Real.pi * p w ^ 3) : ℝ) : ℂ) * Complex.I)

theorem hasDerivAt_inversePhaseDerivative
    {p p' : ℝ → ℝ} {w : ℝ} (hp0 : p w ≠ 0)
    (hp : HasDerivAt p (p' w) w) :
    HasDerivAt (inversePhaseDerivative p)
      (inversePhaseDerivativeDeriv p p' w) w := by
  have hden : 2 * Real.pi * p w ≠ 0 := mul_ne_zero (mul_ne_zero
    (by norm_num) Real.pi_ne_zero) hp0
  have hreal := (hasDerivAt_const w (1 : ℝ)).div
    (hp.const_mul (2 * Real.pi)) hden
  unfold inversePhaseDerivative inversePhaseDerivativeDeriv
  convert hreal.neg.ofReal_comp.mul_const Complex.I using 1
  · funext z
    simp only [Function.comp_apply, Pi.neg_apply, Pi.div_apply]
    push_cast
    ring
  · field_simp [hp0, Real.pi_ne_zero]
    ring

theorem hasDerivAt_inversePhaseDerivativeDeriv
    {p p' p'' : ℝ → ℝ} {w : ℝ} (hp0 : p w ≠ 0)
    (hp : HasDerivAt p (p' w) w)
    (hp' : HasDerivAt p' (p'' w) w) :
    HasDerivAt (inversePhaseDerivativeDeriv p p')
      (inversePhaseDerivativeSecond p p' p'' w) w := by
  have hnum : HasDerivAt p' (p'' w) w := hp'
  have hden : HasDerivAt (fun z ↦ 2 * Real.pi * p z ^ 2)
      (2 * Real.pi * (2 * p w * p' w)) w := by
    convert (hp.pow 2).const_mul (2 * Real.pi) using 1 <;> ring
  have hden0 : 2 * Real.pi * p w ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (pow_ne_zero 2 hp0)
  have hreal := hnum.div hden hden0
  unfold inversePhaseDerivativeDeriv inversePhaseDerivativeSecond
  convert hreal.ofReal_comp.mul_const Complex.I using 1
  field_simp [hp0, Real.pi_ne_zero]

theorem inversePhaseDerivative_mul_phaseDeriv
    {p : ℝ → ℝ} {E : ℝ → ℂ} {w : ℝ} (hp0 : p w ≠ 0) :
    inversePhaseDerivative p w *
        (((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w) = E w := by
  unfold inversePhaseDerivative
  push_cast
  field_simp [hp0, Real.pi_ne_zero]
  rw [Complex.I_sq]
  simp

theorem norm_inversePhaseDerivative_le
    {p : ℝ → ℝ} {w d : ℝ} (hd : 0 < d) (hlower : d ≤ |p w|) :
    ‖inversePhaseDerivative p w‖ ≤ 1 / d := by
  have hpabs : 0 < |p w| := lt_of_lt_of_le hd hlower
  unfold inversePhaseDerivative
  simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_div, abs_one, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hpden : |p w| ≤ 2 * Real.pi * |p w| := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (abs_nonneg (p w))]
  exact one_div_le_one_div_of_le hd (hlower.trans hpden)

theorem norm_inversePhaseDerivativeDeriv_le
    {p p' : ℝ → ℝ} {w d P1 : ℝ}
    (hd : 0 < d) (hP1 : 0 ≤ P1)
    (hlower : d ≤ |p w|) (hupper : |p' w| ≤ P1) :
    ‖inversePhaseDerivativeDeriv p p' w‖ ≤ P1 / d ^ 2 := by
  have hpabs : 0 < |p w| := lt_of_lt_of_le hd hlower
  unfold inversePhaseDerivativeDeriv
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  have hden : d ^ 2 ≤ 2 * Real.pi * |p w| ^ 2 := by
    have hpSq : d ^ 2 ≤ |p w| ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three, sq_nonneg (|p w|)]
  exact div_le_div₀ hP1 hupper (sq_pos_of_pos hd) hden

theorem norm_inversePhaseDerivativeSecond_le
    {p p' p'' : ℝ → ℝ} {w d P1 P2 : ℝ}
    (hd : 0 < d) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    (hlower : d ≤ |p w|)
    (hupper1 : |p' w| ≤ P1) (hupper2 : |p'' w| ≤ P2) :
    ‖inversePhaseDerivativeSecond p p' p'' w‖ ≤
      P2 / d ^ 2 + 2 * P1 ^ 2 / d ^ 3 := by
  have hpabs : 0 < |p w| := lt_of_lt_of_le hd hlower
  unfold inversePhaseDerivativeSecond
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  have hnum : |p'' w * p w - 2 * p' w ^ 2| ≤
      P2 * |p w| + 2 * P1 ^ 2 := by
    calc
      |p'' w * p w - 2 * p' w ^ 2| ≤
          |p'' w * p w| + |2 * p' w ^ 2| := abs_sub _ _ |>.trans_eq rfl
      _ = |p'' w| * |p w| + 2 * |p' w| ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow]
      _ ≤ P2 * |p w| + 2 * P1 ^ 2 := by
        gcongr
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    |p'' w * p w - 2 * p' w ^ 2| /
        (2 * Real.pi * |p w| ^ 3) ≤
        (P2 * |p w| + 2 * P1 ^ 2) / |p w| ^ 3 := by
      exact div_le_div₀
        (show 0 ≤ P2 * |p w| + 2 * P1 ^ 2 by positivity) hnum
        (show 0 < |p w| ^ 3 by positivity)
        (by simpa using (mul_le_mul_of_nonneg_right hpi
          (show 0 ≤ |p w| ^ 3 by positivity)))
    _ = P2 / |p w| ^ 2 + 2 * P1 ^ 2 / |p w| ^ 3 := by
      field_simp [ne_of_gt hpabs]
    _ ≤ P2 / d ^ 2 + 2 * P1 ^ 2 / d ^ 3 := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left hP2 (sq_pos_of_pos hd)
          (pow_le_pow_left₀ hd.le hlower 2)
      · exact div_le_div_of_nonneg_left (by positivity) (pow_pos hd 3)
          (pow_le_pow_left₀ hd.le hlower 3)

#print axioms hasDerivAt_inversePhaseDerivative
#print axioms hasDerivAt_inversePhaseDerivativeDeriv
#print axioms inversePhaseDerivative_mul_phaseDeriv
#print axioms norm_inversePhaseDerivativeSecond_le

end
end MAPMRTNonstationaryPhaseInverse
