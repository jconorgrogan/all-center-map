import MRTEquation77
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace MAPMRTVanDerCorputProof

open MeasureTheory Set
open MAPMRTCorollary53Source

noncomputable section

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase
      ((2 * Real.pi : ℂ) * Complex.I * additivePhase x) x := by
  unfold additivePhase
  refine (?_ : HasDerivAt
    (fun z : ℂ ↦ Complex.exp (2 * Real.pi * z * Complex.I)) _ (x : ℂ)).comp_ofReal
  convert (Complex.hasDerivAt_exp _).comp (x : ℂ)
    (hasDerivAt_id (x : ℂ) |>.const_mul ((2 * Real.pi : ℝ) : ℂ)
      |>.mul_const Complex.I) using 1
  · funext z
    simp only [Function.comp_apply, id_eq]
    congr 1
    push_cast
    ring
  · simp only [id_eq]
    push_cast
    ring

theorem hasDerivAt_additivePhase_comp
    {phase phase' : ℝ → ℝ} {x : ℝ}
    (h : HasDerivAt phase (phase' x) x) :
    HasDerivAt (fun y ↦ additivePhase (phase y))
      (((2 * Real.pi : ℂ) * Complex.I * (phase' x : ℂ)) *
        additivePhase (phase x)) x := by
  simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
    HasDerivAt.scomp x (hasDerivAt_additivePhase (phase x)) h

/-- Arctangent change of variables controlling the regularized inverse of a
monotone derivative. -/
theorem intervalIntegral_abs_deriv_div_sq_add_le
    {a b m : ℝ} {p p' : ℝ → ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hp : ∀ w ∈ Set.Icc a b, HasDerivAt p (p' w) w)
    (hint : IntervalIntegrable
      (fun w ↦ |p' w| / (p w ^ 2 + m ^ 2)) volume a b)
    (hsign : (∀ w ∈ Set.Icc a b, 0 ≤ p' w) ∨
      (∀ w ∈ Set.Icc a b, p' w ≤ 0)) :
    (∫ w : ℝ in a..b, |p' w| / (p w ^ 2 + m ^ 2)) ≤ Real.pi / m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hden : ∀ w, 0 < p w ^ 2 + m ^ 2 := by
    intro w
    nlinarith [sq_nonneg (p w), sq_pos_of_pos hm]
  have hantiDeriv : ∀ w ∈ Set.Icc a b,
      HasDerivAt (fun z ↦ Real.arctan (p z / m) / m)
        (p' w / (p w ^ 2 + m ^ 2)) w := by
    intro w hw
    convert ((hp w hw).div_const m).arctan.div_const m using 1
    field_simp
    ring
  rcases hsign with hpos | hneg
  · have hpoint : ∀ w ∈ Set.Icc a b,
        |p' w| / (p w ^ 2 + m ^ 2) = p' w / (p w ^ 2 + m ^ 2) := by
      intro w hw
      rw [abs_of_nonneg (hpos w hw)]
    have hint' : IntervalIntegrable
        (fun w ↦ p' w / (p w ^ 2 + m ^ 2)) volume a b := by
      apply hint.congr
      intro w hw
      exact hpoint w (by simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hw)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun w hw ↦ hantiDeriv w (by simpa [Set.uIcc_of_le hab] using hw)) hint'
    rw [intervalIntegral.integral_congr (fun w hw ↦ hpoint w
      (by simpa [Set.uIcc_of_le hab] using hw)), hftc]
    have haLow := Real.neg_pi_div_two_lt_arctan (p a / m)
    have hbHigh := Real.arctan_lt_pi_div_two (p b / m)
    have hdiff : Real.arctan (p b / m) - Real.arctan (p a / m) ≤ Real.pi := by
      linarith
    calc
      Real.arctan (p b / m) / m - Real.arctan (p a / m) / m =
          (Real.arctan (p b / m) - Real.arctan (p a / m)) / m := by ring
      _ ≤ Real.pi / m := div_le_div_of_nonneg_right hdiff hm.le

  · have hpoint : ∀ w ∈ Set.Icc a b,
        |p' w| / (p w ^ 2 + m ^ 2) =
          -(p' w / (p w ^ 2 + m ^ 2)) := by
      intro w hw
      rw [abs_of_nonpos (hneg w hw)]
      ring
    have hint' : IntervalIntegrable
        (fun w ↦ p' w / (p w ^ 2 + m ^ 2)) volume a b := by
      have := hint.neg
      apply this.congr
      intro w hw
      change -(|p' w| / (p w ^ 2 + m ^ 2)) = p' w / (p w ^ 2 + m ^ 2)
      rw [hpoint w (by simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hw)]
      ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun w hw ↦ hantiDeriv w (by simpa [Set.uIcc_of_le hab] using hw)) hint'
    rw [intervalIntegral.integral_congr (fun w hw ↦ hpoint w
      (by simpa [Set.uIcc_of_le hab] using hw)), intervalIntegral.integral_neg, hftc]
    have hbLow := Real.neg_pi_div_two_lt_arctan (p b / m)
    have haHigh := Real.arctan_lt_pi_div_two (p a / m)
    have hdiff : Real.arctan (p a / m) - Real.arctan (p b / m) ≤ Real.pi := by
      linarith
    calc
      -(Real.arctan (p b / m) / m - Real.arctan (p a / m) / m) =
          (Real.arctan (p a / m) - Real.arctan (p b / m)) / m := by ring
      _ ≤ Real.pi / m := div_le_div_of_nonneg_right hdiff hm.le

/-- Regularized reciprocal used to prove the second derivative estimate
without splitting at a stationary point. -/
def regularizedReciprocal (m : ℝ) (p : ℝ → ℝ) (w : ℝ) : ℂ :=
  -((p w / (2 * Real.pi * (p w ^ 2 + m ^ 2)) : ℝ) : ℂ) * Complex.I

def regularizedReciprocalDeriv
    (m : ℝ) (p p' : ℝ → ℝ) (w : ℝ) : ℂ :=
  -((p' w * (m ^ 2 - p w ^ 2) /
      (2 * Real.pi * (p w ^ 2 + m ^ 2) ^ 2) : ℝ) : ℂ) * Complex.I

def stationaryWeight (m : ℝ) (p : ℝ → ℝ) (w : ℝ) : ℝ :=
  m ^ 2 / (p w ^ 2 + m ^ 2)

theorem hasDerivAt_regularizedReciprocal
    {m : ℝ} (hm : 0 < m) {p p' : ℝ → ℝ} {w : ℝ}
    (hp : HasDerivAt p (p' w) w) :
    HasDerivAt (regularizedReciprocal m p)
      (regularizedReciprocalDeriv m p p' w) w := by
  have hdenPos : 0 < p w ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg (p w), sq_pos_of_pos hm]
  have hden : 2 * Real.pi * (p w ^ 2 + m ^ 2) ≠ 0 := by positivity
  have hdenDeriv : HasDerivAt
      (fun z ↦ 2 * Real.pi * (p z ^ 2 + m ^ 2))
      (2 * Real.pi * (2 * p w * p' w)) w := by
    convert ((hp.pow 2).add_const (m ^ 2)).const_mul (2 * Real.pi) using 1 <;> ring
  have hquot := hp.div hdenDeriv hden
  have hreal : HasDerivAt
      (fun z ↦ p z / (2 * Real.pi * (p z ^ 2 + m ^ 2)))
      (p' w * (m ^ 2 - p w ^ 2) /
        (2 * Real.pi * (p w ^ 2 + m ^ 2) ^ 2)) w := by
    convert hquot using 1
    field_simp
    ring
  unfold regularizedReciprocal regularizedReciprocalDeriv
  exact hreal.ofReal_comp.neg.mul_const Complex.I

theorem norm_regularizedReciprocal_le
    {m y : ℝ} (hm : 0 < m) :
    ‖-(((y / (2 * Real.pi * (y ^ 2 + m ^ 2)) : ℝ) : ℂ)) * Complex.I‖ ≤
      1 / m := by
  have hden : 0 < y ^ 2 + m ^ 2 := by nlinarith [sq_nonneg y, sq_pos_of_pos hm]
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  have htwo : 2 * |y| * m ≤ y ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg (|y| - m)]
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_div, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos,
    abs_of_pos hden]
  norm_num
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (mul_pos (by positivity : 0 < 2 * Real.pi) hden) hm).2
  nlinarith [Real.pi_gt_three, abs_nonneg y]

theorem norm_regularizedReciprocalDeriv_le
    {m y y' : ℝ} (hm : 0 < m) :
    ‖-(((y' * (m ^ 2 - y ^ 2) /
      (2 * Real.pi * (y ^ 2 + m ^ 2) ^ 2) : ℝ) : ℂ)) * Complex.I‖ ≤
      |y'| / (y ^ 2 + m ^ 2) := by
  have hden : 0 < y ^ 2 + m ^ 2 := by nlinarith [sq_nonneg y, sq_pos_of_pos hm]
  have habs : |m ^ 2 - y ^ 2| ≤ y ^ 2 + m ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg m]
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_div, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos, abs_pow,
    abs_of_pos hden]
  norm_num
  apply (div_le_iff₀
    (mul_pos (by positivity : 0 < 2 * Real.pi) (sq_pos_of_pos hden))).2
  have hnum : |y'| * |m ^ 2 - y ^ 2| ≤ |y'| * (y ^ 2 + m ^ 2) :=
    mul_le_mul_of_nonneg_left habs (abs_nonneg y')
  calc
    |y'| * |m ^ 2 - y ^ 2| ≤ |y'| * (y ^ 2 + m ^ 2) := hnum
    _ ≤ |y'| * (2 * Real.pi * (y ^ 2 + m ^ 2)) := by
      gcongr
      nlinarith [Real.pi_gt_three]
    _ = |y'| / (y ^ 2 + m ^ 2) *
        (2 * Real.pi * (y ^ 2 + m ^ 2) ^ 2) := by
      field_simp [hden.ne']
      <;> ring

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 := by
  simp [additivePhase, Complex.norm_exp]

theorem stationaryWeight_nonneg {m y : ℝ} (hm : 0 < m) :
    0 ≤ m ^ 2 / (y ^ 2 + m ^ 2) := by positivity

theorem stationaryWeight_add_regularized_identity
    {m y : ℝ} (hm : 0 < m) :
    ((m ^ 2 / (y ^ 2 + m ^ 2) : ℝ) : ℂ) +
      (-(((y / (2 * Real.pi * (y ^ 2 + m ^ 2)) : ℝ) : ℂ)) * Complex.I) *
        ((2 * Real.pi : ℂ) * Complex.I * (y : ℂ)) = 1 := by
  have hden : y ^ 2 + m ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg y, sq_pos_of_pos hm]
  ring_nf
  rw [Complex.I_sq]
  push_cast
  have hdenC : (m : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
    intro hz
    have hzre := congrArg Complex.re hz
    simp [pow_two, Complex.mul_re] at hzre
    nlinarith [sq_nonneg y, sq_pos_of_pos hm]
  field_simp [hdenC, Real.pi_ne_zero]
  ring

/-- The exact C¹ weighted second-derivative estimate needed for the stationary
packet.  Its `amplitude'` integral is the absolutely-continuous/BV budget.
The sign assumption records the monotonicity of `phase'`; in the MRT packet it
is immediate from `phase''(w)=βXe^w`. -/
theorem weightedSecondDerivativeVanDerCorputC1
    {a b m M : ℝ} {phase phase' phase'' : ℝ → ℝ}
    {amplitude amplitude' : ℝ → ℂ}
    (hab : a ≤ b) (hm : 0 < m) (hM : 0 ≤ M)
    (hphase : ∀ w ∈ Set.Icc a b, HasDerivAt phase (phase' w) w)
    (hphase' : ∀ w ∈ Set.Icc a b, HasDerivAt phase' (phase'' w) w)
    (hcurvature : ∀ w ∈ Set.Icc a b, m ^ 2 ≤ |phase'' w|)
    (hsign : (∀ w ∈ Set.Icc a b, 0 ≤ phase'' w) ∨
      (∀ w ∈ Set.Icc a b, phase'' w ≤ 0))
    (hamplitude : ∀ w ∈ Set.Icc a b,
      HasDerivAt amplitude (amplitude' w) w)
    (hphase''Cont : ContinuousOn phase'' (Set.Icc a b))
    (hamplitude'Cont : ContinuousOn amplitude' (Set.Icc a b))
    (hamplitudeBound : ∀ w ∈ Set.Icc a b, ‖amplitude w‖ ≤ M) :
    ‖∫ w : ℝ in a..b, additivePhase (phase w) * amplitude w‖ ≤
      10 * (M + ∫ w : ℝ in a..b, ‖amplitude' w‖) / m := by
  let E : ℝ → ℂ := fun w ↦ additivePhase (phase w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (phase' w : ℂ)) * E w
  let q : ℝ → ℂ := regularizedReciprocal m phase'
  let qd : ℝ → ℂ := regularizedReciprocalDeriv m phase' phase''
  let s : ℝ → ℝ := stationaryWeight m phase'
  let u : ℝ → ℂ := fun w ↦ amplitude w * q w
  let ud : ℝ → ℂ := fun w ↦ amplitude' w * q w + amplitude w * qd w
  have hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w := by
    intro w hw
    exact hasDerivAt_additivePhase_comp (hphase w hw)
  have hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w := by
    intro w hw
    exact hasDerivAt_regularizedReciprocal hm (hphase' w hw)
  have hu : ∀ w ∈ Set.Icc a b, HasDerivAt u (ud w) w := by
    intro w hw
    exact (hamplitude w hw).mul (hq w hw)
  have hphaseCont : ContinuousOn phase (Set.Icc a b) :=
    fun w hw ↦ (hphase w hw).continuousAt.continuousWithinAt
  have hphase'Cont : ContinuousOn phase' (Set.Icc a b) :=
    fun w hw ↦ (hphase' w hw).continuousAt.continuousWithinAt
  have hamplitudeCont : ContinuousOn amplitude (Set.Icc a b) :=
    fun w hw ↦ (hamplitude w hw).continuousAt.continuousWithinAt
  have hECont : ContinuousOn E (Set.Icc a b) := by
    exact fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
  have hEdCont : ContinuousOn Ed (Set.Icc a b) := by
    unfold Ed
    exact ((continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn hphase'Cont)).mul hECont
  have hqCont : ContinuousOn q (Set.Icc a b) :=
    fun w hw ↦ (hq w hw).continuousAt.continuousWithinAt
  have hqdCont : ContinuousOn qd (Set.Icc a b) := by
    unfold qd regularizedReciprocalDeriv
    apply ContinuousOn.mul
    · apply ContinuousOn.neg
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro w hw
        have hden : 0 < phase' w ^ 2 + m ^ 2 := by
          nlinarith [sq_nonneg (phase' w), sq_pos_of_pos hm]
        positivity
    · exact continuousOn_const
  have hsCont : ContinuousOn s (Set.Icc a b) := by
    unfold s stationaryWeight
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro w hw
      have : 0 < phase' w ^ 2 + m ^ 2 := by
        nlinarith [sq_nonneg (phase' w), sq_pos_of_pos hm]
      exact this.ne'
  have huCont : ContinuousOn u (Set.Icc a b) := hamplitudeCont.mul hqCont
  have hudCont : ContinuousOn ud (Set.Icc a b) :=
    (hamplitude'Cont.mul hqCont).add (hamplitudeCont.mul hqdCont)
  have hiEd : IntervalIntegrable Ed volume a b := by
    have hc : ContinuousOn Ed (Set.uIcc a b) := by
      simpa [Set.uIcc_of_le hab] using hEdCont
    exact hc.intervalIntegrable
  have hiud : IntervalIntegrable ud volume a b := by
    have hc : ContinuousOn ud (Set.uIcc a b) := by
      simpa [Set.uIcc_of_le hab] using hudCont
    exact hc.intervalIntegrable
  have hiAbsPhase : IntervalIntegrable
      (fun w ↦ |phase'' w| / (phase' w ^ 2 + m ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using
      hphase''Cont.abs.div
        ((hphase'Cont.pow 2).add continuousOn_const)
        (fun w hw ↦ by
          have : 0 < phase' w ^ 2 + m ^ 2 := by
            nlinarith [sq_nonneg (phase' w), sq_pos_of_pos hm]
          exact this.ne')
  have harctan := intervalIntegral_abs_deriv_div_sq_add_le hab hm hphase'
    hiAbsPhase hsign
  have hdecomp : ∀ w ∈ Set.Icc a b,
      E w * amplitude w =
        ((s w : ℝ) : ℂ) * E w * amplitude w + u w * Ed w := by
    intro w hw
    have hid := stationaryWeight_add_regularized_identity
      (m := m) (y := phase' w) hm
    unfold s stationaryWeight u q regularizedReciprocal Ed
    rw [← one_mul (E w * amplitude w), ← hid, add_mul]
    congr 1 <;> ac_rfl
  have hibp : (∫ w : ℝ in a..b, u w * Ed w) =
      u b * E b - u a * E a - ∫ w : ℝ in a..b, ud w * E w := by
    have hu' : ∀ w ∈ Set.uIcc a b, HasDerivAt u (ud w) w := by
      simpa [Set.uIcc_of_le hab] using hu
    have hE' : ∀ w ∈ Set.uIcc a b, HasDerivAt E (Ed w) w := by
      simpa [Set.uIcc_of_le hab] using hE
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu' hE' hiud hiEd
  have hiAmplitudePrime : IntervalIntegrable amplitude' volume a b := by
    have hc : ContinuousOn amplitude' (Set.uIcc a b) := by
      simpa [Set.uIcc_of_le hab] using hamplitude'Cont
    exact hc.intervalIntegrable
  have hiNormAmplitudePrime : IntervalIntegrable
      (fun w ↦ ‖amplitude' w‖) volume a b := hiAmplitudePrime.norm
  have hvariationNonneg : 0 ≤ ∫ w : ℝ in a..b, ‖amplitude' w‖ :=
    intervalIntegral.integral_nonneg hab (fun w hw ↦ norm_nonneg _)
  have hiStationary : IntervalIntegrable
      (fun w ↦ ((s w : ℝ) : ℂ) * E w * amplitude w) volume a b := by
    have hc : ContinuousOn
        (fun w ↦ ((s w : ℝ) : ℂ) * E w * amplitude w)
        (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact (Complex.continuous_ofReal.comp_continuousOn hsCont).mul hECont |>.mul
        hamplitudeCont
    exact hc.intervalIntegrable
  have hiOscillatory : IntervalIntegrable (fun w ↦ u w * Ed w) volume a b := by
    have hc : ContinuousOn (fun w ↦ u w * Ed w) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact huCont.mul hEdCont
    exact hc.intervalIntegrable
  have hIntegralDecomp :
      (∫ w : ℝ in a..b, E w * amplitude w) =
        (∫ w : ℝ in a..b, ((s w : ℝ) : ℂ) * E w * amplitude w) +
        ∫ w : ℝ in a..b, u w * Ed w := by
    rw [intervalIntegral.integral_congr (fun w hw ↦ hdecomp w
      (by simpa [Set.uIcc_of_le hab] using hw))]
    exact intervalIntegral.integral_add hiStationary hiOscillatory
  have hstationaryPoint : ∀ w ∈ Set.Icc a b,
      ‖((s w : ℝ) : ℂ) * E w * amplitude w‖ ≤
        M * (|phase'' w| / (phase' w ^ 2 + m ^ 2)) := by
    intro w hw
    have hden : 0 < phase' w ^ 2 + m ^ 2 := by
      nlinarith [sq_nonneg (phase' w), sq_pos_of_pos hm]
    have hsNonneg : 0 ≤ s w := by
      exact stationaryWeight_nonneg (m := m) (y := phase' w) hm
    have hsBound : s w ≤ |phase'' w| / (phase' w ^ 2 + m ^ 2) := by
      unfold s stationaryWeight
      exact div_le_div_of_nonneg_right (hcurvature w hw) hden.le
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsNonneg, norm_additivePhase, mul_one]
    have hmul := mul_le_mul hsBound (hamplitudeBound w hw)
      (norm_nonneg (amplitude w))
      (div_nonneg (abs_nonneg _) hden.le)
    simpa [mul_comm] using hmul
  have hiStationaryNorm : IntervalIntegrable
      (fun w ↦ ‖((s w : ℝ) : ℂ) * E w * amplitude w‖) volume a b :=
    hiStationary.norm
  have hiPhaseMajorant : IntervalIntegrable
      (fun w ↦ M * (|phase'' w| / (phase' w ^ 2 + m ^ 2))) volume a b :=
    hiAbsPhase.const_mul M
  have hstationaryIntegral :
      ‖∫ w : ℝ in a..b, ((s w : ℝ) : ℂ) * E w * amplitude w‖ ≤
        M * (Real.pi / m) := by
    calc
      ‖∫ w : ℝ in a..b, ((s w : ℝ) : ℂ) * E w * amplitude w‖ ≤
          ∫ w : ℝ in a..b, ‖((s w : ℝ) : ℂ) * E w * amplitude w‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ w : ℝ in a..b,
          M * (|phase'' w| / (phase' w ^ 2 + m ^ 2)) :=
        intervalIntegral.integral_mono_on hab hiStationaryNorm hiPhaseMajorant
          hstationaryPoint
      _ = M * ∫ w : ℝ in a..b,
          |phase'' w| / (phase' w ^ 2 + m ^ 2) := by
        exact intervalIntegral.integral_const_mul M _
      _ ≤ M * (Real.pi / m) := mul_le_mul_of_nonneg_left harctan hM
  have hudPoint : ∀ w ∈ Set.Icc a b,
      ‖ud w * E w‖ ≤ ‖amplitude' w‖ / m +
        M * (|phase'' w| / (phase' w ^ 2 + m ^ 2)) := by
    intro w hw
    have hqBound : ‖q w‖ ≤ 1 / m := by
      exact norm_regularizedReciprocal_le (m := m) (y := phase' w) hm
    have hqdBound : ‖qd w‖ ≤
        |phase'' w| / (phase' w ^ 2 + m ^ 2) := by
      exact norm_regularizedReciprocalDeriv_le
        (m := m) (y := phase' w) (y' := phase'' w) hm
    calc
      ‖ud w * E w‖ ≤ ‖ud w‖ * ‖E w‖ := norm_mul_le _ _
      _ = ‖ud w‖ := by rw [norm_additivePhase]; simp
      _ ≤ ‖amplitude' w * q w‖ + ‖amplitude w * qd w‖ := norm_add_le _ _
      _ ≤ (‖amplitude' w‖ * (1 / m)) +
          (M * (|phase'' w| / (phase' w ^ 2 + m ^ 2))) := by
        apply add_le_add
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left hqBound (norm_nonneg _))
        · exact (norm_mul_le _ _).trans
            (mul_le_mul (hamplitudeBound w hw) hqdBound
              (norm_nonneg _) hM)
      _ = ‖amplitude' w‖ / m +
          M * (|phase'' w| / (phase' w ^ 2 + m ^ 2)) := by
        simp [div_eq_mul_inv]
  have hiUdE : IntervalIntegrable (fun w ↦ ud w * E w) volume a b :=
    hiud.mul_continuousOn (by
      simpa [Set.uIcc_of_le hab] using hECont)
  have hiUdENorm : IntervalIntegrable (fun w ↦ ‖ud w * E w‖) volume a b :=
    hiUdE.norm
  have hiUdMajorant : IntervalIntegrable
      (fun w ↦ ‖amplitude' w‖ / m +
        M * (|phase'' w| / (phase' w ^ 2 + m ^ 2))) volume a b :=
    (hiNormAmplitudePrime.div_const m).add (hiAbsPhase.const_mul M)
  have hudIntegral : ‖∫ w : ℝ in a..b, ud w * E w‖ ≤
      (∫ w : ℝ in a..b, ‖amplitude' w‖) / m + M * (Real.pi / m) := by
    calc
      ‖∫ w : ℝ in a..b, ud w * E w‖ ≤
          ∫ w : ℝ in a..b, ‖ud w * E w‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ w : ℝ in a..b, (‖amplitude' w‖ / m +
          M * (|phase'' w| / (phase' w ^ 2 + m ^ 2))) :=
        intervalIntegral.integral_mono_on hab hiUdENorm hiUdMajorant hudPoint
      _ = (∫ w : ℝ in a..b, ‖amplitude' w‖) / m +
          M * ∫ w : ℝ in a..b,
            |phase'' w| / (phase' w ^ 2 + m ^ 2) := by
        rw [intervalIntegral.integral_add (hiNormAmplitudePrime.div_const m)
          (hiAbsPhase.const_mul M), intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul]
      _ ≤ (∫ w : ℝ in a..b, ‖amplitude' w‖) / m +
          M * (Real.pi / m) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left harctan hM)
  have hendpoint : ∀ w ∈ Set.Icc a b, ‖u w * E w‖ ≤ M / m := by
    intro w hw
    have hqBound : ‖q w‖ ≤ 1 / m :=
      norm_regularizedReciprocal_le (m := m) (y := phase' w) hm
    calc
      ‖u w * E w‖ ≤ ‖u w‖ * ‖E w‖ := norm_mul_le _ _
      _ = ‖u w‖ := by rw [norm_additivePhase]; simp
      _ ≤ ‖amplitude w‖ * ‖q w‖ := norm_mul_le _ _
      _ ≤ M * (1 / m) := mul_le_mul (hamplitudeBound w hw) hqBound
        (norm_nonneg _) hM
      _ = M / m := by simp [div_eq_mul_inv]
  have hoscillatoryIntegral : ‖∫ w : ℝ in a..b, u w * Ed w‖ ≤
      2 * (M / m) +
        ((∫ w : ℝ in a..b, ‖amplitude' w‖) / m + M * (Real.pi / m)) := by
    rw [hibp]
    have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
    have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    calc
      ‖u b * E b - u a * E a - ∫ w : ℝ in a..b, ud w * E w‖ ≤
          ‖u b * E b - u a * E a‖ + ‖∫ w : ℝ in a..b, ud w * E w‖ :=
        norm_sub_le _ _
      _ ≤ (‖u b * E b‖ + ‖u a * E a‖) +
          ‖∫ w : ℝ in a..b, ud w * E w‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (M / m + M / m) +
          ((∫ w : ℝ in a..b, ‖amplitude' w‖) / m + M * (Real.pi / m)) :=
        add_le_add (add_le_add (hendpoint b hbmem) (hendpoint a hamem)) hudIntegral
      _ = 2 * (M / m) +
          ((∫ w : ℝ in a..b, ‖amplitude' w‖) / m + M * (Real.pi / m)) := by ring
  change ‖∫ w : ℝ in a..b, E w * amplitude w‖ ≤ _
  rw [hIntegralDecomp]
  calc
    ‖(∫ w : ℝ in a..b, ((s w : ℝ) : ℂ) * E w * amplitude w) +
        ∫ w : ℝ in a..b, u w * Ed w‖ ≤
        ‖∫ w : ℝ in a..b, ((s w : ℝ) : ℂ) * E w * amplitude w‖ +
        ‖∫ w : ℝ in a..b, u w * Ed w‖ := norm_add_le _ _
    _ ≤ M * (Real.pi / m) +
        (2 * (M / m) +
          ((∫ w : ℝ in a..b, ‖amplitude' w‖) / m + M * (Real.pi / m))) :=
      add_le_add hstationaryIntegral hoscillatoryIntegral
    _ ≤ 10 * (M + ∫ w : ℝ in a..b, ‖amplitude' w‖) / m := by
      simp only [div_eq_mul_inv]
      have hinv : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
      have hcoefficient : 2 * Real.pi + 2 ≤ 10 := by
        nlinarith [Real.pi_lt_four]
      have hMcoefficient : (2 * Real.pi + 2) * M ≤ 10 * M :=
        mul_le_mul_of_nonneg_right hcoefficient hM
      have hMscaled : ((2 * Real.pi + 2) * M) * m⁻¹ ≤ (10 * M) * m⁻¹ :=
        mul_le_mul_of_nonneg_right hMcoefficient hinv
      have hVten : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤
          10 * (∫ w : ℝ in a..b, ‖amplitude' w‖) := by
        nlinarith
      have hVscaled : (∫ w : ℝ in a..b, ‖amplitude' w‖) * m⁻¹ ≤
          (10 * (∫ w : ℝ in a..b, ‖amplitude' w‖)) * m⁻¹ :=
        mul_le_mul_of_nonneg_right hVten hinv
      calc
        M * (Real.pi * m⁻¹) +
            (2 * (M * m⁻¹) +
              ((∫ w : ℝ in a..b, ‖amplitude' w‖) * m⁻¹ +
                M * (Real.pi * m⁻¹))) =
            ((2 * Real.pi + 2) * M) * m⁻¹ +
              (∫ w : ℝ in a..b, ‖amplitude' w‖) * m⁻¹ := by ring
        _ ≤ (10 * M) * m⁻¹ +
            (10 * (∫ w : ℝ in a..b, ‖amplitude' w‖)) * m⁻¹ :=
          add_le_add hMscaled hVscaled
        _ = 10 * (M + ∫ w : ℝ in a..b, ‖amplitude' w‖) * m⁻¹ := by ring

end
end MAPMRTVanDerCorputProof

#print axioms MAPMRTVanDerCorputProof.intervalIntegral_abs_deriv_div_sq_add_le
#print axioms MAPMRTVanDerCorputProof.weightedSecondDerivativeVanDerCorputC1
