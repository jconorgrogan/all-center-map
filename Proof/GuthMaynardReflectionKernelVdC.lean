import MRTVanDerCorputCore

/-!
# The stationary-phase kernel in Guth--Maynard Lemma 6.2

This file certifies the genuinely oscillatory step on pp. 19--20 of
Guth--Maynard.  On each dyadic interval `[V,2V]`, the kernel appearing after
Mellin inversion and the change of variables `v = Nmu` is

`v⁻¹ exp(2πi ((τ/(2π)) log v - v))`.

The paper invokes the first/second derivative van der Corput bounds.  We
specialize the already proved weighted second-derivative theorem to this
literal phase and amplitude.  The result is the required `τ⁻¹/2` saving,
with an explicit constant.  No approximate-functional-equation proposition
is assumed here.
-/

namespace GuthMaynardReflectionKernelVdC

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPMRTVanDerCorputProof
open scoped BigOperators

noncomputable section

def reflectionPhase (τ v : ℝ) : ℝ :=
  τ / (2 * Real.pi) * Real.log v - v

def reflectionPhaseDeriv (τ v : ℝ) : ℝ :=
  τ / (2 * Real.pi * v) - 1

def reflectionPhaseSecond (τ v : ℝ) : ℝ :=
  -τ / (2 * Real.pi * v ^ 2)

def reflectionAmplitude (v : ℝ) : ℂ :=
  (v⁻¹ : ℝ)

def reflectionAmplitudeDeriv (v : ℝ) : ℂ :=
  (-(v ^ 2)⁻¹ : ℝ)

theorem hasDerivAt_reflectionPhase
    {τ v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (reflectionPhase τ) (reflectionPhaseDeriv τ v) v := by
  unfold reflectionPhase reflectionPhaseDeriv
  convert (Real.hasDerivAt_log hv).const_mul (τ / (2 * Real.pi)) |>.sub
    (hasDerivAt_id v) using 1 <;>
    first | rfl | (field_simp [Real.pi_ne_zero] <;> ring)

theorem hasDerivAt_reflectionPhaseDeriv
    {τ v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (reflectionPhaseDeriv τ) (reflectionPhaseSecond τ v) v := by
  unfold reflectionPhaseDeriv reflectionPhaseSecond
  convert (hasDerivAt_inv hv).const_mul (τ / (2 * Real.pi)) |>.sub_const 1 using 1 <;>
    field_simp [Real.pi_ne_zero] <;> ring

theorem hasDerivAt_reflectionAmplitude
    {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt reflectionAmplitude (reflectionAmplitudeDeriv v) v := by
  unfold reflectionAmplitude reflectionAmplitudeDeriv
  exact (hasDerivAt_inv hv).ofReal_comp

theorem norm_reflectionAmplitude {v : ℝ} (hv : 0 < v) :
    ‖reflectionAmplitude v‖ = 1 / v := by
  simp [reflectionAmplitude, Real.norm_eq_abs, abs_of_pos hv]

theorem norm_reflectionAmplitudeDeriv {v : ℝ} (hv : 0 < v) :
    ‖reflectionAmplitudeDeriv v‖ = 1 / v ^ 2 := by
  simp [reflectionAmplitudeDeriv, Real.norm_eq_abs, abs_of_pos hv,
    abs_of_pos (sq_pos_of_pos hv)]

/-- The phase/amplitude used below is exactly the source kernel
`v^(-1+iτ)e(-v)`, written without complex powers so its branch convention is
transparent. -/
theorem reflectionKernel_eq_exp_form
    {τ v : ℝ} (hv : 0 < v) :
    additivePhase (reflectionPhase τ v) * reflectionAmplitude v =
      ((v⁻¹ : ℝ) : ℂ) *
        Complex.exp (Complex.I * (τ * Real.log v)) *
        Complex.exp (-((2 * Real.pi * v : ℝ) : ℂ) * Complex.I) := by
  unfold additivePhase reflectionPhase reflectionAmplitude
  have hexp :
      Complex.exp
          (2 * (Real.pi : ℂ) *
            ((τ / (2 * Real.pi) * Real.log v - v : ℝ) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * (τ * Real.log v)) *
          Complex.exp (-((2 * Real.pi * v : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hexp]
  ring

/-- Literal dyadic stationary-phase estimate used in Lemma 6.2.  The
right-hand side is already `O(τ⁻¹/2)`: the numerator is `2/V`, while the
denominator is `sqrt(τ/(8πV²))`. -/
theorem norm_reflectionKernelIntegral_le
    {τ V : ℝ} (hτ : 0 < τ) (hV : 0 < V) :
    ‖∫ v : ℝ in V..2 * V,
        additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ ≤
      10 * (1 / V + 1 / V) /
        Real.sqrt (τ / (8 * Real.pi * V ^ 2)) := by
  let m : ℝ := Real.sqrt (τ / (8 * Real.pi * V ^ 2))
  have hmArg : 0 < τ / (8 * Real.pi * V ^ 2) := by positivity
  have hm : 0 < m := by unfold m; positivity
  have hab : V ≤ 2 * V := by linarith
  have hphase : ∀ v ∈ Set.Icc V (2 * V),
      HasDerivAt (reflectionPhase τ) (reflectionPhaseDeriv τ v) v := by
    intro v hv
    exact hasDerivAt_reflectionPhase (ne_of_gt (hV.trans_le hv.1))
  have hphase' : ∀ v ∈ Set.Icc V (2 * V),
      HasDerivAt (reflectionPhaseDeriv τ) (reflectionPhaseSecond τ v) v := by
    intro v hv
    exact hasDerivAt_reflectionPhaseDeriv (ne_of_gt (hV.trans_le hv.1))
  have hcurvature : ∀ v ∈ Set.Icc V (2 * V),
      m ^ 2 ≤ |reflectionPhaseSecond τ v| := by
    intro v hv
    have hvPos : 0 < v := hV.trans_le hv.1
    have hvSq : v ^ 2 ≤ 4 * V ^ 2 := by
      calc
        v ^ 2 ≤ (2 * V) ^ 2 := by
          gcongr
          exact hv.2
        _ = 4 * V ^ 2 := by ring
    have hdenV : 0 < 8 * Real.pi * V ^ 2 := by positivity
    have hdenv : 0 < 2 * Real.pi * v ^ 2 := by positivity
    have hfrac : τ / (8 * Real.pi * V ^ 2) ≤
        τ / (2 * Real.pi * v ^ 2) := by
      rw [div_le_div_iff₀ hdenV hdenv]
      calc
        τ * (2 * Real.pi * v ^ 2) ≤
            τ * (2 * Real.pi * (4 * V ^ 2)) := by gcongr
        _ = τ * (8 * Real.pi * V ^ 2) := by ring
    unfold m
    rw [Real.sq_sqrt hmArg.le]
    unfold reflectionPhaseSecond
    have hneg : -τ / (2 * Real.pi * v ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ.le) hdenv.le
    rw [abs_of_nonpos hneg]
    convert hfrac using 1 <;> ring
  have hsign :
      ∀ v ∈ Set.Icc V (2 * V), reflectionPhaseSecond τ v ≤ 0 := by
    intro v hv
    unfold reflectionPhaseSecond
    have hvPos : 0 < v := hV.trans_le hv.1
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ.le) (by positivity)
  have hamp : ∀ v ∈ Set.Icc V (2 * V),
      HasDerivAt reflectionAmplitude (reflectionAmplitudeDeriv v) v := by
    intro v hv
    exact hasDerivAt_reflectionAmplitude (ne_of_gt (hV.trans_le hv.1))
  have hphaseSecondCont : ContinuousOn (reflectionPhaseSecond τ)
      (Set.Icc V (2 * V)) := by
    intro v hv
    have hv0 : v ≠ 0 := ne_of_gt (hV.trans_le hv.1)
    have hden : 2 * Real.pi * v ^ 2 ≠ 0 := by positivity
    have hc : ContinuousAt (fun z : ℝ => -τ / (2 * Real.pi * z ^ 2)) v :=
      continuousAt_const.div
        (continuousAt_const.mul (continuousAt_id.pow 2)) hden
    exact hc.continuousWithinAt
  have hampDerivCont : ContinuousOn reflectionAmplitudeDeriv
      (Set.Icc V (2 * V)) := by
    intro v hv
    have hv0 : v ≠ 0 := ne_of_gt (hV.trans_le hv.1)
    have hr : ContinuousAt (fun z : ℝ => -(z ^ 2)⁻¹) v :=
      ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hv0)).neg
    exact (Complex.continuous_ofReal.continuousAt.comp hr).continuousWithinAt
  have hampBound : ∀ v ∈ Set.Icc V (2 * V),
      ‖reflectionAmplitude v‖ ≤ 1 / V := by
    intro v hv
    have hvPos : 0 < v := hV.trans_le hv.1
    rw [norm_reflectionAmplitude hvPos]
    exact one_div_le_one_div_of_le hV hv.1
  have hderivPoint : ∀ v ∈ Set.Icc V (2 * V),
      ‖reflectionAmplitudeDeriv v‖ ≤ 1 / V ^ 2 := by
    intro v hv
    have hvPos : 0 < v := hV.trans_le hv.1
    rw [norm_reflectionAmplitudeDeriv hvPos]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hV) (by
      gcongr
      exact hv.1)
  have hderivInt :
      (∫ v : ℝ in V..2 * V, ‖reflectionAmplitudeDeriv v‖) ≤ 1 / V := by
    have hfCont : ContinuousOn (fun v ↦ ‖reflectionAmplitudeDeriv v‖)
        (Set.Icc V (2 * V)) := hampDerivCont.norm
    have hfInt : IntervalIntegrable (fun v ↦ ‖reflectionAmplitudeDeriv v‖)
        volume V (2 * V) := by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le hab] using hfCont
    have hcInt : IntervalIntegrable (fun _v : ℝ ↦ 1 / V ^ 2)
        volume V (2 * V) := intervalIntegrable_const
    calc
      (∫ v : ℝ in V..2 * V, ‖reflectionAmplitudeDeriv v‖) ≤
          ∫ _v : ℝ in V..2 * V, 1 / V ^ 2 :=
        intervalIntegral.integral_mono_on hab hfInt hcInt hderivPoint
      _ = 1 / V := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp
        ring
  have hvdc := weightedSecondDerivativeVanDerCorputC1
    (a := V) (b := 2 * V) (m := m) (M := 1 / V)
    hab hm (by positivity) hphase hphase' hcurvature (Or.inr hsign)
    hamp hphaseSecondCont hampDerivCont hampBound
  calc
    ‖∫ v : ℝ in V..2 * V,
        additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ ≤
      10 * (1 / V +
        ∫ v : ℝ in V..2 * V, ‖reflectionAmplitudeDeriv v‖) / m := hvdc
    _ ≤ 10 * (1 / V + 1 / V) / m := by
      gcongr
    _ = 10 * (1 / V + 1 / V) /
        Real.sqrt (τ / (8 * Real.pi * V ^ 2)) := by rfl

/-- The dyadic estimate with the scale `V` cancelled.  This is the uniform
`τ⁻¹/²` form needed when Lemma 6.2 sums the dyadic `v`-blocks. -/
theorem norm_reflectionKernelIntegral_le_uniform
    {τ V : ℝ} (hτ : 0 < τ) (hV : 0 < V) :
    ‖∫ v : ℝ in V..2 * V,
        additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ ≤
      20 * Real.sqrt (8 * Real.pi) / Real.sqrt τ := by
  have hraw := norm_reflectionKernelIntegral_le hτ hV
  calc
    ‖∫ v : ℝ in V..2 * V,
        additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ ≤
        10 * (1 / V + 1 / V) /
          Real.sqrt (τ / (8 * Real.pi * V ^ 2)) := hraw
    _ = 20 * Real.sqrt (8 * Real.pi) / Real.sqrt τ := by
      rw [Real.sqrt_div hτ.le]
      rw [show 8 * Real.pi * V ^ 2 = (8 * Real.pi) * V ^ 2 by ring]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 * Real.pi)]
      rw [Real.sqrt_sq hV.le]
      field_simp [hV.ne', (Real.sqrt_pos.2 hτ).ne',
        (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 8 * Real.pi)).ne']
      <;> ring

def dyadicPoint (V : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * V

/-- Exact telescoping of adjacent dyadic interval integrals. -/
theorem intervalIntegral_dyadicPartition
    {F : ℝ → ℂ} {V : ℝ} (hV : 0 < V) (J : ℕ)
    (hInt : ∀ A B : ℝ, 0 < A → 0 < B →
      IntervalIntegrable F volume A B) :
    (∫ v : ℝ in V..dyadicPoint V J, F v) =
      ∑ j ∈ Finset.range J,
        ∫ v : ℝ in dyadicPoint V j..dyadicPoint V (j + 1), F v := by
  induction J with
  | zero => simp [dyadicPoint]
  | succ J ih =>
      rw [Finset.sum_range_succ,
        Finset.sum_congr rfl (fun _j _hj => rfl)]
      rw [← ih]
      have hdyadicJ : 0 < dyadicPoint V J := by
        unfold dyadicPoint
        positivity
      have hdyadicSucc : 0 < dyadicPoint V (J + 1) := by
        unfold dyadicPoint
        positivity
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hInt V (dyadicPoint V J) hV hdyadicJ)
        (hInt (dyadicPoint V J) (dyadicPoint V (J + 1))
          hdyadicJ hdyadicSucc)]

theorem reflectionKernel_intervalIntegrable
    {τ A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntervalIntegrable
      (fun v : ℝ =>
        additivePhase (reflectionPhase τ v) * reflectionAmplitude v)
      volume A B := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxPos : 0 < x := by
    rw [Set.mem_uIcc] at hx
    rcases hx with hx | hx
    · exact hA.trans_le hx.1
    · exact hB.trans_le hx.1
  have hphase := hasDerivAt_additivePhase_comp
    (phase := reflectionPhase τ) (phase' := reflectionPhaseDeriv τ)
    (hasDerivAt_reflectionPhase hxPos.ne')
  exact (hphase.continuousAt.mul
    (hasDerivAt_reflectionAmplitude hxPos.ne').continuousAt).continuousWithinAt

/-- Summing `J` exact dyadic blocks costs only the number of blocks.  Thus the
reflection kernel on a dyadic union retains the `τ⁻¹/²` saving, with the
logarithmic block count exposed rather than hidden in `T^{o(1)}`. -/
theorem norm_reflectionKernelDyadicUnion_le
    {τ V : ℝ} (hτ : 0 < τ) (hV : 0 < V) (J : ℕ) :
    ‖∫ v : ℝ in V..dyadicPoint V J,
        additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ ≤
      J * (20 * Real.sqrt (8 * Real.pi) / Real.sqrt τ) := by
  rw [intervalIntegral_dyadicPartition hV J
    (fun A B hA hB => reflectionKernel_intervalIntegrable hA hB)]
  calc
    ‖∑ j ∈ Finset.range J,
        ∫ v : ℝ in dyadicPoint V j..dyadicPoint V (j + 1),
          additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ ≤
      ∑ j ∈ Finset.range J,
        ‖∫ v : ℝ in dyadicPoint V j..dyadicPoint V (j + 1),
          additivePhase (reflectionPhase τ v) * reflectionAmplitude v‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range J,
        (20 * Real.sqrt (8 * Real.pi) / Real.sqrt τ) := by
      apply Finset.sum_le_sum
      intro j hj
      convert norm_reflectionKernelIntegral_le_uniform hτ
        (show 0 < dyadicPoint V j by unfold dyadicPoint; positivity) using 1
      unfold dyadicPoint
      rw [pow_succ]
      ring
    _ = J * (20 * Real.sqrt (8 * Real.pi) / Real.sqrt τ) := by
      simp

end

end GuthMaynardReflectionKernelVdC

#print axioms GuthMaynardReflectionKernelVdC.hasDerivAt_reflectionPhase
#print axioms GuthMaynardReflectionKernelVdC.hasDerivAt_reflectionPhaseDeriv
#print axioms GuthMaynardReflectionKernelVdC.reflectionKernel_eq_exp_form
#print axioms GuthMaynardReflectionKernelVdC.norm_reflectionKernelIntegral_le
#print axioms GuthMaynardReflectionKernelVdC.norm_reflectionKernelIntegral_le_uniform
#print axioms GuthMaynardReflectionKernelVdC.intervalIntegral_dyadicPartition
#print axioms GuthMaynardReflectionKernelVdC.reflectionKernel_intervalIntegrable
#print axioms GuthMaynardReflectionKernelVdC.norm_reflectionKernelDyadicUnion_le
