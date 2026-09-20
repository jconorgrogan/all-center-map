import FordMixedKernelBounds

open scoped BigOperators
noncomputable section
namespace FordMixedLogBounds

open FordMixedReciprocalIntegral FordMixedKernelFTC FordMixedKernelBounds

lemma signedMixedDiff_cons_integral
    (hs : List ℝ) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hsteps : ∀ q ∈ hs, 0 ≤ q) :
    signedMixedDiff (h :: hs) x =
      ∫ y in x..x + h, signedKernelDiff 1 hs y := by
  have hxh : x ≤ x + h := by linarith
  have hcont : ContinuousOn (mixedDiff hs Real.log) (Set.Icc x (x + h)) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    exact (hasDerivAt_log_mixedDiff hs (lt_of_lt_of_le hx hy.1) hsteps).continuousAt
  have hderiv : ∀ y ∈ Set.Ioo x (x + h),
      HasDerivAt (mixedDiff hs Real.log)
        (mixedDiff hs (fun z : ℝ => 1 / z) y) y := by
    intro y hy
    exact hasDerivAt_mixedDiff_of_pos hs
      (lt_of_lt_of_le hx (le_of_lt hy.1)) hsteps
      (fun z hz => by
        have h := ((hasDerivAt_id z).log hz.ne')
        simpa [one_div] using h)
  have hcontrec : ContinuousOn
      (mixedDiff hs (fun z : ℝ => 1 / z)) (Set.Icc x (x + h)) := by
    have hc := continuousOn_mixedDiff_reciprocalKernel hs (p := 1) (by omega)
      (a := x) (b := x + h) hx hsteps
    have heq : (fun z : ℝ => 1 / z) = reciprocalKernel 1 := by
      funext z
      simp [reciprocalKernel]
    rw [heq]
    exact hc
  have hint : IntervalIntegrable (mixedDiff hs (fun z : ℝ => 1 / z))
      MeasureTheory.volume x (x + h) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxh]
    exact hcontrec
  have hftc := mixedDiff_cons_eq_intervalIntegral hs
    (f := Real.log) (f' := fun z : ℝ => 1 / z)
    (x := x) (h := h) hxh hcont hderiv hint
  calc
    signedMixedDiff (h :: hs) x =
        (-1 : ℝ) ^ (hs.length + 2) * mixedDiff (h :: hs) Real.log x := by
          rfl
    _ = (-1 : ℝ) ^ (hs.length + 2) *
        (∫ y in x..x + h, mixedDiff hs (fun z : ℝ => 1 / z) y) := by
          rw [hftc]
    _ = ∫ y in x..x + h, signedKernelDiff 1 hs y := by
      rw [show (-1 : ℝ) ^ (hs.length + 2) =
          (-1 : ℝ) ^ hs.length by
            rw [pow_add]
            norm_num]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y hy
      unfold signedKernelDiff reciprocalKernel
      ring

/-- Bounds for the signed `(len hs + 1)`-st logarithmic difference. -/
theorem signedMixedDiff_bounds
    (hs : List ℝ) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hsteps : ∀ q ∈ hs, 0 ≤ q) :
    riseCoeff 1 hs * shiftProd (h :: hs) /
        (x + shiftSum (h :: hs)) ^ (hs.length + 1) ≤
      signedMixedDiff (h :: hs) x ∧
      signedMixedDiff (h :: hs) x ≤
        riseCoeff 1 hs * shiftProd (h :: hs) /
          x ^ (hs.length + 1) := by
  have hxh : x ≤ x + h := by linarith
  have hrepr := signedMixedDiff_cons_integral hs hx hh hsteps
  have hsum0 : 0 ≤ shiftSum hs := shiftSum_nonneg hsteps
  have hprod0 : 0 ≤ shiftProd hs := shiftProd_nonneg hsteps
  have hcoeff0 : 0 ≤ riseCoeff 1 hs :=
    (riseCoeff_pos (p := 1) (hs := hs) (by omega)).le
  have hcont : ContinuousOn (signedKernelDiff 1 hs) (Set.Icc x (x + h)) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    unfold signedKernelDiff
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ =>
      (-1 : ℝ) ^ hs.length) y).mul
      (hasDerivAt_mixedDiff_reciprocalKernel hs (p := 1) (by omega)
        (lt_of_lt_of_le hx hy.1) hsteps).continuousAt
  have hint : IntervalIntegrable (signedKernelDiff 1 hs)
      MeasureTheory.volume x (x + h) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxh]
    exact hcont
  have hlower : ∀ y ∈ Set.Icc x (x + h),
      riseCoeff 1 hs * shiftProd hs /
          (x + h + shiftSum hs) ^ (hs.length + 1) ≤
        signedKernelDiff 1 hs y := by
    intro y hy
    have hyb := signedKernelDiff_bounds hs (p := 1) (by omega)
      (lt_of_lt_of_le hx hy.1) hsteps
    have hyb1 : riseCoeff 1 hs * shiftProd hs /
        (y + shiftSum hs) ^ (hs.length + 1) ≤ signedKernelDiff 1 hs y := by
      simpa [Nat.add_comm] using hyb.1
    apply le_trans ?_ hyb1
    have hys : 0 < y + shiftSum hs := by linarith [hy.1, hsum0]
    have hden : y + shiftSum hs ≤ x + h + shiftSum hs := by linarith [hy.2]
    have hpow := pow_le_pow_left₀ (le_of_lt hys) hden (hs.length + 1)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hcoeff0 hprod0)
  have hupper : ∀ y ∈ Set.Icc x (x + h),
      signedKernelDiff 1 hs y ≤
        riseCoeff 1 hs * shiftProd hs / x ^ (hs.length + 1) := by
    intro y hy
    have hyb := signedKernelDiff_bounds hs (p := 1) (by omega)
      (lt_of_lt_of_le hx hy.1) hsteps
    have hyb2 : signedKernelDiff 1 hs y ≤ riseCoeff 1 hs * shiftProd hs /
        y ^ (hs.length + 1) := by
      simpa [Nat.add_comm] using hyb.2
    apply le_trans hyb2
    have hpow := pow_le_pow_left₀ (le_of_lt hx) hy.1 (hs.length + 1)
    have hypos : 0 < y := lt_of_lt_of_le hx hy.1
    have hypow : 0 < y ^ (hs.length + 1) := by positivity
    have hxpow : 0 < x ^ (hs.length + 1) := by positivity
    apply (div_le_div_iff₀ hypow hxpow).2
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hcoeff0 hprod0)
  have hlowint :
      riseCoeff 1 hs * shiftProd hs /
          (x + h + shiftSum hs) ^ (hs.length + 1) * h ≤
        ∫ y in x..x + h, signedKernelDiff 1 hs y := by
    have hc : IntervalIntegrable
        (fun _ : ℝ => riseCoeff 1 hs * shiftProd hs /
          (x + h + shiftSum hs) ^ (hs.length + 1))
        MeasureTheory.volume x (x + h) := intervalIntegrable_const
    have hm := intervalIntegral.integral_mono_on hxh hc hint hlower
    calc
      _ = ∫ _ : ℝ in x..x + h,
          riseCoeff 1 hs * shiftProd hs /
            (x + h + shiftSum hs) ^ (hs.length + 1) := by
          rw [intervalIntegral.integral_const]
          ring
      _ ≤ _ := hm
  have huppint :
      ∫ y in x..x + h, signedKernelDiff 1 hs y ≤
        riseCoeff 1 hs * shiftProd hs / x ^ (hs.length + 1) * h := by
    have hc : IntervalIntegrable
        (fun _ : ℝ => riseCoeff 1 hs * shiftProd hs /
          x ^ (hs.length + 1))
        MeasureTheory.volume x (x + h) := intervalIntegrable_const
    have hm := intervalIntegral.integral_mono_on hxh hint hc hupper
    calc
      _ ≤ ∫ _ : ℝ in x..x + h,
          riseCoeff 1 hs * shiftProd hs / x ^ (hs.length + 1) := hm
      _ = _ := by
          rw [intervalIntegral.integral_const]
          ring
  constructor
  · rw [hrepr]
    dsimp [shiftProd, shiftSum]
    convert hlowint using 1 <;> ring
  · rw [hrepr]
    dsimp [shiftProd, shiftSum]
    convert huppint using 1 <;> ring

end FordMixedLogBounds

#print axioms FordMixedLogBounds.signedMixedDiff_cons_integral
#print axioms FordMixedLogBounds.signedMixedDiff_bounds
