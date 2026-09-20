import FordMixedReciprocalIntegral

open scoped BigOperators
noncomputable section
namespace FordMixedKernelFTC

open FordMixedReciprocalIntegral

lemma mixedDiff_const_mul (hs : List ℝ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mixedDiff hs (fun y => c * f y) x = c * mixedDiff hs f x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [mixedDiff]
      rw [ih, ih]
      ring

lemma continuousOn_mixedDiff_reciprocalKernel
    (hs : List ℝ) {p : ℕ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 < a)
    (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    ContinuousOn (mixedDiff hs (reciprocalKernel p)) (Set.Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro y hy
  exact (hasDerivAt_mixedDiff_reciprocalKernel hs hp
    (lt_of_lt_of_le ha hy.1) hsteps).continuousAt

/-- One fully discharged FTC step for the reciprocal kernel. -/
theorem mixedDiff_cons_kernel_eq_neg_mul_integral
    (hs : List ℝ) {p : ℕ} {x h : ℝ} (hp : 1 ≤ p)
    (hx : 0 < x) (hh : 0 ≤ h)
    (hsteps : ∀ q ∈ hs, 0 ≤ q) :
    mixedDiff (h :: hs) (reciprocalKernel p) x =
      -(p : ℝ) * ∫ y in x..x + h, mixedDiff hs
        (reciprocalKernel (p + 1)) y := by
  have hxh : x ≤ x + h := by linarith
  have hsteps' : ∀ q ∈ h :: hs, 0 ≤ q := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hh
    · exact hsteps q hq
  have hcont := continuousOn_mixedDiff_reciprocalKernel
    hs hp (a := x) (b := x + h) hx hsteps
  have hderiv : ∀ y ∈ Set.Ioo x (x + h),
      HasDerivAt (mixedDiff hs (reciprocalKernel p))
        (mixedDiff hs (fun z : ℝ => -(p : ℝ) / z ^ (p + 1)) y) y := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hx (le_of_lt hy.1)
    exact hasDerivAt_mixedDiff_of_pos hs hypos hsteps
      (fun z hz => hasDerivAt_reciprocalKernel hp hz)
  have hcontnext := continuousOn_mixedDiff_reciprocalKernel
    hs (p := p + 1) (by omega) (a := x) (b := x + h) hx hsteps
  have heq : (fun z : ℝ => -(p : ℝ) / z ^ (p + 1)) =
      (fun z : ℝ => (-(p : ℝ)) * reciprocalKernel (p + 1) z) := by
    funext z
    simp [reciprocalKernel, div_eq_mul_inv]
  have hcontderiv : ContinuousOn
      (mixedDiff hs (fun z : ℝ => -(p : ℝ) / z ^ (p + 1)))
      (Set.Icc x (x + h)) := by
    have hc : ContinuousOn
        (fun y : ℝ => (-(p : ℝ)) * mixedDiff hs
          (reciprocalKernel (p + 1)) y) (Set.Icc x (x + h)) :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => -(p : ℝ))
        (Set.Icc x (x + h))).mul hcontnext
    rw [heq]
    have hmul : mixedDiff hs
        (fun z : ℝ => (-(p : ℝ)) * reciprocalKernel (p + 1) z) =
        (fun y : ℝ => (-(p : ℝ)) * mixedDiff hs
          (reciprocalKernel (p + 1)) y) := by
      funext y
      exact mixedDiff_const_mul hs (-(p : ℝ))
        (reciprocalKernel (p + 1)) y
    rw [hmul]
    exact hc
  have hint : IntervalIntegrable
      (mixedDiff hs (fun z : ℝ => -(p : ℝ) / z ^ (p + 1)))
      MeasureTheory.volume x (x + h) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxh]
    exact hcontderiv
  have hftc := mixedDiff_cons_eq_intervalIntegral hs
    (f := reciprocalKernel p)
    (f' := fun z : ℝ => -(p : ℝ) / z ^ (p + 1))
    (x := x) (h := h) hxh hcont hderiv hint
  calc
    mixedDiff (h :: hs) (reciprocalKernel p) x =
        ∫ y in x..x + h,
          mixedDiff hs (fun z : ℝ => -(p : ℝ) / z ^ (p + 1)) y := hftc
    _ = ∫ y in x..x + h,
          (-(p : ℝ)) * mixedDiff hs (reciprocalKernel (p + 1)) y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [heq]
      exact mixedDiff_const_mul hs (-(p : ℝ))
        (reciprocalKernel (p + 1)) y
    _ = -(p : ℝ) * ∫ y in x..x + h,
          mixedDiff hs (reciprocalKernel (p + 1)) y := by
      rw [intervalIntegral.integral_const_mul]

end FordMixedKernelFTC

#print axioms FordMixedKernelFTC.mixedDiff_const_mul
#print axioms FordMixedKernelFTC.continuousOn_mixedDiff_reciprocalKernel
#print axioms FordMixedKernelFTC.mixedDiff_cons_kernel_eq_neg_mul_integral
