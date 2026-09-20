import FordMixedKernelFTC

open scoped BigOperators
noncomputable section
namespace FordMixedKernelBounds

open FordMixedReciprocalIntegral FordMixedKernelFTC

/-- Shift sum and product, retained literally for endpoint bounds. -/
def shiftSum : List ℝ → ℝ
  | [] => 0
  | h :: hs => h + shiftSum hs

def shiftProd : List ℝ → ℝ
  | [] => 1
  | h :: hs => h * shiftProd hs

/-- Rising coefficient, in recursive form to avoid factorial normalization. -/
def riseCoeff : ℕ → List ℝ → ℝ
  | p, [] => 1
  | p, _ :: hs => (p : ℝ) * riseCoeff (p + 1) hs

def signedKernelDiff (p : ℕ) (hs : List ℝ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ hs.length * mixedDiff hs (reciprocalKernel p) x

lemma riseCoeff_pos {p : ℕ} {hs : List ℝ} (hp : 1 ≤ p) :
    0 < riseCoeff p hs := by
  induction hs generalizing p with
  | nil => simp [riseCoeff]
  | cons h hs ih =>
      simp only [riseCoeff]
      exact mul_pos (by positivity) (ih (p := p + 1) (by omega))

lemma shiftSum_nonneg {hs : List ℝ} (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    0 ≤ shiftSum hs := by
  induction hs with
  | nil => simp [shiftSum]
  | cons h hs ih =>
      simp only [shiftSum]
      exact add_nonneg (hsteps h (by simp)) (ih (fun q hq => hsteps q (by simp [hq])))

lemma shiftProd_nonneg {hs : List ℝ} (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    0 ≤ shiftProd hs := by
  induction hs with
  | nil => simp [shiftProd]
  | cons h hs ih =>
      simp only [shiftProd]
      exact mul_nonneg (hsteps h (by simp)) (ih (fun q hq => hsteps q (by simp [hq])))

lemma signedKernelDiff_nil {p : ℕ} {x : ℝ} :
    signedKernelDiff p [] x = reciprocalKernel p x := by
  simp [signedKernelDiff, reciprocalKernel]

lemma signedKernelDiff_cons_integral
    (hs : List ℝ) {p : ℕ} {x h : ℝ} (hp : 1 ≤ p)
    (hx : 0 < x) (hh : 0 ≤ h)
    (hsteps : ∀ q ∈ hs, 0 ≤ q) :
    signedKernelDiff p (h :: hs) x =
      (p : ℝ) * ∫ y in x..x + h, signedKernelDiff (p + 1) hs y := by
  have hftc := mixedDiff_cons_kernel_eq_neg_mul_integral hs hp hx hh hsteps
  calc
    signedKernelDiff p (h :: hs) x =
        (-1 : ℝ) ^ (hs.length + 1) *
          (-(p : ℝ) * ∫ y in x..x + h,
            mixedDiff hs (reciprocalKernel (p + 1)) y) := by
      simpa [signedKernelDiff, hftc, List.length_cons]
    _ = (p : ℝ) * ∫ y in x..x + h,
          ((-1 : ℝ) ^ hs.length *
            mixedDiff hs (reciprocalKernel (p + 1)) y) := by
      rw [intervalIntegral.integral_const_mul, pow_succ]
      ring
    _ = (p : ℝ) * ∫ y in x..x + h,
          signedKernelDiff (p + 1) hs y := by rfl

lemma signedKernelDiff_bounds
    (hs : List ℝ) {p : ℕ} {x : ℝ} (hp : 1 ≤ p) (hx : 0 < x)
    (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    riseCoeff p hs * shiftProd hs /
        (x + shiftSum hs) ^ (p + hs.length) ≤
      signedKernelDiff p hs x ∧
      signedKernelDiff p hs x ≤
        riseCoeff p hs * shiftProd hs / x ^ (p + hs.length) := by
  induction hs generalizing p x with
  | nil =>
      constructor <;> simp [signedKernelDiff, riseCoeff, shiftProd, shiftSum,
        reciprocalKernel]
  | cons h hs ih =>
      have hh : 0 ≤ h := hsteps h (by simp)
      have htail : ∀ q ∈ hs, 0 ≤ q := by
        intro q hq
        exact hsteps q (by simp [hq])
      have hsum0 : 0 ≤ shiftSum hs := shiftSum_nonneg htail
      have hprod0 : 0 ≤ shiftProd hs := shiftProd_nonneg htail
      have hcoeff0 : 0 ≤ riseCoeff (p + 1) hs :=
        (riseCoeff_pos (p := p + 1) (by omega)).le
      have hrepr := signedKernelDiff_cons_integral hs hp hx hh htail
      have hcont : ContinuousOn (signedKernelDiff (p + 1) hs)
          (Set.Icc x (x + h)) := by
        apply continuousOn_of_forall_continuousAt
        intro y hy
        unfold signedKernelDiff
        exact (continuousAt_const : ContinuousAt (fun _ : ℝ =>
            (-1 : ℝ) ^ hs.length) y).mul
          (hasDerivAt_mixedDiff_reciprocalKernel hs (p := p + 1)
            (by omega) (lt_of_lt_of_le hx hy.1) htail).continuousAt
      have hint : IntervalIntegrable (signedKernelDiff (p + 1) hs)
          MeasureTheory.volume x (x + h) := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (by linarith : x ≤ x + h)]
        exact hcont
      have hlower : ∀ y ∈ Set.Icc x (x + h),
          riseCoeff (p + 1) hs * shiftProd hs /
              (x + h + shiftSum hs) ^ (p + 1 + hs.length) ≤
            signedKernelDiff (p + 1) hs y := by
        intro y hy
        have hyb := (ih (p := p + 1) (x := y) (by omega)
          (lt_of_lt_of_le hx hy.1) htail)
        apply le_trans ?_ hyb.1
        have hys : 0 < y + shiftSum hs := by linarith [hy.1, hsum0]
        have hxhS : 0 < x + h + shiftSum hs := by linarith [hx, hh, hsum0]
        have hden : y + shiftSum hs ≤ x + h + shiftSum hs := by linarith [hy.2]
        have hpow := pow_le_pow_left₀ (le_of_lt hys) hden
          (p + 1 + hs.length)
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hcoeff0 hprod0)
      have hupper : ∀ y ∈ Set.Icc x (x + h),
          signedKernelDiff (p + 1) hs y ≤
            riseCoeff (p + 1) hs * shiftProd hs /
              x ^ (p + 1 + hs.length) := by
        intro y hy
        have hyb := (ih (p := p + 1) (x := y) (by omega)
          (lt_of_lt_of_le hx hy.1) htail)
        apply le_trans hyb.2
        have hys : 0 < y := lt_of_lt_of_le hx hy.1
        have hpow := pow_le_pow_left₀ (le_of_lt hx) hy.1
          (p + 1 + hs.length)
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hcoeff0 hprod0)
      have hlowint :
          riseCoeff (p + 1) hs * shiftProd hs /
              (x + h + shiftSum hs) ^ (p + 1 + hs.length) * h ≤
            ∫ y in x..x + h, signedKernelDiff (p + 1) hs y := by
        have hc : IntervalIntegrable
            (fun _ : ℝ => riseCoeff (p + 1) hs * shiftProd hs /
              (x + h + shiftSum hs) ^ (p + 1 + hs.length))
            MeasureTheory.volume x (x + h) := intervalIntegrable_const
        have hm := intervalIntegral.integral_mono_on
          (by linarith : x ≤ x + h) hc hint hlower
        calc
          _ = ∫ _ : ℝ in x..x + h,
              riseCoeff (p + 1) hs * shiftProd hs /
                (x + h + shiftSum hs) ^ (p + 1 + hs.length) := by
            rw [intervalIntegral.integral_const]
            ring
          _ ≤ _ := hm
      have huppint :
          ∫ y in x..x + h, signedKernelDiff (p + 1) hs y ≤
            riseCoeff (p + 1) hs * shiftProd hs /
              x ^ (p + 1 + hs.length) * h := by
        have hc : IntervalIntegrable
            (fun _ : ℝ => riseCoeff (p + 1) hs * shiftProd hs /
              x ^ (p + 1 + hs.length))
            MeasureTheory.volume x (x + h) := intervalIntegrable_const
        have hm := intervalIntegral.integral_mono_on
          (by linarith : x ≤ x + h) hint hc hupper
        calc
          _ = ∫ _ : ℝ in x..x + h,
              riseCoeff (p + 1) hs * shiftProd hs /
                x ^ (p + 1 + hs.length) := by
            rw [intervalIntegral.integral_const]
            ring
          _ ≥ _ := hm
      constructor
      · rw [hrepr]
        dsimp [riseCoeff, shiftProd, shiftSum]
        have hpR : 0 ≤ (p : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hlowint hpR
        convert this using 1 <;> ring
      · rw [hrepr]
        dsimp [riseCoeff, shiftProd, shiftSum]
        have hpR : 0 ≤ (p : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left huppint hpR
        convert this using 1 <;> ring

end FordMixedKernelBounds

#print axioms FordMixedKernelBounds.signedKernelDiff_bounds
