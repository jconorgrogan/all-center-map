import Mathlib

noncomputable section
namespace FordMixedReciprocalIntegral

/-- Iterated forward difference with the shifts applied from left to right. -/
def mixedDiff : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f, x => f x
  | h :: hs, f, x => mixedDiff hs f (x + h) - mixedDiff hs f x

@[simp] lemma mixedDiff_nil (f : ℝ → ℝ) (x : ℝ) :
    mixedDiff [] f x = f x := rfl

@[simp] lemma mixedDiff_cons (h : ℝ) (hs : List ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mixedDiff (h :: hs) f x = mixedDiff hs f (x + h) - mixedDiff hs f x := rfl

/-- Differentiation commutes with the mixed forward differences on a positive
half-line.  This is the induction interface for the iterated FTC proof. -/
lemma hasDerivAt_mixedDiff_of_pos
    (hs : List ℝ) {f f' : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hderiv : ∀ y, 0 < y → HasDerivAt f (f' y) y) :
    HasDerivAt (mixedDiff hs f) (mixedDiff hs f' x) x := by
  induction hs generalizing x with
  | nil =>
      convert hderiv x hx
      · ext; rfl
      · rfl
  | cons h hs ih =>
      have hh : 0 ≤ h := hsteps h (by simp)
      have htail : ∀ q ∈ hs, 0 ≤ q := by
        intro q hq
        exact hsteps q (by simp [hq])
      have hbase := ih (x := x) hx htail
      have hshift := ih (x := x + h) (by linarith) htail
      have hcomp := hshift.comp x ((hasDerivAt_id x).add_const h)
      have hsub := hcomp.sub hbase
      convert hsub
      · ext; rfl
      · simp [mixedDiff]

/-- The logarithm instance of the derivative compatibility lemma, with the
reciprocal as the differentiated kernel. -/
lemma hasDerivAt_log_mixedDiff
    (hs : List ℝ) {x : ℝ} (hx : 0 < x)
    (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    HasDerivAt (mixedDiff hs Real.log)
      (mixedDiff hs (fun y : ℝ => 1 / y) x) x := by
  apply hasDerivAt_mixedDiff_of_pos hs hx hsteps
  intro y hy
  have h := ((hasDerivAt_id y).log hy.ne')
  simpa [one_div] using h

/-- One FTC step for the recursive mixed difference.  The continuity and
integrability premises are deliberately explicit, so later positivity proofs
can discharge them from the reciprocal kernel without hiding analytic input. -/
lemma mixedDiff_cons_eq_intervalIntegral
    (hs : List ℝ) {f f' : ℝ → ℝ} {x h : ℝ}
    (hxh : x ≤ x + h)
    (hcont : ContinuousOn (mixedDiff hs f) (Set.Icc x (x + h)))
    (hderiv : ∀ y ∈ Set.Ioo x (x + h),
      HasDerivAt (mixedDiff hs f) (mixedDiff hs f' y) y)
    (hint : IntervalIntegrable (mixedDiff hs f') MeasureTheory.volume x (x + h)) :
    mixedDiff (h :: hs) f x =
      ∫ y in x..x + h, mixedDiff hs f' y := by
  rw [mixedDiff]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hxh hcont hderiv hint

/-- The sign convention for the `(r+1)`-st logarithmic difference. -/
def signedMixedDiff (hs : List ℝ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (hs.length + 1) * mixedDiff hs Real.log x

@[simp] lemma signedMixedDiff_nil (x : ℝ) :
    signedMixedDiff [] x = -Real.log x := by
  simp [signedMixedDiff]

/- The positive reciprocal kernel used after differentiating a logarithmic
mixed difference. -/
def reciprocalKernel (p : ℕ) (x : ℝ) : ℝ := 1 / x ^ p

lemma reciprocalKernel_pos {p : ℕ} {x : ℝ} (hx : 0 < x) :
    0 < reciprocalKernel p x := by
  unfold reciprocalKernel
  positivity

lemma hasDerivAt_reciprocalKernel {p : ℕ} {x : ℝ} (hp : 1 ≤ p) (hx : 0 < x) :
    HasDerivAt (reciprocalKernel p)
      (-(p : ℝ) / x ^ (p + 1)) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h := (hasDerivAt_pow p x).inv (pow_ne_zero p hx0)
  have hder : (-((p : ℝ) * x ^ (p - 1)) / (x ^ p) ^ 2) = (-(p : ℝ) / x ^ (p + 1)) := by
    have hxpow : x ^ p ≠ 0 := pow_ne_zero p hx0
    have hxpow' : x ^ (p + 1) ≠ 0 := pow_ne_zero (p + 1) hx0
    have hsq : (x ^ p) ^ 2 ≠ 0 := pow_ne_zero 2 hxpow
    apply (div_eq_div_iff hsq hxpow').mpr
    have hpow : x ^ (p - 1) * x ^ (p + 1) = (x ^ p) ^ 2 := by
      rw [← pow_add, ← pow_mul, mul_two]
      congr 1
      omega
    calc
      -((p : ℝ) * x ^ (p - 1)) * x ^ (p + 1)
          = -((p : ℝ) * (x ^ (p - 1) * x ^ (p + 1))) := by ring
      _ = -((p : ℝ) * (x ^ p) ^ 2) := by rw [hpow]
      _ = -(p : ℝ) * (x ^ p) ^ 2 := by ring
  unfold reciprocalKernel
  have hfun : (fun y : ℝ => 1 / y ^ p) = fun y => (y ^ p)⁻¹ := by
    funext y; simp [one_div]
  rw [hfun]
  convert h using 1
  exact hder.symm

lemma continuousOn_reciprocalKernel {p : ℕ} {a b : ℝ}
    (ha : 0 < a) :
    ContinuousOn (reciprocalKernel p) (Set.Icc a b) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  exact (continuousAt_const.div
    (continuousAt_id.pow p) (by positivity : x ^ p ≠ 0)).continuousWithinAt

lemma intervalIntegrable_reciprocalKernel {p : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (reciprocalKernel p) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact continuousOn_reciprocalKernel ha

lemma hasDerivAt_mixedDiff_reciprocalKernel
    (hs : List ℝ) {p : ℕ} {x : ℝ} (hp : 1 ≤ p) (hx : 0 < x)
    (hsteps : ∀ h ∈ hs, 0 ≤ h) :
    HasDerivAt (mixedDiff hs (reciprocalKernel (p : ℕ)))
      (mixedDiff hs (fun y : ℝ => -(p : ℝ) / y ^ ((p : ℕ) + 1)) x) x := by
  apply hasDerivAt_mixedDiff_of_pos hs hx hsteps
  intro y hy
  exact hasDerivAt_reciprocalKernel hp hy

end FordMixedReciprocalIntegral

#print axioms FordMixedReciprocalIntegral.hasDerivAt_mixedDiff_of_pos
#print axioms FordMixedReciprocalIntegral.hasDerivAt_log_mixedDiff
#print axioms FordMixedReciprocalIntegral.mixedDiff_cons_eq_intervalIntegral
#print axioms FordMixedReciprocalIntegral.hasDerivAt_reciprocalKernel
#print axioms FordMixedReciprocalIntegral.intervalIntegrable_reciprocalKernel
#print axioms FordMixedReciprocalIntegral.hasDerivAt_mixedDiff_reciprocalKernel
