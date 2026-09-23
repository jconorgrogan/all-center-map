import GuthMaynardLemma295DualTail
import GuthMaynardLemma295ThetaAnalytic
import GuthMaynardLemma295FiniteContour

/-!
# Pole-free second rectangle in Lemma 29.5

After applying the zeta functional equation on the deep-left line, retain the
first `K` terms of the absolutely convergent dual Dirichlet series.  This
finite reflected integrand is holomorphic throughout every rectangle whose
right edge lies strictly left of `Re s = 1`; hence its boundary integral is
zero.  This is the finite Cauchy--Goursat core of the source's second contour
movement back to the critical line.
-/

namespace GuthMaynardLemma295ReflectedFiniteContour

open Complex Set
open FinitePoleRectangle
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295FiniteContour
open GuthMaynardLemma295ThetaAnalytic

noncomputable section

/-- The retained finite dual Dirichlet series is entire. -/
theorem differentiable_sourceDualPartialNat (K : ℕ) :
    Differentiable ℂ (sourceDualPartialNat K) := by
  unfold sourceDualPartialNat
  have h : Differentiable ℂ
      (∑ n ∈ Finset.range K,
        (fun z : ℂ => 1 / ((n + 1 : ℕ) : ℂ) ^ (1 - z))) := by
    apply Differentiable.sum
    intro n hn
    apply Differentiable.fun_div (differentiable_const (c := (1 : ℂ)))
    · exact ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).const_cpow
        (.inl (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)))
    · intro z
      simpa only [Nat.cast_add, Nat.cast_one] using
        Complex.natCast_add_one_cpow_ne_zero n (1 - z)
  rw [show (fun z : ℂ => ∑ n ∈ Finset.range K,
      1 / ((n + 1 : ℕ) : ℂ) ^ (1 - z)) =
      (∑ n ∈ Finset.range K,
        (fun z : ℂ => 1 / ((n + 1 : ℕ) : ℂ) ^ (1 - z))) by
    funext z
    simp]
  exact h

/-- Literal finite reflected integrand after the functional equation. -/
def lemma295ReflectedFiniteIntegrand
    (N g : ℝ) (K : ℕ) (s : ℂ) : ℂ :=
  let z := s - g * I
  sourceZetaTheta z * sourceDualPartialNat K z *
    (N : ℂ) ^ z * mellin sourceHZero s

/-- The finite reflected integrand is holomorphic wherever `Re s < 1`.
The imaginary translation by `g` does not change the real part. -/
theorem differentiableAt_lemma295ReflectedFiniteIntegrand
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ)
    {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (lemma295ReflectedFiniteIntegrand N g K) s := by
  let z : ℂ := s - g * I
  have hzre : z.re = s.re := by simp [z]
  have hz : z.re < 1 := by simpa [hzre] using hs
  have hinner : DifferentiableAt ℂ (fun w : ℂ => w - g * I) s := by
    fun_prop
  have htheta : DifferentiableAt ℂ
      (fun w : ℂ => sourceZetaTheta (w - g * I)) s :=
    by
      simpa only [Function.comp_def] using!
        (differentiableAt_sourceZetaTheta_of_re_lt_one hz).comp s hinner
  have hpartial : DifferentiableAt ℂ
      (fun w : ℂ => sourceDualPartialNat K (w - g * I)) s :=
    by
      simpa only [Function.comp_def] using!
        (differentiable_sourceDualPartialNat K).differentiableAt.comp s hinner
  have hscale : DifferentiableAt ℂ
      (fun w : ℂ => (N : ℂ) ^ (w - g * I)) s :=
    hinner.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  have hmellin : DifferentiableAt ℂ (mellin sourceHZero) s :=
    differentiableAt_mellin_sourceHZero s
  exact (((htheta.mul hpartial).mul hscale).mul hmellin :
    DifferentiableAt ℂ (lemma295ReflectedFiniteIntegrand N g K) s)

/-- Exact finite second-rectangle identity.  There are no residues. -/
theorem rectangleBoundaryIntegral_reflectedFinite_eq_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ)
    {a b u v : ℝ} (hab : a ≤ b) (hb : b < 1) :
    rectangleBoundaryIntegral
        (lemma295ReflectedFiniteIntegrand N g K) a b u v = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro s hs
  have hsre := hs.1
  rw [uIcc_of_le hab] at hsre
  exact (differentiableAt_lemma295ReflectedFiniteIntegrand hN g K
    (by linarith [hsre.2])).differentiableWithinAt

end


end GuthMaynardLemma295ReflectedFiniteContour

#print axioms GuthMaynardLemma295ReflectedFiniteContour.differentiable_sourceDualPartialNat
#print axioms GuthMaynardLemma295ReflectedFiniteContour.differentiableAt_lemma295ReflectedFiniteIntegrand
#print axioms GuthMaynardLemma295ReflectedFiniteContour.rectangleBoundaryIntegral_reflectedFinite_eq_zero
