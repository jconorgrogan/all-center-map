import GuthMaynardLemma295CutoffAnalytic

/-!
# Holomorphy of the Lemma-29.5 theta multiplier left of one

The second rectangle in the proof of Lemma 29.5 moves the finite reflected
Dirichlet polynomial from a deep-left line to `Re s = 1/2`.  The only
archimedean factor is `Theta(s-ig)`.  Its numerator Gamma argument has
positive real part throughout `Re(s-ig) < 1`, while reciprocal Gamma is
entire.  This file records the exact local differentiability statement needed
for that pole-free rectangle.
-/

namespace GuthMaynardLemma295ThetaAnalytic

open Complex
open GuthMaynardLemma295CutoffAnalytic

noncomputable section

/-- The printed theta multiplier is holomorphic at every point strictly left
of `Re z = 1`. -/
theorem differentiableAt_sourceZetaTheta_of_re_lt_one
    {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ sourceZetaTheta z := by
  have hnumArg : ∀ m : ℕ, (1 - z) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [div_re, sub_re, one_re, Nat.cast_ofNat, ofReal_re,
      ofReal_im, mul_re, mul_im, neg_re, natCast_re] at hre
    norm_num at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hnumInner : DifferentiableAt ℂ (fun w : ℂ => (1 - w) / 2) z := by
    fun_prop
  have hnum : DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gamma ((1 - w) / 2)) z :=
    (Complex.differentiableAt_Gamma ((1 - z) / 2) hnumArg).comp z hnumInner
  have hdenInv : DifferentiableAt ℂ
      (fun w : ℂ => (Complex.Gamma (w / 2))⁻¹) z :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp z (by fun_prop)
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ (w - 1 / 2)) z :=
    (differentiableAt_id.sub_const _).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [show sourceZetaTheta = fun w : ℂ =>
      Complex.Gamma ((1 - w) / 2) / Complex.Gamma (w / 2) *
        (Real.pi : ℂ) ^ (w - 1 / 2) by
    funext w
    exact sourceZetaTheta_eq_printed w]
  simpa only [div_eq_mul_inv] using (hnum.mul hdenInv).mul hpow

end

end GuthMaynardLemma295ThetaAnalytic

#print axioms GuthMaynardLemma295ThetaAnalytic.differentiableAt_sourceZetaTheta_of_re_lt_one
