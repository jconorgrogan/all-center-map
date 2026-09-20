import GuthMaynardLemma295CriticalExactWeld
import GuthMaynardLemma295HorizontalPointwise
import GuthMaynardLemma295MellinPolynomialDecay

/-!
# Arbitrary-order pointwise decay on the reflected critical line
-/

namespace GuthMaynardLemma295CriticalTailPointwise

open Complex
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295ThetaBounds
open GuthMaynardLemma295ReflectedFiniteContour
open GuthMaynardLemma295CriticalMajorant
open GuthMaynardLemma295HorizontalPointwise
open GuthMaynardLemma295MellinPolynomialDecay

noncomputable section

 theorem norm_lemma295ReflectedPolynomial_nat_le
    (K : ℕ) (tau : ℝ) :
    ‖lemma295ReflectedPolynomial K tau‖ ≤ K := by
  have heq := sourceDualPartialNat_critical_eq_reflectedPolynomial_neg K (-tau)
  have hbound := norm_sourceDualPartialNat_le_card K
    (z := ((1 / 2 : ℝ) : ℂ) - ((-tau : ℝ) : ℂ) * I) (by norm_num)
  rw [heq] at hbound
  simpa using hbound

 theorem norm_lemma295CriticalIntegrand_le_arbitraryOrder
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g t : ℝ) :
    ‖lemma295CriticalIntegrand N K g t‖ ≤
      Real.sqrt N * K *
        (sourceMellinDecayConstantAt (1 / 2) k /
          (1 + |t| ^ k)) := by
  have htheta := norm_sourceZetaTheta_criticalLine_eq_one (-(g + t))
  have htheta' :
      ‖sourceZetaTheta (((1 / 2 : ℝ) : ℂ) - (g + t) * I)‖ = 1 := by
    have harg :
        (((1 / 2 : ℝ) : ℂ) - (g + t) * I) =
          ((1 / 2 : ℝ) : ℂ) + ((-(g + t) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg]
    exact htheta
  have hscale := norm_cpow_criticalScale_eq_sqrt hN g t
  have hpoly := norm_lemma295ReflectedPolynomial_nat_le K (g + t)
  have hmellin :=
    norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
      (1 / 2) k (-t)
  have hmellin' :
      ‖mellin sourceHZero (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k) := by
    simpa [sub_eq_add_neg] using hmellin
  unfold lemma295CriticalIntegrand
  repeat' rw [norm_mul]
  rw [htheta', one_mul, hscale]
  have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
  have hsqrt0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hpoly hsqrt0) hmellin'
    (norm_nonneg _) (mul_nonneg hsqrt0 hK0)

end
end GuthMaynardLemma295CriticalTailPointwise

#print axioms GuthMaynardLemma295CriticalTailPointwise.norm_lemma295ReflectedPolynomial_nat_le
#print axioms GuthMaynardLemma295CriticalTailPointwise.norm_lemma295CriticalIntegrand_le_arbitraryOrder
