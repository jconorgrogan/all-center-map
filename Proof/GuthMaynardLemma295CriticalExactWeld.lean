import GuthMaynardLemma295ReflectedFiniteContour
import GuthMaynardLemma295CriticalMajorant

/-!
# Exact critical-line weld for Lemma 29.5

The finite reflected contour produces the phase `-(g+t)`, while the printed
majorant is written with `g+t` after reversing the integration variable.
These polynomials are complex conjugates, so their norms agree.  This file
certifies that sign/orientation step and connects the exact finite reflected
integrand to the already-proved critical-line majorant.
-/

namespace GuthMaynardLemma295CriticalExactWeld

open Complex
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295ReflectedFiniteContour
open GuthMaynardLemma295CriticalMajorant

noncomputable section

theorem star_dirichletPhase (m : ℕ) (tau : ℝ) :
    star (dirichletPhase m tau) = dirichletPhase m (-tau) := by
  unfold dirichletPhase
  rw [show star (Complex.exp ((((tau * Real.log m : ℝ) : ℂ) * I))) =
      Complex.exp (star ((((tau * Real.log m : ℝ) : ℂ) * I))) by
    exact (Complex.exp_conj _).symm]
  congr 1
  change (starRingEnd ℂ) ((((tau * Real.log m : ℝ) : ℂ) * I)) = _
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem star_lemma295ReflectedPolynomial (M tau : ℝ) :
    star (lemma295ReflectedPolynomial M tau) =
      lemma295ReflectedPolynomial M (-tau) := by
  unfold lemma295ReflectedPolynomial
  change (starRingEnd ℂ)
      (∑ m ∈ GuthMaynardJutilaTransference.natRealIoc 0 M,
        (Real.rpow (m : ℝ) (-(1 / 2 : ℝ)) : ℂ) * dirichletPhase m tau) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul, show (starRingEnd ℂ) (dirichletPhase m tau) =
      dirichletPhase m (-tau) from star_dirichletPhase m tau]
  simp only [Complex.conj_ofReal]

theorem norm_lemma295ReflectedPolynomial_neg (M tau : ℝ) :
    ‖lemma295ReflectedPolynomial M (-tau)‖ =
      ‖lemma295ReflectedPolynomial M tau‖ := by
  rw [← star_lemma295ReflectedPolynomial M tau, norm_star]

/-- At the exact critical point delivered by the second contour, the norm is
the norm of the source-facing critical integrand. -/
theorem norm_reflectedFinite_critical_eq
    (N g : ℝ) (K : ℕ) (t : ℝ) :
    ‖lemma295ReflectedFiniteIntegrand N g K
        (((1 / 2 : ℝ) : ℂ) - t * I)‖ =
      ‖lemma295CriticalIntegrand N K g t‖ := by
  have hz :
      (((1 / 2 : ℝ) : ℂ) - t * I) - g * I =
        ((1 / 2 : ℝ) : ℂ) - (g + t) * I := by
    push_cast
    ring
  unfold lemma295ReflectedFiniteIntegrand lemma295CriticalIntegrand
  dsimp only
  rw [hz]
  have hgt : ((g : ℂ) + (t : ℂ)) = ((g + t : ℝ) : ℂ) := by push_cast; ring
  rw [hgt, sourceDualPartialNat_critical_eq_reflectedPolynomial_neg]
  repeat' rw [norm_mul]
  rw [norm_lemma295ReflectedPolynomial_neg]
  ring

/-- Consequently the exact finite reflected integrand obeys the literal
critical majorant already used in the statement of Lemma 29.5. -/
theorem norm_reflectedFinite_critical_le
    {N : ℝ} (hN : 0 < N) (K : ℕ) (g t : ℝ) :
    ‖lemma295ReflectedFiniteIntegrand N g K
        (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
      GuthMaynardLemma295MellinAllLines.sourceMellinDecayConstant (1 / 2) *
        (Real.sqrt N *
          (‖lemma295ReflectedPolynomial K (g + t)‖ / (1 + t ^ 2))) := by
  rw [norm_reflectedFinite_critical_eq]
  exact norm_lemma295CriticalIntegrand_le hN K g t

end

end GuthMaynardLemma295CriticalExactWeld

#print axioms GuthMaynardLemma295CriticalExactWeld.star_lemma295ReflectedPolynomial
#print axioms GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_eq
#print axioms GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_le
