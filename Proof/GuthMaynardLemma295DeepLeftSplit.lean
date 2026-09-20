import GuthMaynardLemma295ReflectedFiniteContour

/-!
# Exact functional-equation split on the deep-left line

This identifies the raw zeta integrand with the retained finite reflected
integrand plus the literal dual tail.  The exceptional ordinate `t=g` is
kept explicit; it is a null singleton in the subsequent vertical integral.
-/

namespace GuthMaynardLemma295DeepLeftSplit

open Complex
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295FiniteContour
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295ReflectedFiniteContour

noncomputable section

theorem lemma295RawIntegrand_deepLeft_eq_finite_add_tail
    (N g : ℝ) (K n : ℕ) {t : ℝ}
    (htg : t ≠ g) :
    lemma295RawIntegrand N g
        ((deepLeftSigma n : ℂ) + t * I) =
      lemma295ReflectedFiniteIntegrand N g K
          ((deepLeftSigma n : ℂ) + t * I) +
        lemma295DeepLeftTailIntegrand N g K n t := by
  let s : ℂ := (deepLeftSigma n : ℂ) + t * I
  let z : ℂ := s - g * I
  have hzre : z.re = deepLeftSigma n := by simp [z, s]
  have hzim : z.im = t - g := by simp [z, s]
  have hzneg : z.re < 0 := by
    rw [hzre]
    unfold deepLeftSigma
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hz0 : z ≠ 0 := ne_zero_of_re_ne_zero (ne_of_lt hzneg)
  have hdual0 : 1 - z ≠ 0 := by
    apply ne_zero_of_re_ne_zero
    simp only [sub_re, one_re]
    linarith
  have hgamma : Complex.Gammaℝ z ≠ 0 := by
    intro hzero
    rw [Complex.Gammaℝ_eq_zero_iff] at hzero
    obtain ⟨m, hm⟩ := hzero
    have : z.im = 0 := by rw [hm]; simp
    rw [hzim] at this
    exact htg (sub_eq_zero.mp this)
  have hgammaDual : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [sub_re, one_re]
    linarith
  have hFE := riemannZeta_eq_sourceZetaTheta_mul
    hz0 hdual0 hgamma hgammaDual
  have hsplit : riemannZeta (1 - z) =
      sourceDualPartialNat K z + sourceDualTailNat K z := by
    unfold sourceDualTailNat
    ring
  unfold lemma295RawIntegrand lemma295ReflectedFiniteIntegrand
    lemma295DeepLeftTailIntegrand
  dsimp only
  change (N : ℂ) ^ z * riemannZeta z * mellin sourceHZero s = _
  rw [hFE, hsplit]
  ring

end
end GuthMaynardLemma295DeepLeftSplit

#print axioms GuthMaynardLemma295DeepLeftSplit.lemma295RawIntegrand_deepLeft_eq_finite_add_tail
