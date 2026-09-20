import GuthMaynardJutilaReflection2941

/-!
# The finite pair majorant inside Jutila Lemma 29.5

After the approximate functional equation, the reflected polynomial is
shifted by the common Mellin variable `t`.  Its coefficient has modulus one.
This file certifies the exact sign convention and shows that summing its
square over all ordinate differences is bounded by the unshifted
coefficient-one reflected prefix moment.  This is the finite Lemma-29.6 step;
no contour shift or integral estimate occurs here.
-/

namespace GuthMaynardLemma295PairMajorant

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardJutilaReflection2941

noncomputable section

/-- Exact sign normalization: `g₁-g₂+t` is represented by the swapped
negative-phase Gram pair `(g₂,g₁)` and the common unit coefficient
`n^(it)`. -/
theorem lemma295ReflectedPolynomial_eq_shiftedGram
    (M g₁ g₂ t : ℝ) :
    lemma295ReflectedPolynomial M ((g₁ - g₂) + t) =
      gramPolynomial (natRealIoc 0 M)
        (sigmaCoefficient (fun n => dirichletPhase n t) (1 / 2))
        negativeDirichletPhase g₂ g₁ := by
  unfold lemma295ReflectedPolynomial gramPolynomial sigmaCoefficient
    negativeDirichletPhase
  apply Finset.sum_congr rfl
  intro n hn
  unfold dirichletPhase
  rw [show star
      (Complex.exp (((((-g₁ * Real.log n) : ℝ) : ℂ) * Complex.I))) =
        Complex.exp
          (star (((((-g₁ * Real.log n) : ℝ) : ℂ) * Complex.I))) by
    exact (Complex.exp_conj _).symm]
  have hstar :
      star (((((-g₁ * Real.log n) : ℝ) : ℂ) * Complex.I)) =
        (((g₁ * Real.log n : ℝ) : ℂ) * Complex.I) := by
    change (starRingEnd ℂ)
      (((((-g₁ * Real.log n) : ℝ) : ℂ) * Complex.I)) = _
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hstar]
  calc
    (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
        Complex.exp
          ((((g₁ - g₂ + t) * Real.log n : ℝ) : ℂ) * Complex.I) =
      (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
        (Complex.exp ((((t * Real.log n : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((-g₂ * Real.log n : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((g₁ * Real.log n : ℝ) : ℂ) * Complex.I))) := by
            congr 1
            rw [← Complex.exp_add, ← Complex.exp_add]
            congr 1
            push_cast
            ring
    _ = _ := by ring

/-- The shifted coefficient has exactly the unshifted inverse-square-root
modulus. -/
theorem norm_shiftedSigmaCoefficient_eq
    (n : ℕ) (t : ℝ) :
    ‖sigmaCoefficient (fun n => dirichletPhase n t) (1 / 2) n‖ =
      Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := by
  unfold sigmaCoefficient dirichletPhase
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Real.exp_zero, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Pointwise in the Mellin variable, the full shifted pair moment is bounded
by the exact coefficient-one prefix moment. -/
theorem shifted_reflected_pairMoment_le_prefix
    (M t : ℝ) (G : Finset ℝ) :
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
      ‖lemma295ReflectedPolynomial M ((g₁ - g₂) + t)‖ ^ 2) ≤
      jutilaReflectedPrefixMoment M G := by
  let a : ℕ → ℂ :=
    sigmaCoefficient (fun n => dirichletPhase n t) (1 / 2)
  let b : ℕ → ℝ := fun n => Real.rpow (n : ℝ) (-(1 / 2 : ℝ))
  have hmajor := gram_majorant_principle
    (natRealIoc 0 M) G a b negativeDirichletPhase
    (fun n hn => by
      dsimp only [a, b]
      exact (norm_shiftedSigmaCoefficient_eq n t).le)
  have hleft :
      (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        ‖lemma295ReflectedPolynomial M ((g₁ - g₂) + t)‖ ^ 2) =
      realGramQuadratic (natRealIoc 0 M) G a negativeDirichletPhase := by
    unfold realGramQuadratic
    calc
      (∑ g₁ ∈ G, ∑ g₂ ∈ G,
          ‖lemma295ReflectedPolynomial M ((g₁ - g₂) + t)‖ ^ 2) =
        ∑ g₁ ∈ G, ∑ g₂ ∈ G,
          ‖gramPolynomial (natRealIoc 0 M) a
              negativeDirichletPhase g₂ g₁‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro g₁ hg₁
            apply Finset.sum_congr rfl
            intro g₂ hg₂
            rw [lemma295ReflectedPolynomial_eq_shiftedGram]
      _ = ∑ g₂ ∈ G, ∑ g₁ ∈ G,
          ‖gramPolynomial (natRealIoc 0 M) a
              negativeDirichletPhase g₂ g₁‖ ^ 2 := by
            rw [Finset.sum_comm]
      _ = _ := rfl
  have hright :
      realGramQuadratic (natRealIoc 0 M) G
          (fun n => (b n : ℂ)) negativeDirichletPhase =
        jutilaReflectedPrefixMoment M G := by
    unfold jutilaReflectedPrefixMoment sourceQuadratic sigmaCoefficient
    congr 2
    funext n
    dsimp [b]
    simp
  rw [hleft]
  exact hmajor.trans_eq hright

end

end GuthMaynardLemma295PairMajorant

#print axioms GuthMaynardLemma295PairMajorant.lemma295ReflectedPolynomial_eq_shiftedGram
#print axioms GuthMaynardLemma295PairMajorant.shifted_reflected_pairMoment_le_prefix
